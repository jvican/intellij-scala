package org.jetbrains.plugins.scala
package lang
package psi
package types

import java.util.Objects

import com.intellij.psi.PsiElement
import org.jetbrains.plugins.scala.lang.psi.api.statements.params.{ScTypeParam, TypeParamId}
import org.jetbrains.plugins.scala.lang.psi.types.api._
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue._
import org.jetbrains.plugins.scala.lang.psi.types.recursiveUpdate.{ScSubstitutor, Update}
import org.jetbrains.plugins.scala.lang.refactoring.util.ScTypeUtil.AliasType
import org.jetbrains.plugins.scala.project.ProjectContext

import scala.annotation.tailrec
import scala.collection.mutable

/**
  * @author ilyas
  */
class ScExistentialType private (val quantified: ScType,
                                 val wildcards: List[ScExistentialArgument],
                                 private val simplifiedQ: ScType) extends ScalaType with ValueType {

  override implicit def projectContext: ProjectContext = quantified.projectContext

  override protected def isAliasTypeInner: Option[AliasType] = {
    quantified.isAliasType.map(a => a.copy(lower = a.lower.map(_.unpackedType), upper = a.upper.map(_.unpackedType)))
  }

  val boundNames: Set[String] = wildcards.map(_.name).toSet

  override def equals(other: Any): Boolean = other match {
    case that: ScExistentialType => quantified == that.quantified
    case _ => false
  }

  //make it different from quantified.hashCode
  override def hashCode(): Int = ScExistentialType.hashCode() + quantified.hashCode()

  override def removeAbstracts = ScExistentialType(quantified.removeAbstracts)

  override def updateSubtypes(updates: Seq[Update], visited: Set[ScType]): ScType =
    ScExistentialType(quantified.recursiveUpdateImpl(updates, visited))

  override def recursiveVarianceUpdateModifiable[T](data: T, update: (ScType, Variance, T) => (Boolean, ScType, T),
                                                    variance: Variance = Covariant, revertVariances: Boolean = false): ScType = {
    update(this, variance, data) match {
      case (true, res, _) => res
      case (_, _, newData) =>
        ScExistentialType(quantified.recursiveVarianceUpdateModifiable(newData, update, variance))
    }
  }

  override def equivInner(r: ScType, uSubst: ScUndefinedSubstitutor, falseUndef: Boolean): (Boolean, ScUndefinedSubstitutor) = {
    if (r.equiv(Nothing)) return quantified.equiv(Nothing, uSubst)
    var undefinedSubst = uSubst
    val simplified = unpackedType match {
      case ex: ScExistentialType => ex.simplify()
      case u => u
    }
    val conformance: ScalaConformance = typeSystem
    if (this != simplified) return simplified.equiv(r, undefinedSubst, falseUndef)
    (quantified, r) match {
      case (ParameterizedType(ScAbstractType(typeParameter, lowerBound, upperBound), args), _) if !falseUndef =>
        val subst = ScSubstitutor.bind(typeParameter.typeParameters, args)
        val upper: ScType =
          subst.subst(upperBound) match {
            case ParameterizedType(u, _) => ScExistentialType(ScParameterizedType(u, args))
            case u => ScExistentialType(ScParameterizedType(u, args))
          }
        val conformance = r.conforms(upper, undefinedSubst)
        if (!conformance._1) return conformance

        val lower: ScType =
          subst.subst(lowerBound) match {
            case ParameterizedType(l, _) => ScExistentialType(ScParameterizedType(l, args))
            case l => ScExistentialType(ScParameterizedType(l, args))
          }
        return lower.conforms(r, conformance._2)
      case (ParameterizedType(UndefinedType(typeParameter, _), args), _) if !falseUndef =>
        r match {
          case ParameterizedType(des, _) =>
            val y = conformance.addParam(typeParameter, des, undefinedSubst)
            if (!y._1) return (false, undefinedSubst)
            undefinedSubst = y._2
            return ScExistentialType(ScParameterizedType(des, args)).equiv(r, undefinedSubst, falseUndef)
          case ScExistentialType(ParameterizedType(des, _), _) =>
            val y = conformance.addParam(typeParameter, des, undefinedSubst)
            if (!y._1) return (false, undefinedSubst)
            undefinedSubst = y._2
            return ScExistentialType(ScParameterizedType(des, args)).equiv(r, undefinedSubst, falseUndef)
          case _ => return (false, undefinedSubst) //looks like something is wrong
        }
      case (ParameterizedType(pType, args), ParameterizedType(rType, _)) =>
        val res = pType.equivInner(rType, undefinedSubst, falseUndef)
        if (!res._1) return res
        conformance.extractParams(rType) match {
          case Some(iter) =>
            val (names, existArgsBounds) =
              args.zip(iter.toList).collect {
                case (arg: ScExistentialArgument, rParam: ScTypeParam)
                  if rParam.isCovariant && wildcards.contains(arg) => (arg.name, arg.upper)
                case (arg: ScExistentialArgument, rParam: ScTypeParam)
                  if rParam.isContravariant && wildcards.contains(arg) => (arg.name, arg.lower)
              }.unzip
            val subst = ScSubstitutor.bind(names, existArgsBounds)(TypeParamId.nameBased)
            return subst.subst(quantified).equiv(r, undefinedSubst, falseUndef)
          case _ =>
        }
      case _ =>
    }
    r.unpackedType match {
      case ex: ScExistentialType =>
        val simplified = ex.simplify()
        if (ex != simplified) return this.equiv(simplified, undefinedSubst, falseUndef)
        val list = wildcards.zip(ex.wildcards)
        val iterator = list.iterator
        while (iterator.hasNext) {
          val (w1, w2) = iterator.next()
          val t = w2.equivInner(w1, undefinedSubst, falseUndef)
          if (!t._1) return (false, undefinedSubst)
          undefinedSubst = t._2
        }
        quantified.equiv(ex.quantified, undefinedSubst, falseUndef) //todo: probable problems with different positions of skolemized types.
      case poly: ScTypePolymorphicType if poly.typeParameters.length == wildcards.length =>
        val list = wildcards.zip(poly.typeParameters)
        val iterator = list.iterator
        var t = (true, undefinedSubst)
        while (iterator.hasNext) {
          val (w, tp) = iterator.next()
          t = w.lower.equivInner(tp.lowerType, t._2, falseUndef)
          if (!t._1) return (false, undefinedSubst)
          t = w.upper.equivInner(tp.upperType, t._2, falseUndef)
          if (!t._1) return (false, undefinedSubst)
        }
        val polySubst = ScSubstitutor.bind(poly.typeParameters, wildcards)
        quantified.equiv(polySubst.subst(poly.internalType), t._2, falseUndef)
      case _ => (false, undefinedSubst)
    }
  }

  /** Specification 3.2.10:
    * 1. Multiple for-clauses in an existential type can be merged. E.g.,
    * T forSome {Q} forSome {H} is equivalent to T forSome {Q;H}.
    * 2. Unused quantifications can be dropped. E.g., T forSome {Q;H} where
    * none of the types defined in H are referred to by T or Q, is equivalent to
    * T forSome {Q}.
    * 3. An empty quantification can be dropped. E.g., T forSome { } is equivalent
    * to T.
    * 4. An existential type T forSome {Q} where Q contains a clause
    * type t[tps] >: L <: U is equivalent to the type T' forSome {Q} where
    * T' results from T by replacing every covariant occurrence (4.5) of t in T by
    * U and by replacing every contravariant occurrence of t in T by L.
    *
    * 1., 2. and 3. are guaranteed by construction (see ScExistentialType.apply)
    * T' from 4. is also built in the factory method.
    */
  def simplify(): ScType = ScExistentialType(simplifiedQ)

  override def visitType(visitor: TypeVisitor): Unit = visitor match {
    case scalaVisitor: ScalaTypeVisitor => scalaVisitor.visitExistentialType(this)
    case _ =>
  }

  override def typeDepth: Int = {
    def typeParamsDepth(typeParams: Seq[TypeParameterType]): Int = {
      typeParams.map {
        case typeParam =>
          val boundsDepth = typeParam.lowerType.typeDepth.max(typeParam.upperType.typeDepth)
          if (typeParam.arguments.nonEmpty) {
            (typeParamsDepth(typeParam.arguments) + 1).max(boundsDepth)
          } else boundsDepth
      }.max
    }

    val quantDepth = quantified.typeDepth
    if (wildcards.nonEmpty) {
      (wildcards.map {
        wildcard =>
          val boundsDepth = wildcard.lower.typeDepth.max(wildcard.upper.typeDepth)
          if (wildcard.args.nonEmpty) {
            (typeParamsDepth(wildcard.args) + 1).max(boundsDepth)
          } else boundsDepth
      }.max + 1).max(quantDepth)
    } else quantDepth
  }
}

object ScExistentialType {

  /** Specification 3.2.10:
    * 1. Multiple for-clauses in an existential type can be merged. E.g.,
    * T forSome {Q} forSome {H} is equivalent to T forSome {Q;H}.
    * 2. Unused quantifications can be dropped. E.g., T forSome {Q;H} where
    * none of the types defined in H are referred to by T or Q, is equivalent to
    * T forSome {Q}.
    * 3. An empty quantification can be dropped. E.g., T forSome { } is equivalent
    * to T.
    */
  final def apply(quantified: ScType): ScType = {
    quantified match {
      case e: ScExistentialType =>
        //first rule
        ScExistentialType(e.quantified)
      case _ =>
        val (simplified, wildcards) = simplifiedAndUsedWildcards(quantified)
        if (wildcards.nonEmpty) {
          //second rule
          new ScExistentialType(quantified, wildcards.toList, simplified)
        }
        else simplified //third rule
    }
  }

  def apply(quantified: ScType, wildcards: List[ScExistentialArgument]): ScType =
    ScExistentialType(quantified)

  def unapply(existential: ScExistentialType): Option[(ScType, List[ScExistentialArgument])] =
    Some((existential.quantified, existential.wildcards))

  /** Specification 3.2.10:
    * 4. An existential type T forSome {Q} where Q contains a clause
    *    type t[tps] >: L <: U is equivalent to the type T' forSome {Q} where
    *    T' results from T by replacing every covariant occurrence (4.5) of t in T by
    *    U and by replacing every contravariant occurrence of t in T by L.
    */
  private def simplifiedAndUsedWildcards(quantified: ScType): (ScType, Set[ScExistentialArgument]) = {
    quantified match {
      case arg: ScExistentialArgument => (arg.upper, Set(arg)) //treat top level as Covariant
      case _ =>
        var wildcards = Set.empty[ScExistentialArgument]

        val simplification: (ScType, Variance) => (Boolean, ScType) = {
          case (ex: ScExistentialType, _) =>
            (true, ex.simplifiedQ)
          case (arg: ScExistentialArgument, variance) =>
            wildcards += arg

            val argOrBound = variance match {
              case Covariant => arg.upper
              case Contravariant => arg.lower
              case _ => arg
            }
            (true, argOrBound)
          case (tp, _) => (false, tp)
        }
        (quantified.recursiveVarianceUpdate(simplification, Invariant), wildcards)
    }
  }

  def existingWildcards(tp: ScType): Set[String] = {
    val existingWildcards = new mutable.HashSet[String]
    tp.visitRecursively {
      case ex: ScExistentialType => existingWildcards ++= ex.boundNames
      case _ =>
    }
    existingWildcards.toSet
  }

  @tailrec
  def fixExistentialArgumentName(name: String, existingWildcards: Set[String]): String = {
    if (existingWildcards.contains(name)) {
      fixExistentialArgumentName(name + "$u", existingWildcards) //todo: fix it for name == "++"
    } else name
  }

  def fixExistentialArgumentNames(tp: ScType, existingWildcards: Set[String]): ScType = {
    if (existingWildcards.isEmpty) tp
    else {
      tp.recursiveVarianceUpdateModifiable[Set[String]](Set.empty, {
        case (s: ScExistentialArgument, _, data) if !data.contains(s.name) =>
          val name = fixExistentialArgumentName(s.name, existingWildcards)
          (true, ScExistentialArgument(name, s.args, s.lower, s.upper), data)
        case (ex: ScExistentialType, _, data) =>
          (false, ex, data ++ ex.boundNames)
        case (t, _, data) => (false, t, data)
      })
    }
  }
}

class ScExistentialArgument private (val name: String,
                                     val args: List[TypeParameterType],
                                     val lower: ScType,
                                     val upper: ScType,
                                     private val id: Int)

  extends NamedType with ValueType {

  override implicit def projectContext: ProjectContext = lower.projectContext

  override def hashCode(): Int =
    Objects.hash(name, args, lower, upper, id: Integer)

  override def equals(other: Any): Boolean = other match {
    case ex: ScExistentialArgument =>
      id == ex.id &&
      name == ex.name &&
      args == ex.args &&
      lower == ex.lower &&
      upper == ex.upper
    case _ => false
  }

  def withBounds(newLower: ScType, newUpper: ScType): ScExistentialArgument =
    new ScExistentialArgument(name, args, newLower, newUpper, id)

  def withoutAbstracts: ScExistentialArgument = ScExistentialArgument(name, args, lower.removeAbstracts, upper.removeAbstracts)

  override def updateSubtypes(updates: Seq[Update], visited: Set[ScType]): ScExistentialArgument = {
    ScExistentialArgument(name, args,
      lower.recursiveUpdateImpl(updates, visited),
      upper.recursiveUpdateImpl(updates, visited))
  }

  def recursiveVarianceUpdateModifiableNoUpdate[T](data: T, update: (ScType, Variance, T) => (Boolean, ScType, T),
                                                            variance: Variance = Covariant): ScExistentialArgument = {
    ScExistentialArgument(name, args, lower.recursiveVarianceUpdateModifiable(data, update, Contravariant),
      upper.recursiveVarianceUpdateModifiable(data, update, Covariant))
  }

  override def recursiveVarianceUpdateModifiable[T](data: T, update: (ScType, Variance, T) => (Boolean, ScType, T),
                                                    v: Variance = Covariant, revertVariances: Boolean = false): ScType = {
    update(this, v, data) match {
      case (true, res, _) => res
      case (_, _, newData) =>
        recursiveVarianceUpdateModifiableNoUpdate(newData, update, v)
    }
  }

  override def equivInner(r: ScType, uSubst: ScUndefinedSubstitutor, falseUndef: Boolean): (Boolean, ScUndefinedSubstitutor) = {
    r match {
      case exist: ScExistentialArgument =>
        var undefinedSubst = uSubst
        val s = ScSubstitutor.bind(exist.args.map(_.name), args)(TypeParamId.nameBased)
        val t = lower.equiv(s.subst(exist.lower), undefinedSubst, falseUndef)
        if (!t._1) return (false, undefinedSubst)
        undefinedSubst = t._2
        upper.equiv(s.subst(exist.upper), undefinedSubst, falseUndef)
      case _ => (false, uSubst)
    }
  }

  override def visitType(visitor: TypeVisitor): Unit = visitor match {
    case scalaVisitor: ScalaTypeVisitor => scalaVisitor.visitExistentialArgument(this)
    case _ =>
  }
}

object ScExistentialArgument {
  def apply(name: String, args: List[TypeParameterType], lower: ScType, upper: ScType, id: Int = 0) =
    new ScExistentialArgument(name, args, lower, upper, id)

  def apply(name: String, args: List[TypeParameterType], lower: ScType, upper: ScType, psi: PsiElement) =
    new ScExistentialArgument(name, args, lower, upper, id = psi.hashCode())

  def unapply(arg: ScExistentialArgument): Option[(String, List[TypeParameterType], ScType, ScType)] =
    Some((arg.name, arg.args, arg.lower, arg.upper))
}
