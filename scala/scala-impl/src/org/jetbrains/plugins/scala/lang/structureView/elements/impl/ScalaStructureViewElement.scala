package org.jetbrains.plugins.scala.lang.structureView.elements.impl

import java.util.Objects

import com.intellij.ide.structureView.StructureViewTreeElement
import com.intellij.ide.util.treeView.smartTree.TreeElement
import com.intellij.navigation.ItemPresentation
import com.intellij.pom.Navigatable
import com.intellij.psi.PsiElement
import org.jetbrains.plugins.scala.extensions.ObjectExt
import org.jetbrains.plugins.scala.lang.psi.api.expr.ScBlockExpr
import org.jetbrains.plugins.scala.lang.psi.api.statements.params.ScClassParameter
import org.jetbrains.plugins.scala.lang.psi.api.statements.{ScFunction, ScTypeAlias, ScValue, ScVariable}
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.ScPackaging
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.typedef.ScTypeDefinition

import scala.collection.Seq

/**
* @author Alexander Podkhalyuzin
* Date: 04.05.2008
*/

abstract class ScalaStructureViewElement[T <: PsiElement](val element: T, val inherited: Boolean = false)
  extends StructureViewTreeElement with ScalaItemPresentation {

  override def getPresentation: ItemPresentation = this

  override def getValue: AnyRef = if (element.isValid) element else null

  override def navigate(b: Boolean): Unit = navigatable.foreach(_.navigate(b))

  override def canNavigate: Boolean = navigatable.exists(_.canNavigate)

  override def canNavigateToSource: Boolean = navigatable.exists(_.canNavigateToSource)

  private def navigatable = element.asOptionOf[Navigatable]

  override def getChildren: Array[TreeElement] = TreeElement.EMPTY_ARRAY

  // TODO
  override def equals(o: Any): Boolean = {
    val clazz = o match {
      case obj: Object => obj.getClass
      case _ => return false
    }
    if (o == null || getClass != clazz) return false
    val that = o.asInstanceOf[ScalaStructureViewElement[_]]
    if (inherited != that.inherited) return false

    val value = getValue
    if (value == null) that.getValue == null
    else value == that.getValue
  }

  override def hashCode(): Int = Objects.hash(getValue, Boolean.box(inherited))
}

object ScalaStructureViewElement {
  def apply(element: PsiElement, inherited: Boolean = false): Seq[ScalaStructureViewElement[_]] = element match {
    case packaging: ScPackaging => packaging.typeDefinitions.map(new ScalaTypeDefinitionStructureViewElement(_))
    // TODO Type definition can be inherited
    case definition: ScTypeDefinition => Seq(new ScalaTypeDefinitionStructureViewElement(definition))
    case parameter: ScClassParameter => Seq(new ScalaValOrVarParameterStructureViewElement(parameter, inherited))
    case function: ScFunction => ScalaFunctionStructureViewElement(function, inherited)
    case variable: ScVariable => variable.declaredElements.flatMap(ScalaVariableStructureViewElement(_, inherited))
    case value: ScValue => value.declaredElements.flatMap(ScalaValueStructureViewElement(_, inherited))
    case alias: ScTypeAlias => Seq(new ScalaTypeAliasStructureViewElement(alias, inherited))
    case block: ScBlockExpr => Seq(new ScalaBlockStructureViewElement(block))
    case _ => Seq.empty
  }
}