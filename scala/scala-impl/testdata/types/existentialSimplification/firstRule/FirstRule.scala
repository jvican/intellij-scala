class Z[T, Q]
val x: (Z[T, Q] forSome {type T}) forSome {type Q} = null
/*start*/x/*end*/
//(Z[T, Q]) forSome {type T; type Q}