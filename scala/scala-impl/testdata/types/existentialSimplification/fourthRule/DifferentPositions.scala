class A[X, +Y, -Z]
val x: A[X, X, X] forSome {type X} = null
/*start*/x/*end*/
//(A[X, Any, Nothing]) forSome {type X}