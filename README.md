# Type Inference and Unification

This is a Haskell implementation ported from the Cornell CS3110 [lecture notes](https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm).

```
$ cabal run
? x
a
? \x -> x
a -> a
? \x -> \y -> \z -> x z (y z)
(c -> e -> f) -> (c -> e) -> c -> f
? \x -> \y -> x
a -> b -> a
? \f -> \g -> \x -> f (g x)
(d -> e) -> (c -> d) -> c -> e
? \f -> (\x -> f x x) (\y -> f y y)
ERROR: not unifiable due to circularity
```
