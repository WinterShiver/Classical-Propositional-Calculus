# Classical-Propositional-Calculus
A series of Haskell implementations of logic systems. This one is for the most simple propositional calculus. 

P.hs

* The expression of propostions and proofs correspond to data definition of `Prop` and `Proof`. The correctness of proof is guaranteed with type signature. Type error would be detected in compile if the proof is wrong. 

TODO

1. Implementation based on Discrete Mathematics Using a Computer, Chapter 6. Reference code: [[code]](http://www.dcs.gla.ac.uk/~jtod/discrete-mathematics/Stdm.lhs)
2. Is it possible to build automatic proof? (Probably not) Is it possible to estimate the proof complexity so that we can search a proof for a given proposition?
