# NativeGroundSeparation

## Abstract

NativeGroundSeparation

**Definition 1.1 (Finite Boolean free terms).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.Term`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.Term` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constants and variables have different sum constructors. Terms are finite free ordered full trees, with repeated variable names preserving one shared value.

**Definition 1.2 (Native ground evaluation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.evaluate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FreeMagma.lift simultaneously replaces variables by actual Boolean trees and preserves constants and ordered pairs.

**Definition 1.3 (Occurrence masses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.counts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.counts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Variable and constant occurrences are counted separately, including repetitions. Under a common variable leaf mass M, evaluation has exactly M times the variable count plus the constant count leaves.

**Definition 1.4 (Equal-mass separating assignments).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.code`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing comb constructor encodes a finite index by one marked leaf in a common finite shape. Its existing length and equality theorem is reused directly.

**Theorem 1.5 (All finite disequalities simultaneously).**

$$\forall X: Type, (\forall I: \operatorname{Fintype}\left(X\right), (\forall D: \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{Term}\left(X\right), \operatorname{Term}\left(X\right)\right)\right), ((\forall p: \operatorname{Prod}\left(\operatorname{Term}\left(X\right), \operatorname{Term}\left(X\right)\right), ((p \in D) \implies (\operatorname{fst}\left(p\right) \neq \operatorname{snd}\left(p\right)))) \iff (\exists v: X \to Source, (\forall p: \operatorname{Prod}\left(\operatorname{Term}\left(X\right), \operatorname{Term}\left(X\right)\right), ((p \in D) \implies (\operatorname{evaluate}\left(v, \operatorname{fst}\left(p\right)\right) \neq \operatorname{evaluate}\left(v, \operatorname{snd}\left(p\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.simultaneous_ground_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite list of syntactically unequal term pairs admits one simultaneous ground assignment separating every pair. Large common variable masses prevent a variable from colliding with either a ground subterm or a genuine compound containing a variable. The empty variable type is included. This is an existence and feasibility result, not an acquisition of source values.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.Term`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.code`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.counts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.evaluate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.simultaneous_ground_separation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](../FourExitRawEndpointSpectrum.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
