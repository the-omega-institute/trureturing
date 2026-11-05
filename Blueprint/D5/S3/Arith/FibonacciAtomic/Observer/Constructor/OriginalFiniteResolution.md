# Finite symbolic resolution of functional expressions

## Abstract

OriginalFiniteResolution

**Theorem 1.1 (Syntactic finite derivations and values forced in every solution).**

$$\forall k: Nat, (\forall m: Nat, (\forall E: \operatorname{Definitions}\left(k, m\right), (\forall mode: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), ((\forall e: \operatorname{Expr}\left(k, m\right), ((\operatorname{isSome}\left(\operatorname{compile}\left(E, mode, e\right)\right) = true) \iff (\operatorname{FiniteDerivation}\left(E, mode, e\right)))) \land (\forall e: \operatorname{Expr}\left(k, m\right), (\forall f: \operatorname{FiniteExpr}\left(k\right), ((\operatorname{compile}\left(E, mode, e\right) = \operatorname{some}\left(f\right)) \implies (\forall p: \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Nat\right), (\forall v: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), CompletionTree\right), ((\operatorname{Solution}\left(E, mode, p, v\right)) \implies (\operatorname{value}\left(mode, p, v, e\right) = \operatorname{embed}\left(\operatorname{finiteValue}\left(p, f\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution.original_finite_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, Function(A,B) denotes functions from A to B, and isSome is the Boolean test for a defined optional result. This expression language has finite grounds, named finite or divergent parameter atoms, decorated state variables and ordered pairs. It has no independent literal Omega constructor. Undefined states may have arbitrary completed values. The compiler uses exactly as many rounds as there are original states; parameter atoms remain symbolic and are never expanded to a bounded family of values.

Successful compilation is equivalent to a finite syntactic derivation from the defining expressions. A compiled finite expression evaluates to the same finite native tree in every solution at every parameter assignment. Repeated names, atomic coincidences, arbitrary powers and zero state or parameter counts are allowed. The stabilization bound directly applies pinned Mathlib Nat.stabilises_of_monotone to the monotone support cardinality, bounded by the original state count. Equal adjacent cardinalities give equal supports and hence equal environments; environment stability propagates to the next round. This consumed application supplies no new mathematical-content credit.

For the four-state edgeSystem in OriginalCanonicalClassification, encodeDefinitions shifts the two finite parameter names and reserves a fixed divergent slot for literal Omega. Resolving the pair of original states 0 and 1 succeeds after the four state rounds, with no bound on either natural parameter. The original_finite_resolution soundness clause is applied inside OriginalNativeConstruction.finite_compile_sound to the same encoded input and decoded successful expression. Its conclusion fixes that finite ordered pair in every original solution even though the same system also has a recurrent coordinate and an undefined coordinate.

The conclusion does not construct a solution or identify semantic finiteness of a canonical solution. Literal Omega in the larger native source language is handled by a separate exact encoding with a fixed divergent internal slot, followed by decoding to the original finite parameter names. No external literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/OriginalFiniteResolution.original_finite_resolution`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionPositiveDriftRegion](../CompletionPositiveDriftRegion.md)
