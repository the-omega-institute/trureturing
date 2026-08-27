# Dual Gram Visible Ranges

## Abstract

The two Gram operators of a finite protocol family expose its two visible ranges.

**Theorem 1.1 (The state and protocol visible ranges are adjoint duals).**

$$\begin{aligned}\forall K, V, iota: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(V)], [\operatorname{InnerProductSpace}(K, V)],\\{}[\operatorname{FiniteDimensional}(K, V)], [\operatorname{Fintype}(iota)],\\\forall ell: iota \to \operatorname{LinearMap}(K, V, K),\\{}let M: \operatorname{LinearMap}(K, V, \operatorname{PiLp}(2, iota \to K)) = \operatorname{comp}(\operatorname{toLinearMap}(\operatorname{symm}(\operatorname{withLpLinearEquiv}(2, K, iota \to K))), \operatorname{linearPi}(ell));\\\operatorname{range}(\operatorname{comp}(\operatorname{adjoint}(M), M)) = \operatorname{range}(\operatorname{adjoint}(M)) \land\\{}\operatorname{range}(\operatorname{comp}(M, \operatorname{adjoint}(M))) = \operatorname{range}(M).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/DualGramVisibleRanges.dual_gram_visible_ranges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let an indexed family assign a scalar linear readout to every protocol. The observation map is constructed coordinatewise by the canonical linear-map product constructor.

The state Gram operator is the adjoint followed by the observation map, while the protocol Gram operator uses the reverse composition. Their ranges are respectively the adjoint range and the realizable observation range.

The proof directly applies the pinned library's two exact finite-dimensional adjoint-composition range lemmas.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/DualGramVisibleRanges.dual_gram_visible_ranges`
