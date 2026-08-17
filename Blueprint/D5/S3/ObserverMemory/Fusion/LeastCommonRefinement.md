# Least Common Refinement

## Abstract

The quotient by the intersection relation is the least common refinement.

**Theorem 1.1 (The least common refinement has a unique surjective factor).**

$$\begin{gathered}\forall Y, W,\\R_{1}, R_{2}: \operatorname{Setoid}(Y),\\r: Y \to W, p_{1}: W \to \operatorname{Quotient}(R_{1}),\\p_{2}: W \to \operatorname{Quotient}(R_{2}),\\\operatorname{Surjective}\left(r\right) \Rightarrow \operatorname{Surjective}\left(p_{1}\right) \Rightarrow \operatorname{Surjective}\left(p_{2}\right) \Rightarrow\\(\forall y\in Y, p_{1}(r(y)) = [y]_{R_{1}}) \Rightarrow\\(\forall y\in Y, p_{2}(r(y)) = [y]_{R_{2}}) \Rightarrow\\\exists! h: W \to \operatorname{Quotient}(\operatorname{inf}\left(R_{1}, R_{2}\right)), \operatorname{Surjective}\left(h\right) \land\\\forall y\in Y, h(r(y)) = [y]_{\operatorname{inf}\left(R_{1}, R_{2}\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/LeastCommonRefinement.least_common_refinement_universal_property` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R1 and R2 be equivalence relations on Y. A surjective projection r from Y onto W is assumed to admit surjective maps from W to both component quotients. Each map must commute with r and the corresponding canonical quotient projection.

There is then a unique surjective map from W to the quotient of Y by the intersection of R1 and R2, and it commutes with the original projection. Thus the fused quotient retains exactly the least information needed to refine both component quotients.

Compatibility puts every fiber of r inside both relations. A pinned Mathlib right inverse chooses a representative of each point of W; the intersection inclusion makes its fused class independent of that choice. Surjectivity of r proves both surjectivity and uniqueness of the induced map.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/LeastCommonRefinement.least_common_refinement_universal_property`
