# Nyman-Beurling Finite Gram Distance

## Abstract

The source finite-stage Gram formulas hold on the actual complex Nyman-Beurling L2 carrier.

The carrier is Lp(C, 2, volume restricted to (0,infinity)), using the repository's canonical positiveMeasure. The target chi is the Lp class of the indicator of (0,1). For every natural a at least one, f_a is the complexification of the canonical real fractionalReciprocal vector; sourceVector_coe_ae proves its representative is x |-> ofReal(fract(1/(a*x))) almost everywhere. target_coe_ae likewise identifies the indicator representative, and target_norm_sq proves its squared norm is one from the measure of (0,1).

For each natural N, coefficients lie in EuclideanSpace C (Fin N), with i representing the source index a=i+1. V_N is finite synthesis, S_N is the span of f_1 through f_N, G_N = V_N* V_N, and b_N = V_N* chi. The distance d_N is independently defined as Metric.infDist chi S_N. MP denotes the constructed Moore-Penrose inverse with all four Penrose identities proved in the attributed upstream port.

**Theorem 1.1 (Canonical finite synthesis).**

$$\forall N\in \mathbb{N}, \forall c\in \mathbb{C}^{N}, V_{N}c = \sum_{i\in \operatorname{Fin}(N)}c_{i}f_{i+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.synthesis_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis-defined continuous linear map has exactly the source's finite sum, with the one-based index represented by i+1.

**Theorem 1.2 (Range equals the source span).**

$$\forall N\in \mathbb{N}, \operatorname{range}(V_{N}) = S_{N}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.synthesis_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shell is defined as the span. Its finite dimension and completeness are derived, so its orthogonal projection needs no extra closure assumption.

**Theorem 1.3 (Gram entries).**

$$\forall N\in \mathbb{N}, \forall i,j\in \operatorname{Fin}(N), (G_{N}e_{j})_{i} = \langle f_{i+1}, f_{j+1}\rangle$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.gramOperator_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The e_j are the standard orthonormal coefficient vectors. These entries identify the Gram operator with the source matrix.

**Theorem 1.4 (Target correlations).**

$$\forall N\in \mathbb{N}, \forall i\in \operatorname{Fin}(N), (b_{N})_{i} = \langle f_{i+1}, \mathrm{chi}\rangle$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.correlations_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inner product is conjugate-linear in its first argument, so this is the source's b_N = V_N* chi convention.

**Theorem 1.5 (All three finite-stage Gram distance clauses).**

$$\begin{gathered}\forall N\in \mathbb{N}, \\P_{S_{N}} = V_{N}\operatorname{MP}(G_{N})V_{N}^{*}\\\land d_{N}^{2} = 1-\langle b_{N}, \operatorname{MP}(G_{N})b_{N}\rangle\\\land (\forall A:\mathbb{C}^{N}\equiv_{\mathbb{C}}\mathbb{C}^{N}, A = G_{N} \Rightarrow d_{N}^{2} = 1-\langle b_{N}, A^{-1}b_{N}\rangle)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.nyman_beurling_finite_gram_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both distance equalities are in C, with the real squared distance coerced into C. The first therefore also proves that the Gram quadratic expression is real. The projection clause is an equality of operators on the full Lp carrier. Only the third clause assumes invertibility, expressed by a linear equivalence whose underlying map is the Gram operator. The theorem holds for every natural N, including zero, hence in particular every source stage N at least one. It asserts the finite distance formula, with no assertion about the limiting residual or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.correlations_entry`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.gramOperator_entry`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.nyman_beurling_finite_gram_distance`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.synthesis_apply`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.synthesis_range`
- Dependency: [D5/S3/Constants/InnerProducts/FractionalReciprocalInnerProduct](../../Constants/InnerProducts/FractionalReciprocalInnerProduct.md)
- Dependency: [D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance](FiniteSynthesisGramDistance.md)
