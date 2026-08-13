# Skew Symmetry of Finite Renyi Divergence

## Abstract

Finite Renyi divergence obeys alpha-complement skew symmetry, with exact endpoint residues and an unconditional form away from orders zero and one.

**Theorem 1.1 (Renyi divergence has alpha-complement skew symmetry).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\((\alpha=1 \Rightarrow \log (\sum _{i} p(i))= 0) \land \\(\alpha=0 \Rightarrow \log (\sum _{i} q(i))= 0)) \Rightarrow\\(\alpha-1) * D_{\alpha }(p\Vert \Vert q)= -\alpha * D_{1-\alpha }(q\Vert \Vert p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The primary duality statement is a product identity. Multiplication by alpha - 1 on one side and by -alpha on the other avoids dividing at either exceptional order, while exchanging the laws and replacing alpha by 1 - alpha.

The endpoint assumptions record exactly what Lean's totalized definition forces. At alpha = 1 the residue is log(sum p), and at alpha = 0 it is log(sum q). These conditions are weaker than normalization: unit total mass satisfies them through log 1 = 0, but zero total mass also satisfies them because Lean's Real.log 0 = 0.

Away from the endpoint cases, the two finite power sums agree termwise after commuting multiplication and simplifying the complementary exponent. No sign, support, or normalization property is used in that algebraic step.

Complementation maps the interval 0 < alpha < 1 onto itself. It sends alpha > 1 to the negative order 1 - alpha, outside the range of the frozen sub-unit data-processing theorem. This identity therefore does not mirror that theorem into an above-one data-processing inequality; that gap remains open.

**Theorem 1.2 (Normalized laws have alpha-complement skew symmetry at every order).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(\sum _{i} p(i)= 1 \land \sum _{i} q(i)= 1) \Rightarrow\\(\alpha-1) * D_{\alpha }(p\Vert \Vert q)= -\alpha * D_{1-\alpha }(q\Vert \Vert p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry_of_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both finite laws have unit total mass, the product-form identity holds at every real order. No pointwise nonnegativity or strict positivity assumption is needed; normalization is used only to discharge the two possible endpoint logarithms as log 1.

This is a sufficient specialization of the exact endpoint theorem, not a characterization of all admissible laws. In particular, the preceding zero-total-mass possibility shows why replacing the endpoint conditions by normalization would state a stronger hypothesis than the proof requires.

The conclusion remains in product form at alpha = 0 and alpha = 1. It does not identify the totalized order-one value with Kullback--Leibler divergence and asserts no limiting statement.

**Theorem 1.3 (Away from zero and one, skew symmetry is unconditional).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(\alpha\neq 0 \land \alpha\neq 1) \Rightarrow\\(\alpha-1) * D_{\alpha }(p\Vert \Vert q)= -\alpha * D_{1-\alpha }(q\Vert \Vert p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry_of_ne_zero_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When alpha differs from both zero and one, the endpoint obligations are vacuous and product-form skew symmetry is purely algebraic. The functions p and q are completely arbitrary finite real-valued functions: the theorem requires no normalization, nonnegativity, positivity, support condition, or other hypothesis on either one.

This unrestricted statement includes sub-unit, super-unit, and negative orders other than zero and one. Its breadth comes from retaining each base and exponent in the same term while only reversing the product, so the totalized behavior of Real.rpow at a zero base creates no extra case.

The absence of assumptions on p and q does not enlarge the range of the frozen data-processing result. For a super-unit alpha, the dual order is negative, and no data-processing inequality at that dual order has been proved here.

**Theorem 1.4 (Renyi divergence equals its scaled dual).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, \forall p, q: \iota\to \mathbb{R},\\(\alpha\neq 1 \land (\alpha=0 \Rightarrow \log (\sum _{i} q(i))= 0)) \Rightarrow\\D_{\alpha }(p\Vert \Vert q)= \frac{\alpha}{1-\alpha} * D_{1-\alpha }(q\Vert \Vert p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_eq_scaled_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Solving the product identity for its first divergence gives the familiar scaled-dual form with factor alpha/(1 - alpha). This division excludes alpha = 1, which is why the solved form is secondary to the endpoint-safe product identity.

Order zero remains within the statement. At that order the exact condition log(sum q) = 0 is still required by the totalized definition; no condition on the total mass of p is introduced. Away from zero, this remaining endpoint premise is vacuous.

The displayed equality is an algebraic rearrangement under a nonzero denominator. It supplies neither an order-one continuation nor a route from the frozen below-one data-processing inequality to an above-one theorem.

**Theorem 1.5 (Half-order Renyi divergence is symmetric).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\D_{\frac{1}{2} }(p\Vert \Vert q)= D_{\frac{1}{2} }(q\Vert \Vert p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_one_half_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order one half is fixed by alpha complementation. Specializing the unconditional away-from-endpoints identity therefore makes the two scalar factors equal and yields symmetry under exchange of p and q.

No hypothesis on either finite real-valued function is needed. This theorem is a specialization of the product identity rather than a second expansion of the Renyi definition or an appeal to symmetry of another coefficient.

Self-duality is specific to order one half within the alpha-complement map. The result does not assert symmetry at general order.

**Theorem 1.6 (The half-order dual Renyi divergence equals the Bhattacharyya expression).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\(\forall i, 0\le p(i)) \Rightarrow\\D_{\frac{1}{2} }(q\Vert \Vert p)= -2 * \log (\operatorname{bhattacharyya}(p, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_one_half_dual_eq_bhattacharyya` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual orientation at order one half agrees with the frozen Bhattacharyya link: D one half of q relative to p equals minus twice the logarithm of the Bhattacharyya coefficient written in the p, q orientation. The differing orientations make this a direct consistency check between the two frozen notions.

Only pointwise nonnegativity of p is assumed. The frozen Bhattacharyya identity is applied once in the p, q orientation, and half-order symmetry then exchanges the divergence arguments. Consequently no nonnegativity, normalization, positivity, or support premise on q is needed.

This cross-check does not strengthen the frozen Bhattacharyya theorem beyond its stated hypothesis, and it supplies no new data-processing or limiting result.

## References

- Truth anchor: `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_eq_scaled_dual`
- Truth anchor: `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_one_half_dual_eq_bhattacharyya`
- Truth anchor: `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_one_half_symmetry`
- Truth anchor: `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry`
- Truth anchor: `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry_of_ne_zero_one`
- Truth anchor: `D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry_of_normalized`
- Dependency: [D5/S3/RenyiDivergence/Basic](Basic.md)
