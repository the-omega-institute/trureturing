# Squared Hellinger Distance, Divergence, and Metric Laws

## Abstract

Squared Hellinger distance is dominated by KL divergence and satisfies its finite square-root metric laws.

**Theorem 1.1 (Squared Hellinger distance is dominated by KL divergence).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum _{i} q(i)=1) \land\\(\forall i, q(i)=0 \Rightarrow p(i)=0) \Rightarrow\\H^{2}(p, q)\le D(p || q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_le_kl_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative normalized finite mass functions p and q satisfying discrete absolute continuity p << q, squared Hellinger distance is at most the KL divergence D(p||q). Divergence is measured in nats.

The proof is an assembly of frozen results rather than a fresh analytic argument. The frozen estimate exp(-D) <= BC^2, together with positivity of the exponential and nonnegativity of the Bhattacharyya coefficient, gives exp(-D/2) <= BC. The frozen bridge H^2=2(1-BC) then yields H^2 <= 2(1-exp(-D/2)). Finally, mathlib's Real.add_one_le_exp gives 1-exp(-x) <= x at x=D/2 and closes the chain.

Nonnegativity of D is supplied by the frozen kl_divergence_nonneg theorem; it is not an additional assumption. Real.add_one_le_exp holds for every real argument, so the scalar library fact is stronger than the nonnegative-domain estimate needed by this proof.

Warning: H^2 <= D and the frozen inequality H^2/2 <= TV point in the same direction away from H^2. They cannot be chained to bound total variation above by the divergence. Pinsker and Bretagnolle--Huber give that upper control; the present comparison serves a different purpose. The reversed chain is not supported by this module.

**Theorem 1.2 (Hellinger--KL domination is strict on a Bool witness).**

$$\begin{gathered}p(\operatorname{true})=1, p(\operatorname{false})=0,\\q(\operatorname{true})=\frac{1}{4}, q(\operatorname{false})=\frac{3}{4},\\H^{2}(p, q)=1<\log 4=D(p || q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_lt_kl_divergence_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strictness is itself kernel-checked. On Bool, p is the point mass at true and q assigns masses 1/4 and 3/4 to true and false. Lean computes H^2(p,q)=1 and D(p||q)=log 4, then verifies 1 < log 4. Thus the main bound is not an identity disguised as an inequality.

**Theorem 1.3 (Squared Hellinger distance is unconditionally nonnegative).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\0\le H^{2}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity holds for arbitrary finite real functions. No pointwise sign condition, normalization, or support hypothesis appears: the result is the coordinatewise nonnegativity of squares summed over a finite type.

**Theorem 1.4 (Squared Hellinger distance is unconditionally symmetric).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\H^{2}(p, q)=H^{2}(q, p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry likewise holds on all finite real functions without hypotheses. Exchanging p and q negates each square-root gap and leaves its square unchanged.

**Theorem 1.5 (The zero set is square-root equality with an exact domain boundary).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\H^{2}(p, q)=0 \Leftrightarrow \\(i\mapsto \sqrt {p(i)})=(i\mapsto \sqrt {q(i)}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_eq_zero_iff_sqrt_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vanishing characterization consists of three inseparable statements. One might expect the conclusion to mirror total_variation_eq_zero_iff, which separates arbitrary finite real functions with no hypotheses. It does not, and the precise unconditional theorem is instead hellinger_sq_eq_zero_iff_sqrt_eq: H^2 vanishes exactly when the coordinatewise square-root functions agree.

The obstruction is not relegated to a caveat. The theorem hellinger_sq_negative_counterexample takes Unit with the constant functions p=-1 and q=-2. They are distinct, but Real.sqrt annihilates both, so H^2(p,q)=0. The counterexample is a theorem in the module, not a remark: the limitation is kernel-checked and frozen alongside the characterization.

The companion theorem hellinger_sq_eq_zero_iff recovers separation exactly on the pointwise nonnegative cone: if p(i) and q(i) are nonnegative for every coordinate, then H^2(p,q)=0 if and only if p=q. No normalization is required for this recovery.

The comparison with total variation is therefore exact. Total variation separates points everywhere, whereas squared Hellinger distance separates points only where the square root is injective. Real.sqrt collapses the entire nonpositive half-line, and pointwise nonnegativity is precisely the domain restriction that removes this obstruction.

**Theorem 1.6 (The square-root Hellinger distance satisfies the triangle inequality).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q, r: \iota\to \mathbb{R},\\\sqrt {H^{2}(p, r)}\le \sqrt {H^{2}(p, q)}+\sqrt {H^{2}(q, r)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDivergence.sqrt_hellinger_sq_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is stated for sqrt(H^2), the Hellinger distance itself, and holds for arbitrary finite real functions with no hypotheses. Together with unconditional nonnegativity and symmetry, it records the metric laws that survive on the all-real domain; point separation remains restricted exactly as described above.

The triangle inequality cost nothing to obtain. It is Minkowski's inequality in l2, obtained by applying mathlib's existing Real.Lp_add_le at exponent two to the two coordinatewise square-root gaps. Their sum is the direct p-to-r gap.

No new definition, normed-space instance, or EuclideanSpace wrapper was introduced. Building such scaffolding to reach a single inequality would not have been worthwhile, and the existing finite Lp theorem made it unnecessary.

The TotalVariation bucket now contains Pinsker's bound, the metric structure with the attained variational characterization, data-processing contraction, Bretagnolle--Huber with the Bhattacharyya coefficient, the Hellinger comparison with total variation, and now the Hellinger--KL comparison together with these square-root metric properties. All divergence units in this narrative are nats.

No Renyi divergence, reverse bound of D by H^2, equality analysis, or measure-theoretic analogue is claimed.

## References

- Truth anchor: `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_comm`
- Truth anchor: `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_eq_zero_iff_sqrt_eq`
- Truth anchor: `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_le_kl_divergence`
- Truth anchor: `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_lt_kl_divergence_witness`
- Truth anchor: `D5/S3/TotalVariation/HellingerDivergence.hellinger_sq_nonneg`
- Truth anchor: `D5/S3/TotalVariation/HellingerDivergence.sqrt_hellinger_sq_triangle`
- Dependency: [D5/S3/TotalVariation/Hellinger](Hellinger.md)
