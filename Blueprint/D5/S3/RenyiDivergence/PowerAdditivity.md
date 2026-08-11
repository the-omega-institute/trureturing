# Power Additivity of Finite Renyi Divergence

## Abstract

Repeating a finite nonnegative experiment n times multiplies its Renyi divergence exactly by n at every real order, without normalization.

**Theorem 1.1 (Finite Renyi divergence is additive on i.i.d. powers).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R},\\\forall p, q: \iota\to \mathbb{R},\\\forall n \in \mathbb{N},\\((\forall i, 0\le p(i)) \land (\forall i, 0\le q(i))) \Rightarrow \\D_{\alpha }(\operatorname{iidPower}(p, n)\Vert \Vert \operatorname{iidPower}(q, n))=\\n \cdot D_{\alpha }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/PowerAdditivity.renyi_divergence_power_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeating an experiment n times multiplies its Renyi divergence by exactly n. This identity is a prerequisite for sample-complexity statements: it converts the distinguishability of two single-trial laws into the number of independent trials required to distinguish their repeated observations.

The encoding is chosen so that induction consumes the frozen binary theorem directly. IidSpace is a recursive right-associated product: IidSpace iota 0 is PUnit, while IidSpace iota (n+1) is iota times IidSpace iota n; iidPower assigns mass one to the empty product and the corresponding product mass at a successor. Consequently, the successor sample type and mass are definitionally in the product shape accepted by renyi_divergence_product_additive. The conventional alternative Fin n -> iota requires no new definitions, but it would require every finite sum to be re-indexed through Fin.consEquiv before the binary theorem could apply. Two minimal definitions were judged cheaper than a re-indexing at every step. The induction therefore applies the frozen theorem directly rather than re-deriving additivity.

The final theorem requires strictly less than the theorem on which its induction depends. Binary additivity requires both marginal power sums to be nonzero, whereas the n-fold statement assumes only pointwise nonnegativity of p and q. The separately stated, load-bearing power-sum lemma identifies the n-copy power sum with the n-th power of the single-trial power sum. When the base is nonzero, pow_ne_zero supplies the non-vanishing premise needed by the frozen binary theorem; when the base is zero, the complementary branch is settled directly. Both branches are internal to the proof, so no power-sum hypothesis survives in the theorem statement.

The zero-copy case is clean. IidSpace iota 0 is PUnit, iidPower is the empty product of value one, and its power sum is one. The left side is therefore (1/(alpha-1)) times log 1 = 0, while the right side is zero times D_alpha(p,q) = 0. Neither non-vanishing nor normalization is consumed in this case.

The freedoms of the binary theorem are inherited without narrowing: alpha may be any real number, and neither p nor q is required to be normalized. Thus the n-fold theorem introduces no order restriction and no probability-mass requirement beyond the stated pointwise nonnegativity.

No sample-complexity corollary, order-one limit, measure-theoretic analogue, or theorem for non-identical factors is claimed. Products of non-identical factors remain the territory of the frozen binary additivity theorem.

## References

- Truth anchor: `D5/S3/RenyiDivergence/PowerAdditivity.renyi_divergence_power_additive`
- Dependency: [D5/S3/RenyiDivergence/ProductAdditivity](ProductAdditivity.md)
