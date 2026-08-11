# Power Additivity of Finite Classical KL Divergence

## Abstract

Repeating a finite strictly positive probability law n times multiplies its classical KL divergence exactly by n.

**Theorem 1.1 (Finite classical KL divergence is additive on i.i.d. powers).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\forall n \in \mathbb{N},\\((\sum _{i} p(i)=1) \land (\forall i, 0<p(i)) \land (\forall i, 0<q(i))) \Rightarrow \\D(\operatorname{iidPower}(p, n)\Vert \Vert \operatorname{iidPower}(q, n))=\\n \cdot D(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/PowerAdditivity.kl_divergence_power_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeating an experiment n times multiplies its classical KL divergence by exactly n. Together with the repository's testing-error floors, this identity is the algebraic step that converts a per-trial divergence bound into one indexed by the sample count.

The n-fold encoding is reused, not rebuilt. IidSpace and iidPower are imported from the Renyi power-additivity module that landed one wave earlier, and this file declares no definition of its own. A second n-fold encoding would duplicate a source of truth. This import crosses buckets within S3, as the DivergenceSupport bucket already does when it imports from the Divergence bucket.

The interesting finding is negative: the hypothesis shedding proved for the Renyi n-fold theorem does not occur here. There, the power-sum lemma handled both the nonzero-base and zero-base branches internally, so no non-vanishing premise survived into the theorem statement. Classical divergence has no branch in which failed positivity makes both sides collapse to a common value. Every successor application of the frozen binary theorem therefore still needs strict positivity of p, q, iidPower p n, and iidPower q n. This is a structural asymmetry between the two divergence families, not a shortcoming of the proof. One hypothesis is absent: q need not be normalized, because the frozen binary theorem does not normalize its reference functions. The module claims only that these are the hypotheses forced by this proof, not that they are logically minimal under every possible proof strategy.

Two named propagation lemmas carry the successor step. iid_power_pos preserves strict positivity through the finite product and discharges the binary theorem's positivity arguments for the two powered factors. iid_power_sum_one preserves total mass one and supplies the required normalization of the powered primary factor. They are the classical n-fold analogues of the power-sum lemma in the Renyi module, and each is consumed at its corresponding argument of the binary theorem.

The zero-copy case is clean. IidSpace iota 0 is PUnit, both empty products have value one, and the sole summand is log(1/1) = 0. The right side is zero times the one-copy divergence. Neither normalization nor positivity is consumed in this case.

No sample-complexity corollary is yet claimed; composing this theorem with the testing-error floors is a separate step. No order-one connection to the Renyi family, measure-theoretic analogue, or theorem for non-identical factors is claimed. Products of non-identical factors remain the territory of the frozen binary theorem.

## References

- Truth anchor: `D5/S3/DivergenceSupport/PowerAdditivity.kl_divergence_power_additive`
- Dependency: [D5/S3/Divergence/ProductAdditivity](../Divergence/ProductAdditivity.md)
- Dependency: [D5/S3/RenyiDivergence/PowerAdditivity](../RenyiDivergence/PowerAdditivity.md)
