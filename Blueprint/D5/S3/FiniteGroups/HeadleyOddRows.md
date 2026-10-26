# HeadleyOddRows

## Abstract

Gordon predecessor connects every row without treating an odd abelian group as cyclic.

**Theorem 1.1 (Positive wrap and the complete predecessor orbit).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall i \in Nat,\; (i \le \operatorname{volume}\left(ds\right)) \Rightarrow (\operatorname{apply}\left(\operatorname{pow}\left(\operatorname{predecessor}\left(ds\right), i\right), 0\right) = \operatorname{residue}\left(ds, \operatorname{volume}\left(ds\right)-i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddRows.predecessor_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N=volume(ds)>0, the i-th predecessor of zero is residue(N-i) for every i up to N, closure included. The proof invokes the original positive-index pred_residue at N-i; it never applies that theorem at zero. The empty radix list has N=1 and remains in scope. Rank is a set equivalence, not an additive group coordinate.

**Theorem 1.2 (One cycle on every mixed-radix row).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \operatorname{IsCycleOn}\left(\operatorname{predecessor}\left(ds\right), \operatorname{univ}\left(\operatorname{Box}\left(ds\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddRows.predecessor_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual predecessor equivalence has inverse x↦residue(rank(x)+1). Positive-index predecessor steps take every residue to zero, so every row is on the same cycle. The original GordonCarry rankEquiv, rank_residue, residue_zero and pred_residue are reused directly; GordonProduct residue_eq_iff is exposed at its original owner without changing its proof.

**Theorem 1.3 (The ordinary row difference).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall h \in \operatorname{Box}\left(ds\right),\; \operatorname{deltaZero}\left(ds, h\right) = \operatorname{rowZero}\left(ds, h\right)-h$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddRows.delta_zero_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row map is negation. Its actual difference is negative doubling, which is a permutation by the original box_two_injective and finiteness. The inverse is negative half, where half is the inverse of that original doubling map.

**Theorem 1.4 (The carry supplies the distinguished actual difference).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall h \in \operatorname{Box}\left(ds\right),\; \operatorname{deltaOne}\left(ds, h\right) = \operatorname{rowOne}\left(ds, h\right)-h$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddRows.delta_one_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinguished row map is pred after negation. Its coefficient-one difference is -carry(-h)-ones, with the sign derived from the original carry definition. Both maps are actual equivalences: their inverses are negative successor and negative inverse-carry evaluated at -y-ones. No row orthomorphism is assumed.

**Theorem 1.5 (Traversal order gives predecessor).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall h \in \operatorname{Box}\left(ds\right),\; \operatorname{rowOne}\left(ds, \operatorname{rowZero}\left(ds, h\right)\right) = \operatorname{predecessor}\left(ds, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddRows.row_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying negation and then the distinguished row map gives pred. This equality is the row return used by HeadleyOddProduct. It replaces the cyclic translation used by the earlier native inverse-pair construction and works for noncyclic odd groups.

**Theorem 1.6 (A consumed normalization of the original unconditional decomposition).**

$$\forall H \in Type,\; [\operatorname{AddCommGroup}\left(H\right)] [\operatorname{Fintype}\left(H\right)] (\operatorname{Odd}\left(\operatorname{card}\left(H\right)\right)) \Rightarrow (\exists ds \in \operatorname{List}\left(OddRadix\right),\; \operatorname{Nonempty}\left(\operatorname{AddEquiv}\left(H, \operatorname{Box}\left(ds\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyOddRows.odd_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original GordonFullSet finite_abelian_presentation, chain_classification and case_transport supply the unconditional trichotomy. Odd cardinality excludes the two even alternatives, using the original card_even_of_power_box. Their original statements, assumptions and proof bodies are preserved; only listed visibility changes are made. This is not a new decomposition theorem and does not invoke the nonzero-total sequencing result. The full product registration attempt and its remaining dependent-family obligations are disclosed at https://github.com/the-omega-institute/trureturing/issues/21042; the existing successful GordonCarry registration is preserved.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddRows.delta_one_spec`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddRows.delta_zero_spec`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddRows.odd_box`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddRows.predecessor_cycle`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddRows.predecessor_orbit`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyOddRows.row_return`
- Dependency: [D5/S3/FiniteGroups/GordonFullSet](GordonFullSet.md)
