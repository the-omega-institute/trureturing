# Unit Gram Indistinguishability

## Abstract

Unit Gram overlap detects equality and defines an equivalence relation.

**Theorem 1.1 (Unit Gram overlap is exactly record equality).**

$$\forall i, j, \Vert e_{i} \Vert = 1 \land \Vert e_{j} \Vert = 1 \Rightarrow\\(\langle e_{i}, e_{j} \rangle = 1 \Leftrightarrow e_{i} = e_{j}) \land\\\operatorname{Equivalence}(\sim_{G}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/UnitGramIndistinguishability.unit_gram_overlap_characterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e_i be a family of unit vectors in a real or complex inner-product space. The Gram overlap of e_i and e_j is one exactly when the two record vectors are equal.

Consequently, declaring two record indices indistinguishable when their Gram overlap is one gives a reflexive, symmetric, and transitive relation. Its classes are precisely the fibers of the record map.

Pinned Mathlib and Loogle both returned the exact theorem inner_eq_one_iff_of_norm_eq_one. The Lean proof applies that result directly and only packages equality as an equivalence relation; it does not reprove the equality case of Cauchy-Schwarz.

## References

- Truth anchor: `D5/S3/Quantum/PureState/UnitGramIndistinguishability.unit_gram_overlap_characterization`
