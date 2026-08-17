# Nonzero Two-Torsion Phase Indices

## Abstract

The nonzero indices killed by doubling modulo twenty-four are exactly three pairs.

**Theorem 1.1 (The nonzero two-torsion indices form a three-point set).**

$$\forall q\in (\mathbb{Z}/24\mathbb{Z})^{2},\ (2q=0 \land q\neq0) \Leftrightarrow q=(0, 12) \lor q=(12, 0) \lor q=(12, 12).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/TwoTorsionPhaseIndices.nonzero_two_torsion_phase_indices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An index in the product of two residue groups modulo twenty-four is nonzero and killed by doubling exactly when it is one of (0,12), (12,0), or (12,12). Thus the nontrivial two-torsion subgroup has the three displayed phase indices.

Pinned Mathlib supplies ZMod.neg_eq_self_iff, which classifies one coordinate fixed by negation, and ZMod.natCast_zmod_val, which identifies its nonzero residue as twelve. The Lean proof applies these results coordinatewise and excludes the zero pair.

This closes only the two-torsion index classification in remark 27.596, clause 3. It does not formalize the associated phase values, the claimed cross-tower isomorphism, or any exhaustive classification of the surrounding SIC data.

Repository searches found no equivalent D5 declaration. The pinned Mathlib source search found the general one-coordinate theorem; local smart-search name queries found no full product theorem.

## References

- Truth anchor: `D5/S3/QuantumContext/TwoTorsionPhaseIndices.nonzero_two_torsion_phase_indices`
