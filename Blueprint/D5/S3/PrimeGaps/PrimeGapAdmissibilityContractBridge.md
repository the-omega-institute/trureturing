# Direct omission and local residue counts

## Abstract

Direct omission and local residue counts.

**Theorem 1.1 (Direct omission and local residue counts).**

$$\forall H\in \operatorname{Finset}\left(Int\right),\operatorname{DirectTupleAdmissible}\left(H\right)\iff{\forall p\in Nat,\operatorname{Prime}\left(p\right)\Rightarrow\operatorname{localResidueCount}\left(H, p\right)<p}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/PrimeGapAdmissibilityContractBridge.directTupleAdmissible_iff_local_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This inherited equivalence applies to every finite integer offset set. The all-prime local count counts negated residue classes, while DirectTupleAdmissible asks for a missing direct residue. Negation identifies their cardinalities. No positivity assumption on H is needed.

## References

- Truth anchor: `D5/S3/PrimeGaps/PrimeGapAdmissibilityContractBridge.directTupleAdmissible_iff_local_residue`
- Dependency: [D5/S3/Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion](../Analytic/PrimeProducts/FiniteLocalResidueBlockingCriterion.md)
