# Sound and complete normalized even search

## Abstract

Sound and complete normalized even search.

**Theorem 1.1 (Sound and complete normalized even search).**

$$\forall k,B\in Nat,0<k\Rightarrow{\operatorname{admissibleWindowCheck}\left(k, B\right)=true\iff \operatorname{AdmissibleWindowWitness}\left(k, B\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/AdmissibleWindowFiniteSearch.admissibleWindowCheck_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural tuple size k and every natural width B, the finite Boolean search succeeds exactly when the existing all-prime admissible-window proposition holds. Completeness subtracts the minimum offset, preserves cardinality and omitted residues, and proves that a normalized admissible tuple is even. Soundness uses the imported finite prime-cutoff theorem. The result concerns standard admissible-tuple optimization and claims formalization content, not new number theory.

## References

- Truth anchor: `D5/S3/PrimeGaps/AdmissibleWindowFiniteSearch.admissibleWindowCheck_eq_true_iff`
- Dependency: [D5/S3/PrimeGaps/DHLAdmissibleDiameterTransfer](DHLAdmissibleDiameterTransfer.md)
- Dependency: [D5/S3/PrimeGaps/PrimeGapAdmissibilityContractBridge](PrimeGapAdmissibilityContractBridge.md)
