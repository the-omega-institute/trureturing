# Golden Desubstitution Normal-Form Depth

## Abstract

Identify the exact length of every golden desubstitution path to its chosen normal form.

**Theorem 1.1 (Exact depth to the chosen normal form).**

$$\forall n r\in \mathbb{N},\ \left(\exists xs, length(xs)=r \land \operatorname{IsChain}(\operatorname{desubStep} n, xs) \land \operatorname{getLast}(n, xs)=\operatorname{nf}(\operatorname{desubStep}, \operatorname{desubStepTermination}, \operatorname{desubStepLocalConfluence}, n)\right) \iff r=\operatorname{desubstitutionShift}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Powers/GoldenDesubstitutionNfDepth.golden_desubstitution_nf_exact_depth_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every chain ending at the chosen normal form has the unique length measured by the least occupied Zeckendorf index.

## References

- Truth anchor: `D5/S1/Words/Powers/GoldenDesubstitutionNfDepth.golden_desubstitution_nf_exact_depth_iff`
- Dependency: [D5/S1/Words/Powers/GoldenDesubstitutionDepth](GoldenDesubstitutionDepth.md)
