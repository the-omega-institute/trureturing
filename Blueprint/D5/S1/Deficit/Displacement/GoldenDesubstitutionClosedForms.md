# Golden Desubstitution Face-Length Closed Forms

## Abstract

The two face lengths have individual closed forms in terms of the hidden product nS.

**Theorem 1.1 (The expansion-face length has a hidden-product closed form).**

$$n\neq0 \implies \lambda_{+}(n) = \log(nS n) - \psi \cdot \log n$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms.lambdaPlus_eq_log_nS_sub_goldenConj_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding log n and log(nS n) over their prime factorizations reduces the equality to one identity for each exponent. The hidden product replaces an exponent by its golden substitution start, which is the Zeckendorf displacement decode. The expansion-face beta reading is exactly that displacement minus the original exponent multiplied by the golden conjugate, so the finite sums agree termwise.

**Theorem 1.2 (The contraction-face length has a hidden-product closed form).**

$$n\neq0 \implies \lambda_{-}(n) = \log(nS n) - \phi \cdot \log n$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms.lambdaMinus_eq_log_nS_sub_goldenRatio_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same factorization expansion applies on the contraction face. The public two-face spread and the identity phi minus psi equals sqrt(5) convert the expansion reading into the conjugate reading: displacementDecode at an exponent minus phi times that exponent. Summing these exponentwise identities gives log(nS n) minus phi log n.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms.lambdaMinus_eq_log_nS_sub_goldenRatio_log`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms.lambdaPlus_eq_log_nS_sub_goldenConj_log`
- Dependency: [D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength](GoldenDesubstitutionConjugateLength.md)
