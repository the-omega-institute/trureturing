# Ququint Numerical Certificate Assembly

## Abstract

All thirty-two explicit numerical branch matrices are negative definite.

**Theorem 1.1 (All numerical branches are negative definite).**

$$\forall s:\mathrm{Fin} 32,\mathrm{Matrix}.\mathrm{PosDef}(-\mathrm{D5}.\mathrm{S3}.\mathrm{Quantum}.\mathrm{Magic}.\mathrm{QuquintCertificateData}.\mathrm{branch}(s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

branch is the public numerical matrix family in D5.S3.Quantum.Magic.QuquintCertificateData. The proof consumes all thirty-two LDL identities, verifies all 128 pivots are positive, and proves the lower triangular factors invertible. Matrix.PosDef.diagonal and IsUnit.posDef_star_right_conjugate_iff yield the result.

QuquintCertificateBridge identifies the numerical matrices with the phase-point quadratic forms through QuquintWignerCriticalGeometry.tangentEquiv. QuquintFiniteMaximum consumes this certificate to prove strict second-variation negativity. QuquintStrictDecrease.exact_change and directional_decrease prove the normalized perturbation identity and strict mana decrease along each nonzero constrained tangent direction. This does not classify other directions or critical points, cover other dimensions, solve general mana extremisation, identify Claim C as an author-verbatim conjecture, or assert global novelty beyond the recorded search.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative`
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateFirst](QuquintCertificateFirst.md)
- Dependency: [D5/S3/Quantum/Magic/QuquintCertificateSecond](QuquintCertificateSecond.md)
