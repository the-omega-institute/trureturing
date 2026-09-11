# Gamma Scale Modulus

## Abstract

The actual positive Gamma resolvent sum controls symmetric prime-translation changes across moving-window thresholds.

**Definition 1.1 (Finite positive part of the actual Gamma multiplier).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gammaShiftPartial`

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gammaShiftPartial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One plus the first J terms 2*xi^2/(b*(b^2+xi^2)), b=2j+1/2. The classical digamma identity identifies the infinite completion with 1+gamma(xi)-gamma(0). That special-function identification remains a separate paper bridge, not an alternative definition of gamma.

**Theorem 1.2 (Unweighted energy remains controlled).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_shift_partial_one_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_shift_partial_one_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite resolvent summand is nonnegative for every real frequency. Thus the partial weight is at least one, including J=0 and xi=0. This supplies the low-frequency side of the live modulus estimate.

**Theorem 1.3 (Explicit harmonic high-frequency floor).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_shift_partial_high_frequency`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_shift_partial_high_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For |xi|>=2J, each actual summand dominates 1/(2(j+1)). Summing and using the existing harmonic number gives the floor 1+harmonic(J)/2. No lower bound on an unspecified operator is supplied as a premise.

**Theorem 1.4 (Actual symmetric-translation multiplier bound).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_controlled_cosine_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_controlled_cosine_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real shifts s,t and frequency xi, the difference |cos(s*xi)-cos(t*xi)| is bounded by [2J*|s-t|+2/(1+harmonic(J)/2)] times the finite Gamma weight. The proof combines the real cosine Lipschitz bound below the cutoff with the harmonic floor above it. Both shift signs and all frequencies are included.

**Theorem 1.5 (An explicit unit-interval majorant for Gamma scaling).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_log_scale_derivative_term`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_log_scale_derivative_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For b=2j+5/2 and b-1<=u<=b, the log-frequency derivative term 4*b*t^2/(b^2+t^2)^2 is at most (5/3)*4*u*t^2/(u^2+t^2)^2. Integrating disjoint unit intervals and adding the first Gamma term gives the paper bound |gamma(r*xi)-gamma(xi)|<=6*|log r|.

The concrete consumer dilates the original Weil forms to [-1,1], keeps every prime power in a common finite range, and obtains an explicit common-form-norm modulus. The original prime block has an ordinary operator-norm jump at activation; no contrary continuity is asserted. Plancherel, common-domain/core identification, norm-resolvent continuity, and local simple-even propagation are paper proofs in the existing RH volume. The numerical file certifies finite coefficients in the parameterized estimate. Lean elaboration, Scribe emission and transitive axiom checks have not run. No global gap or unbounded-scale Xi convergence follows from this local continuity theorem.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gammaShiftPartial`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_controlled_cosine_difference`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_log_scale_derivative_term`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_shift_partial_high_frequency`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaScaleModulus.gamma_shift_partial_one_le`
