# Finite differences detect a noninteger power

## Abstract

Finite differences detect a noninteger power.

For real functions write Delta_t^R f(x) for R iterations of u -> f(u+t)-f(u), evaluated at x, and D^R f for the iterated real derivative. The mean-value and real-power derivative formulas are classical finite-difference tools. Their square-root-scale application isolates the nonaffine part of the target.

**Theorem 1.1 (Differentiate at all finite-difference nodes).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.has_deriv_at_fwd_diff_iter`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.has_deriv_at_fwd_diff_iter` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For every real t,x, natural n and real functions f,fprime, if HasDerivAt f (fprime(x+i t)) (x+i t) for every natural i<=n, then HasDerivAt (Delta_t^n f) (Delta_t^n fprime(x)) x. Neither positivity of t nor differentiability away from the finitely many nodes is assumed.

**Theorem 1.2 (The derivative is evaluated inside the original interval).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.exists_fwd_diff_iter_eq_iterated_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.exists_fwd_diff_iter_eq_iterated_deriv` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For every real f, natural R, real x and t>0, assume D^k f is differentiable at every y in [x,x+Rt] for every natural k<R. There exists y in this same closed interval such that Delta_t^R f(x)=t^R D^R f(y). The statement includes R=0.

**Theorem 1.3 (A derivative budget controls the difference).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.abs_fwd_diff_iter_le`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.abs_fwd_diff_iter_le` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For every real f, natural R, real x,D and t>0, under the preceding differentiability hypothesis and |D^R f(y)|<=D for every y in [x,x+Rt], |Delta_t^R f(x)|<=t^R D. D is an arbitrary real bound; the hypotheses supply any necessary nonnegativity.

**Theorem 1.4 (Real powers on the positive half-line).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos` (`✓ std3`). ∎

*Citation.* Joris Roos; source proof authored by Codex (2026). *LeanSpherical PlanarResolution: iterated derivatives of positive real powers*. URL: <https://raw.githubusercontent.com/roos-j/lean-spherical/2b0e2bbf35cdf45ab99d1d77b2dea37b214fe236/LeanSpherical/Auto/Spherical/BRSRadial/PlanarResolution.lean>.

*Commentary.*

For every real p and natural n, D^n(u -> u^p) agrees on (0,infinity) with u -> [product_{i<n}(p-i)] u^(p-n). This positive-half-line formula is ported from the pinned Apache-licensed LeanSpherical source identified in the literature note.

**Theorem 1.5 (No difference order annihilates a nonintegral power).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.rpow_fwd_diff_iter_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.rpow_fwd_diff_iter_ne_zero` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For every real beta, natural R, and real x,t>0, if beta differs from every natural number, Delta_t^R(u -> u^beta)(x) is nonzero. No assumption beta>0 is imposed. The derivative product has no zero factor on the positive interval.

**Theorem 1.6 (The unit-step signal is strictly positive).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.unit_signal_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.unit_signal_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For every real beta differing from every natural number and every natural R, |Delta_1^R(u -> u^beta)(1)|>0.

**Theorem 1.7 (Homogeneity of the power difference).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.rpow_fwd_diff_iter_scale`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.rpow_fwd_diff_iter_scale` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For every real beta, natural R and real t>0, Delta_t^R(u -> u^beta)(t)=t^beta Delta_1^R(u -> u^beta)(1).

**Theorem 1.8 (Orders at least two kill affine functions).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.affine_fwd_diff_iter_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.affine_fwd_diff_iter_eq_zero` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For all real a,b,t and natural R>=2, Delta_t^R(u -> a+b u) is the zero function, as an equality of functions. No sign assumption on t is required.

**Theorem 1.9 (The affine part disappears exactly).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.affine_power_fwd_diff_iter`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.affine_power_fwd_diff_iter` (`✓ std3`). ∎

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For all real a,b,c,beta, natural R>=2 and real t>0, Delta_t^R(u -> a+b u-c u^beta)(t)=-c t^beta Delta_1^R(u -> u^beta)(1).

**Theorem 1.10 (The exact square-root-scale target signal).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.target_signal_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.target_signal_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions, Section 3.3: Interpolation*. URL: <https://dlmf.nist.gov/3.3>.

*Commentary.*

For all real B,C,beta,rho, natural R>=2, rho>0 and beta differing from every natural number, S=rho^beta |Delta_1^R(u -> u^beta)(1)|/16 is strictly positive. For every real n>0, |Delta_{rho/sqrt(n)}^R(u -> (1-u/C)/(2B)-u^beta/16)(rho/sqrt(n))|=S n^(-beta/2). There are no sign or nonzero hypotheses on B or C: real division is the totalized Lean operation, and the corresponding term is affine for all their values.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.abs_fwd_diff_iter_le`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.affine_fwd_diff_iter_eq_zero`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.affine_power_fwd_diff_iter`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.exists_fwd_diff_iter_eq_iterated_deriv`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.has_deriv_at_fwd_diff_iter`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.rpow_fwd_diff_iter_ne_zero`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.rpow_fwd_diff_iter_scale`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.target_signal_scaled`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.unit_signal_pos`
