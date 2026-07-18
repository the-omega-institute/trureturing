/- GID: D5/S3/Zeros/EulerWindows
   generality: I
   mirror-B: D5/B/S3/Zeros/EulerWindows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bind the prime-axis zeta trace and finite Euler-window zero-freeness. -/

import D5.S3.Weil.EulerProduct
import D5.S3.Weil.SpectralHilbert

namespace D5.S3.Zeros.EulerWindows

open D5.S1.Digit
open D5.S3.Weil.Convention
open D5.S3.Weil.EulerProduct
open D5.S3.Weil.SpectralHilbert
open scoped BigOperators ComplexConjugate

/-- The coordinate sum of the prime-axis labeled-zeta family. -/
noncomputable def primeAxisHeatTrace (s : ℂ) : ℂ :=
  ∑' a : PrimeAxisTable, labeledZetaCoefficient s a

/-- In its absolute-convergence half-plane, the prime-axis heat trace is classical zeta. -/
theorem prime_axis_heat_trace_eq_zeta (s : ℂ) (hs : 1 < s.re) :
    primeAxisHeatTrace s = classicalZeta s := by
  have hKernel := labeled_zeta_kernel s 0 (by simpa using hs)
  simpa [primeAxisHeatTrace, labeledZetaCoefficient] using hKernel

/-- No finite prime Euler window can produce a zero at positive real abscissa. -/
theorem finite_euler_window_ne_zero (S : Finset ℕ)
    (hPrime : ∀ p ∈ S, p.Prime) {s : ℂ} (hs : 0 < s.re) :
    finiteEulerProduct S s ≠ 0 := by
  apply (finite_euler_zero_free_and_pole_locus S hPrime s).1.mpr
  intro p hpS hzero
  obtain ⟨k, hk⟩ :=
    (finite_euler_denominator_eq_zero_iff (hPrime p hpS) s).mp hzero
  have hre : s.re = 0 := by
    rw [hk, Complex.div_ofReal_re]
    simp
  linarith

end D5.S3.Zeros.EulerWindows
