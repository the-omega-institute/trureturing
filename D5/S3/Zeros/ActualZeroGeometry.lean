/- GID: D5/S3/Zeros/ActualZeroGeometry
   generality: I
   mirror-B: D5/B/S3/Zeros/ActualZeroGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual xi zeros connect standard RH to center coordinates and Cayley geometry. -/

import D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Zeros.Symmetry.CriticalCenterCoordinate
import D5.S3.Midline.CayleyCriticalLine

/-!
These dictionaries retain the actual entire xi reading, all complex arguments,
and Mathlib's exceptional-zero quantifiers. They do not prove RH.
The lower geometry imports no Li analytic consumer. Generality I follows the
frozen xi and critical-center owners. Utility none: these are general analytic
and geometric equivalences, not finite instances or numerical certificates.

The preregistered roots proof shape is bind-only, with no escape witness.
Admission basis: atom-required-bridge. The half-plane dictionary is consumed by
CanonicalLiGrowthZeroFree's bare disk converse and hence its summability-to-RH
theorem. The coordinate and Cayley dictionaries are the named companions for
CanonicalLiDiskEquivalence.actual_zero_geometry_disk_spec.
Repository and pinned-library searches found the exact zero correspondence,
RH forward lemma, right-half-strip reducer, inverse coordinate laws and Cayley
locus theorem; each is applied below. External searches are bounded, not complete.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.ActualZeroGeometry

open D5.S3.Zeros.CompletedZeta
open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
open D5.S3.Zeros.Symmetry.CriticalCenterCoordinate
open D5.S3.Midline.CayleyCriticalLine

/-- Standard RH expressed using the actual nontrivial-zero strip predicate. -/
theorem rh_iff_nontrivial_zeros_on_line :
    RiemannHypothesis ↔ ∀ rho : ℂ, Zeta23.IsNontrivialZero rho →
      rho.re = (1 : ℝ) / 2 := by
  refine ⟨fun hRH _ hzero => Zeta23.RH_implies_on_line hRH hzero, ?_⟩
  intro hline
  apply golden_right_half_strip_implies_rh
  intro rho hzero hhalf hone
  have h := hline rho ⟨hzero, by linarith, hone⟩
  linarith

/-- With the plus-I convention, every complex Xi zero is real exactly under RH. -/
theorem rh_iff_xi_central_zeros_real :
    RiemannHypothesis ↔ ∀ z : ℂ,
      xiReading ((1 / 2 : ℂ) + Complex.I * z) = 0 → z.im = 0 := by
  have coordinate (z : ℂ) : invCentralCoord z = (1 / 2 : ℂ) + Complex.I * z := by
    simp [invCentralCoord, D5.S3.Weil.Convention.criticalAbscissa]
  rw [rh_iff_nontrivial_zeros_on_line]
  constructor
  · intro hline z hzero
    have h : (invCentralCoord z).re = (1 : ℝ) / 2 :=
      hline _ ((xiReading_eq_zero_iff_nontrivial _).mp (by
        rw [coordinate]
        exact hzero))
    have hc := (critical_line_iff_central_coord_im_zero _).mp h
    simpa only [central_coord_inv_central_coord] using hc
  · intro hreal rho hzero
    apply (critical_line_iff_central_coord_im_zero rho).mpr
    apply hreal (centralCoord rho)
    rw [← coordinate]
    rw [inv_central_coord_central_coord]
    exact (xiReading_eq_zero_iff_nontrivial rho).mpr hzero

/-- Nonvanishing on the entire open right half-plane, including one, is RH. -/
theorem rh_iff_xi_right_half_plane :
    RiemannHypothesis ↔ ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0 := by
  constructor
  · intro hRH s hs hzero
    have hline := Zeta23.RH_implies_on_line hRH
      ((xiReading_eq_zero_iff_nontrivial s).mp hzero)
    linarith
  · intro hfree
    apply golden_right_half_strip_implies_rh
    intro s hzero hhalf hone
    exact hfree s hhalf ((xiReading_eq_zero_iff_nontrivial s).mpr
      ⟨hzero, by linarith, hone⟩)

/-- An actual strip zero is nonzero, so the source Cayley expression is valid. -/
theorem nontrivial_zero_cayley_eq (rho : ℂ) (hzero : Zeta23.IsNontrivialZero rho) :
    1 - 1 / rho = cayleyRatio rho := by
  have hne : rho ≠ 0 := by
    intro h
    have hpos := hzero.2.1
    simpa [h] using hpos
  unfold cayleyRatio
  field_simp [hne]

/-- Actual nontrivial zeros have unit source Cayley norm exactly under RH. -/
theorem rh_iff_nontrivial_zero_cayley_norm :
    RiemannHypothesis ↔ ∀ rho : ℂ, Zeta23.IsNontrivialZero rho →
      ‖1 - 1 / rho‖ = 1 := by
  rw [rh_iff_nontrivial_zeros_on_line]
  constructor
  · intro hline rho hzero
    rw [nontrivial_zero_cayley_eq rho hzero]
    exact (cayley_ratio_norm_one_iff_critical_line rho).mpr (hline rho hzero)
  · intro hunit rho hzero
    apply (cayley_ratio_norm_one_iff_critical_line rho).mp
    rw [← nontrivial_zero_cayley_eq rho hzero]
    exact hunit rho hzero

#print axioms rh_iff_nontrivial_zeros_on_line
#print axioms rh_iff_xi_central_zeros_real
#print axioms rh_iff_xi_right_half_plane
#print axioms nontrivial_zero_cayley_eq
#print axioms rh_iff_nontrivial_zero_cayley_norm

end D5.S3.Zeros.ActualZeroGeometry
