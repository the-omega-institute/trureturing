/- GID: D5/S3/Analytic/Curvature/OffLineCurvatureDipoleTotalVariation
   generality: G
   mirror-B: D5/B/S3/Analytic/Curvature/OffLineCurvatureDipoleTotalVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The off-line curvature dipole has total variation four divided by its scale. -/

import D5.S3.Analytic.Adelic.OffLineCurvatureDipole

/-!
# Off-line curvature dipole total variation

The frozen off-line curvature theorem supplies the rational density together
with its integrability, zero total mass, exact boundary zeros, and sign
profile.  Integrating its elementary primitive over the negative core and
using zero mass for the positive wings determines the absolute integral.

Library-search audit trail (2026-09-02):

* Exact-name, absolute-integral-shape, and `4 / delta` searches found no D5
  theorem for this total variation identity.
* The frozen `off_line_curvature_dipole` theorem supplies every global and
  sign fact used here; this module does not re-prove those facts.
* Pinned Mathlib supplies `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
  `MeasureTheory.integral_add_compl`, `Integrable.abs`, and the set-integral
  congruence lemmas.  No pinned theorem states this dipole identity directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Curvature.OffLineCurvatureDipoleTotalVariation

open Filter MeasureTheory Set
open scoped Topology

/-- The positive-scale hypothesis is inhabited. -/
example : 0 < (1 : ℝ) := by norm_num

/-- The carrier of the dipole density is inhabited. -/
example : ℝ := 0

/--
For every positive scale and every center, the absolute integral of the
frozen off-line curvature dipole is exactly four divided by the scale.
-/
theorem off_line_curvature_dipole_total_variation
    (delta gamma : ℝ) (hdelta : 0 < delta) :
    let kappa := fun t : ℝ =>
      2 * (((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2)
    ∫ t : ℝ, |kappa t| = 4 / delta := by
  dsimp only
  let kappa := fun t : ℝ =>
    2 * (((t - gamma) ^ 2 - delta ^ 2) /
      ((t - gamma) ^ 2 + delta ^ 2) ^ 2)
  change (∫ t : ℝ, |kappa t|) = 4 / delta
  rcases
      D5.S3.Analytic.Adelic.OffLineCurvatureDipole.off_line_curvature_dipole
        delta gamma hdelta with
    ⟨hformula, _hcenter, hzeros, hcurvatureIntegrable, hcurvatureZero,
      hcurvatureNeg, hcurvaturePos⟩
  have hkappaIntegrable : Integrable kappa :=
    hcurvatureIntegrable.congr
      (ae_of_all _ fun t => hformula t)
  have hkappaZero : (∫ t : ℝ, kappa t) = 0 := by
    calc
      (∫ t : ℝ, kappa t) =
          ∫ t : ℝ, deriv
            (deriv (fun u : ℝ =>
              Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
                Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2)) 0 :=
        integral_congr_ae (ae_of_all _ fun t => (hformula t).symm)
      _ = 0 := hcurvatureZero
  have hkappaZeros (t : ℝ) :
      kappa t = 0 ↔ t = gamma - delta ∨ t = gamma + delta := by
    change
      2 * (((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2) = 0 ↔
          t = gamma - delta ∨ t = gamma + delta
    rw [← hformula t]
    exact hzeros t
  have hkappaNeg (t : ℝ) (ht : |t - gamma| < delta) : kappa t < 0 := by
    change 2 * (((t - gamma) ^ 2 - delta ^ 2) /
      ((t - gamma) ^ 2 + delta ^ 2) ^ 2) < 0
    rw [← hformula t]
    exact hcurvatureNeg t ht
  have hkappaPos (t : ℝ) (ht : delta < |t - gamma|) : 0 < kappa t := by
    change 0 < 2 * (((t - gamma) ^ 2 - delta ^ 2) /
      ((t - gamma) ^ 2 + delta ^ 2) ^ 2)
    rw [← hformula t]
    exact hcurvaturePos t ht
  let primitive := fun t : ℝ =>
    -2 * (t - gamma) / ((t - gamma) ^ 2 + delta ^ 2)
  have hderiv (t : ℝ) : HasDerivAt primitive (kappa t) t := by
    have hdenNe : (t - gamma) ^ 2 + delta ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (t - gamma), sq_pos_of_pos hdelta]
    have hnum : HasDerivAt (fun x : ℝ => -2 * (x - gamma)) (-2) t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).sub_const gamma).const_mul (-2)
    have hden :
        HasDerivAt (fun x : ℝ => (x - gamma) ^ 2 + delta ^ 2)
          (2 * (t - gamma)) t := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one] using
        (((hasDerivAt_id t).sub_const gamma).pow 2).add_const (delta ^ 2)
    dsimp only [primitive, kappa]
    have hraw := hnum.div hden hdenNe
    refine (hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    field_simp [hdenNe]
    ring
  have hle : gamma - delta ≤ gamma + delta := by linarith
  have hcoreInterval :
      (∫ t in gamma - delta..gamma + delta, kappa t) = -2 / delta := by
    calc
      (∫ t in gamma - delta..gamma + delta, kappa t) =
          primitive (gamma + delta) - primitive (gamma - delta) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hderiv t) hkappaIntegrable.intervalIntegrable
      _ = -2 / delta := by
        dsimp only [primitive]
        field_simp [hdelta.ne']
        ring
  let core : Set ℝ := Icc (gamma - delta) (gamma + delta)
  have hcoreIntegral : (∫ t in core, kappa t) = -2 / delta := by
    calc
      (∫ t in core, kappa t) =
          ∫ t in Ioc (gamma - delta) (gamma + delta), kappa t := by
        exact integral_Icc_eq_integral_Ioc
      _ = ∫ t in gamma - delta..gamma + delta, kappa t :=
        (intervalIntegral.integral_of_le hle).symm
      _ = -2 / delta := hcoreInterval
  have hkappaNonpos (t : ℝ) (ht : t ∈ core) : kappa t ≤ 0 := by
    have habs : |t - gamma| ≤ delta := by
      rw [abs_le]
      dsimp only [core] at ht
      constructor <;> linarith [ht.1, ht.2]
    rcases habs.lt_or_eq with habslt | habseq
    · exact (hkappaNeg t habslt).le
    · have hsquare : (t - gamma) ^ 2 = delta ^ 2 := by
        rw [← sq_abs, habseq]
      have htEndpoint :
          t = gamma - delta ∨ t = gamma + delta := by
        rcases eq_or_eq_neg_of_sq_eq_sq (t - gamma) delta hsquare with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      exact ((hkappaZeros t).2 htEndpoint).le
  have hkappaNonnegOffCore (t : ℝ) (ht : t ∈ coreᶜ) : 0 ≤ kappa t := by
    have habs : delta < |t - gamma| := by
      by_contra hnot
      have habsle : |t - gamma| ≤ delta := le_of_not_gt hnot
      have hbds := abs_le.mp habsle
      apply ht
      dsimp only [core]
      constructor <;> linarith [hbds.1, hbds.2]
    exact (hkappaPos t habs).le
  have habsCore :
      (∫ t in core, |kappa t|) = -(∫ t in core, kappa t) := by
    calc
      (∫ t in core, |kappa t|) = ∫ t in core, -kappa t := by
        apply setIntegral_congr_fun
        · exact measurableSet_Icc
        · intro t ht
          exact abs_of_nonpos (hkappaNonpos t ht)
      _ = -(∫ t in core, kappa t) :=
        integral_neg (f := kappa) (μ := volume.restrict core)
  have habsOffCore :
      (∫ t in coreᶜ, |kappa t|) = ∫ t in coreᶜ, kappa t := by
    apply setIntegral_congr_fun
    · exact measurableSet_Icc.compl
    · intro t ht
      exact abs_of_nonneg (hkappaNonnegOffCore t ht)
  have hsplit :
      (∫ t in core, kappa t) + (∫ t in coreᶜ, kappa t) = 0 := by
    calc
      (∫ t in core, kappa t) + (∫ t in coreᶜ, kappa t) =
          ∫ t : ℝ, kappa t :=
        integral_add_compl measurableSet_Icc hkappaIntegrable
      _ = 0 := hkappaZero
  rw [← integral_add_compl measurableSet_Icc hkappaIntegrable.abs,
    habsCore, habsOffCore, hcoreIntegral]
  rw [hcoreIntegral] at hsplit
  have hoffCore : (∫ t in coreᶜ, kappa t) = 2 / delta := by
    linear_combination hsplit
  rw [hoffCore]
  ring

#print axioms off_line_curvature_dipole_total_variation

end D5.S3.Analytic.Curvature.OffLineCurvatureDipoleTotalVariation
