/- GID: D5/S3/Analytic/Boundary/GoldenDisplacementSeriesDifferentiability
   generality: I
   mirror-B: D5/B/S3/Analytic/Boundary/GoldenDisplacementSeriesDifferentiability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves differentiability of the golden displacement sum on its convergence region. -/

/- Library-search audit trail (2026-08-26):
   * Searches over D5/**/*.lean and Blueprint/**/* found no differentiability
     statement for the golden displacement sum. Before this node, 14 D5 Lean
     files mentioned `dTerm`; none contained any of the exact tokens
     `Differentiable`, `HasDerivAt`, `HasFDerivAt`, `fderiv`, or `deriv`.
   * Pinned Mathlib's global `differentiable_tsum` requires one summable
     derivative bound on the whole parameter plane. The local multivariable
     `hasFDerivAt_tsum_of_isPreconnected` applies after the proof constructs an
     open quadrant and a point-dependent summable derivative bound.
   * The proof invokes `Real.log_natCast_le_rpow_div` for the logarithm-to-power
     estimate below; pinned Mathlib derives that specialization from the general
     `Real.log_le_rpow_div`. The complex one-variable theorem
     `differentiableOn_tsum_of_summable_norm` does not apply to this real
     two-variable parameter space.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion
open GoldenDesubstitutionLength

namespace D5.S3.Analytic.Boundary.GoldenDisplacementSeriesDifferentiability

/-- The golden displacement sum is differentiable throughout its exact
convergence region. -/
theorem golden_displacement_series_differentiableOn :
    DifferentiableOn ℝ (fun p : ℝ × ℝ => ∑' n, dTerm p.1 p.2 n)
      {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
  intro p hp
  have hpConstraints :=
    (dTerm_summable_iff_two_constraints p.1 p.2).mp hp
  let delta : ℝ :=
    min ((2 * p.1 + p.2 - 1) / 12)
      ((3 * p.1 + 2 * p.2 - 1) / 20)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith [hpConstraints.1])
      (by linarith [hpConstraints.2])
  let corner : ℝ × ℝ := (p.1 - 2 * delta, p.2 - 2 * delta)
  have hcornerConstraints :
      1 < 2 * corner.1 + corner.2 ∧
        1 < 3 * corner.1 + 2 * corner.2 := by
    have hfirst : delta ≤ (2 * p.1 + p.2 - 1) / 12 :=
      min_le_left _ _
    have hsecond : delta ≤ (3 * p.1 + 2 * p.2 - 1) / 20 :=
      min_le_right _ _
    dsimp [corner]
    constructor <;> linarith
  have hcornerSummable : Summable (dTerm corner.1 corner.2) :=
    (dTerm_summable_iff_two_constraints corner.1 corner.2).mpr
      hcornerConstraints
  let midpoint : ℝ × ℝ := (p.1 - delta, p.2 - delta)
  let region : Set (ℝ × ℝ) :=
    Set.Ioi midpoint.1 ×ˢ Set.Ioi midpoint.2
  have hregionOpen : IsOpen region := isOpen_Ioi.prod isOpen_Ioi
  have hregionPreconnected : IsPreconnected region :=
    isPreconnected_Ioi.prod isPreconnected_Ioi
  have hpRegion : p ∈ region := by
    change midpoint.1 < p.1 ∧ midpoint.2 < p.2
    dsimp [midpoint]
    constructor <;> linarith [hdelta]
  let f : ℕ → ℝ × ℝ → ℝ := fun n q => dTerm q.1 q.2 n
  let f' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun n q =>
    if n = 0 then 0 else
      ((nS n : ℝ) ^ (-q.1)) •
          (((n : ℝ) ^ (-q.2) * Real.log n) •
            -(ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        ((n : ℝ) ^ (-q.2)) •
          (((nS n : ℝ) ^ (-q.1) * Real.log (nS n)) •
            -(ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hf : ∀ n q, q ∈ region → HasFDerivAt (f n) (f' n q) q := by
    intro n q _
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [f, f', dTerm_zero, ↓reduceIte]
      fun_prop
    · have hnPos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hnSPos : (0 : ℝ) < nS n := by
        exact_mod_cast Nat.pos_of_ne_zero
          (GoldenSubstitutionOrbit.nS_ne_zero n)
      simp only [f, f', hn, ↓reduceIte, dTerm]
      exact
        ((hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)
          (p := q)).neg.const_rpow hnSPos).mul
          ((hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)
            (p := q)).neg.const_rpow hnPos)
  let u : ℕ → ℝ := fun n =>
    (2 / delta) * dTerm corner.1 corner.2 n
  have huSummable : Summable u :=
    hcornerSummable.mul_left (2 / delta)
  have hfBound : ∀ n q, q ∈ region → ‖f' n q‖ ≤ u n := by
    intro n q hq
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f', u, dTerm_zero]
    · have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnSOne : (1 : ℝ) ≤ nS n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (GoldenSubstitutionOrbit.nS_ne_zero n)
      change midpoint.1 < q.1 ∧ midpoint.2 < q.2 at hq
      dsimp [midpoint] at hq
      have hqFirst : corner.1 + delta ≤ q.1 := by
        dsimp [corner]
        linarith [hq.1, hdelta]
      have hqSecond : corner.2 + delta ≤ q.2 := by
        dsimp [corner]
        linarith [hq.2, hdelta]
      have hfirstRpow :
          (nS n : ℝ) ^ (-q.1) ≤
            (nS n : ℝ) ^ (-(corner.1 + delta)) :=
        Real.rpow_le_rpow_of_exponent_le hnSOne (neg_le_neg hqFirst)
      have hsecondRpow :
          (n : ℝ) ^ (-q.2) ≤
            (n : ℝ) ^ (-(corner.2 + delta)) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (neg_le_neg hqSecond)
      have hfirstCorner :
          (nS n : ℝ) ^ (-q.1) ≤ (nS n : ℝ) ^ (-corner.1) :=
        hfirstRpow.trans <|
          Real.rpow_le_rpow_of_exponent_le hnSOne (by linarith)
      have hsecondCorner :
          (n : ℝ) ^ (-q.2) ≤ (n : ℝ) ^ (-corner.2) :=
        hsecondRpow.trans <|
          Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
      have hlogFirst :
          ‖Real.log (nS n)‖ ≤ (nS n : ℝ) ^ delta / delta := by
        rw [Real.norm_of_nonneg (Real.log_nonneg hnSOne)]
        exact Real.log_natCast_le_rpow_div (nS n) hdelta
      have hlogSecond :
          ‖Real.log n‖ ≤ (n : ℝ) ^ delta / delta := by
        rw [Real.norm_of_nonneg (Real.log_nonneg hnOne)]
        exact Real.log_natCast_le_rpow_div n hdelta
      have hfirstCoefficient :
          (nS n : ℝ) ^ (-q.1) * (n : ℝ) ^ (-q.2) *
              ‖Real.log (nS n)‖ ≤
            dTerm corner.1 corner.2 n / delta := by
        calc
          _ ≤ (nS n : ℝ) ^ (-(corner.1 + delta)) *
                (n : ℝ) ^ (-corner.2) *
                  ((nS n : ℝ) ^ delta / delta) := by
              gcongr
          _ = dTerm corner.1 corner.2 n / delta := by
              unfold dTerm
              rw [if_neg hn, div_eq_mul_inv, div_eq_mul_inv]
              have hrpow :
                  (nS n : ℝ) ^ (-(corner.1 + delta)) *
                      (nS n : ℝ) ^ delta =
                    (nS n : ℝ) ^ (-corner.1) := by
                rw [← Real.rpow_add (by positivity)]
                congr 1
                ring
              rw [show
                (nS n : ℝ) ^ (-(corner.1 + delta)) *
                      (n : ℝ) ^ (-corner.2) *
                        ((nS n : ℝ) ^ delta * delta⁻¹) =
                    ((nS n : ℝ) ^ (-(corner.1 + delta)) *
                        (nS n : ℝ) ^ delta) *
                      (n : ℝ) ^ (-corner.2) * delta⁻¹ by
                ring, hrpow]
      have hsecondCoefficient :
          (nS n : ℝ) ^ (-q.1) * (n : ℝ) ^ (-q.2) *
              ‖Real.log n‖ ≤
            dTerm corner.1 corner.2 n / delta := by
        calc
          _ ≤ (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-(corner.2 + delta)) *
                  ((n : ℝ) ^ delta / delta) := by
              gcongr
          _ = dTerm corner.1 corner.2 n / delta := by
              unfold dTerm
              rw [if_neg hn, div_eq_mul_inv, div_eq_mul_inv]
              have hrpow :
                  (n : ℝ) ^ (-(corner.2 + delta)) *
                      (n : ℝ) ^ delta =
                    (n : ℝ) ^ (-corner.2) := by
                rw [← Real.rpow_add (by positivity)]
                congr 1
                ring
              rw [show
                (nS n : ℝ) ^ (-corner.1) *
                      (n : ℝ) ^ (-(corner.2 + delta)) *
                        ((n : ℝ) ^ delta * delta⁻¹) =
                    (nS n : ℝ) ^ (-corner.1) *
                      ((n : ℝ) ^ (-(corner.2 + delta)) *
                        (n : ℝ) ^ delta) * delta⁻¹ by
                ring, hrpow]
      have hfirstMap :
          ‖((n : ℝ) ^ (-q.2)) •
              (((nS n : ℝ) ^ (-q.1) * Real.log (nS n)) •
                -(ContinuousLinearMap.fst ℝ ℝ ℝ))‖ ≤
            (nS n : ℝ) ^ (-q.1) * (n : ℝ) ^ (-q.2) *
              ‖Real.log (nS n)‖ := by
        rw [norm_smul, norm_smul, norm_neg, norm_mul]
        rw [Real.norm_of_nonneg (by positivity)]
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          (n : ℝ) ^ (-q.2) *
                ((nS n : ℝ) ^ (-q.1) * ‖Real.log (nS n)‖ *
                  ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖) ≤
              (n : ℝ) ^ (-q.2) *
                ((nS n : ℝ) ^ (-q.1) * ‖Real.log (nS n)‖ * 1) := by
            gcongr
            exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
          _ = _ := by ring
      have hsecondMap :
          ‖((nS n : ℝ) ^ (-q.1)) •
              (((n : ℝ) ^ (-q.2) * Real.log n) •
                -(ContinuousLinearMap.snd ℝ ℝ ℝ))‖ ≤
            (nS n : ℝ) ^ (-q.1) * (n : ℝ) ^ (-q.2) *
              ‖Real.log n‖ := by
        rw [norm_smul, norm_smul, norm_neg, norm_mul]
        rw [Real.norm_of_nonneg (by positivity)]
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          (nS n : ℝ) ^ (-q.1) *
                ((n : ℝ) ^ (-q.2) * ‖Real.log n‖ *
                  ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖) ≤
              (nS n : ℝ) ^ (-q.1) *
                ((n : ℝ) ^ (-q.2) * ‖Real.log n‖ * 1) := by
            gcongr
            exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
          _ = _ := by ring
      simp only [f', hn, ↓reduceIte, u]
      calc
        _ ≤ ‖((nS n : ℝ) ^ (-q.1)) •
                (((n : ℝ) ^ (-q.2) * Real.log n) •
                  -(ContinuousLinearMap.snd ℝ ℝ ℝ))‖ +
              ‖((n : ℝ) ^ (-q.2)) •
                (((nS n : ℝ) ^ (-q.1) * Real.log (nS n)) •
                  -(ContinuousLinearMap.fst ℝ ℝ ℝ))‖ :=
          norm_add_le _ _
        _ ≤ dTerm corner.1 corner.2 n / delta +
              dTerm corner.1 corner.2 n / delta :=
          add_le_add (hsecondMap.trans hsecondCoefficient)
            (hfirstMap.trans hfirstCoefficient)
        _ = (2 / delta) * dTerm corner.1 corner.2 n := by
          ring
  have hsumDeriv :=
    hasFDerivAt_tsum_of_isPreconnected huSummable hregionOpen
      hregionPreconnected hf hfBound hpRegion hp hpRegion
  exact hsumDeriv.differentiableAt.differentiableWithinAt

end D5.S3.Analytic.Boundary.GoldenDisplacementSeriesDifferentiability
