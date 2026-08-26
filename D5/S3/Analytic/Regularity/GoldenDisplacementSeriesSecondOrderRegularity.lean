/- GID: D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSecondOrderRegularity
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenDisplacementSeriesSecondOrderRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Second-order regularity of the golden displacement sum on its region. -/

/- Library-search audit trail (2026-08-26):
   * Searches over D5/**/*.lean and Blueprint/** found no higher-regularity
     statement for the golden displacement sum.
   * Pinned Mathlib's `contDiff_tsum`, `contDiff_tsum_of_eventually`,
     `iteratedFDeriv_tsum`, and `iteratedFDeriv_tsum_apply` require bounds on
     the whole parameter space. The only `contDiffOn_tsum` token found in all
     pinned Mathlib Lean files was the specialized `contDiffOn_tsum_cexp`.
   * `Real.isLittleO_log_rpow_rpow_atTop` is the named all-order asymptotic
     estimate found for powers of logarithms. No direct pointwise theorem of
     the form `log(x)^k <= C*x^epsilon` was found. This finite-order proof uses
     `Real.log_natCast_le_rpow_div` twice instead.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion
open GoldenDesubstitutionLength

namespace D5.S3.Analytic.Regularity.GoldenDisplacementSeriesSecondOrderRegularity

/-- The golden displacement sum is twice continuously differentiable
throughout its exact convergence region. -/
theorem golden_displacement_series_contDiffOn_two :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∑' n, dTerm p.1 p.2 n)
      {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
  intro p hp
  have hpConstraints :=
    (dTerm_summable_iff_two_constraints p.1 p.2).mp hp
  let delta : ℝ :=
    min ((2 * p.1 + p.2 - 1) / 18)
      ((3 * p.1 + 2 * p.2 - 1) / 30)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith [hpConstraints.1])
      (by linarith [hpConstraints.2])
  let corner : ℝ × ℝ := (p.1 - 3 * delta, p.2 - 3 * delta)
  have hcornerConstraints :
      1 < 2 * corner.1 + corner.2 ∧
        1 < 3 * corner.1 + 2 * corner.2 := by
    have hfirst : delta ≤ (2 * p.1 + p.2 - 1) / 18 :=
      min_le_left _ _
    have hsecond : delta ≤ (3 * p.1 + 2 * p.2 - 1) / 30 :=
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
  let ell : ℕ → (ℝ × ℝ →L[ℝ] ℝ) := fun n =>
    (Real.log (nS n) • -(ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      (Real.log n • -(ContinuousLinearMap.snd ℝ ℝ ℝ))
  let f : ℕ → ℝ × ℝ → ℝ := fun n q =>
    if n = 0 then 0 else Real.exp (ell n q)
  let f' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun n q =>
    if n = 0 then 0 else Real.exp (ell n q) • ell n
  let f'' : ℕ → ℝ × ℝ →
      (ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ)) := fun n q =>
    if n = 0 then 0 else
      (Real.exp (ell n q) • ell n).smulRight (ell n)
  have hfEq : ∀ n q, f n q = dTerm q.1 q.2 n := by
    intro n q
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f, dTerm_zero]
    · have hnPos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hnSPos : (0 : ℝ) < nS n := by
        exact_mod_cast Nat.pos_of_ne_zero
          (GoldenSubstitutionOrbit.nS_ne_zero n)
      simp only [f, hn, ↓reduceIte, dTerm, ell]
      rw [Real.rpow_def_of_pos hnSPos, Real.rpow_def_of_pos hnPos]
      rw [← Real.exp_add]
      congr 1
  have hf : ∀ n q, HasFDerivAt (f n) (f' n q) q := by
    intro n q
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [f, f', ↓reduceIte]
      fun_prop
    · simp only [f, f', hn, ↓reduceIte]
      exact (ell n).hasFDerivAt.exp
  have hf' : ∀ n q, HasFDerivAt (f' n) (f'' n q) q := by
    intro n q
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [f', f'', ↓reduceIte]
      fun_prop
    · simp only [f', f'', hn, ↓reduceIte]
      exact ((ell n).hasFDerivAt.exp.smul_const (ell n))
  let u1 : ℕ → ℝ := fun n =>
    (2 / delta) * dTerm corner.1 corner.2 n
  have hu1Summable : Summable u1 :=
    hcornerSummable.mul_left (2 / delta)
  have hf'Bound : ∀ n q, q ∈ region → ‖f' n q‖ ≤ u1 n := by
    intro n q hq
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f', u1, dTerm_zero]
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
          dTerm q.1 q.2 n * ‖Real.log (nS n)‖ ≤
            dTerm corner.1 corner.2 n / delta := by
        unfold dTerm
        rw [if_neg hn, if_neg hn]
        calc
          _ ≤ (nS n : ℝ) ^ (-(corner.1 + delta)) *
                (n : ℝ) ^ (-corner.2) *
                  ((nS n : ℝ) ^ delta / delta) := by
              gcongr
          _ = (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-corner.2) / delta := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              rw [show
                (nS n : ℝ) ^ (-(corner.1 + delta)) *
                      (n : ℝ) ^ (-corner.2) *
                        ((nS n : ℝ) ^ delta * delta⁻¹) =
                    ((nS n : ℝ) ^ (-(corner.1 + delta)) *
                        (nS n : ℝ) ^ delta) *
                      (n : ℝ) ^ (-corner.2) * delta⁻¹ by ring]
              rw [← Real.rpow_add (by positivity)]
              congr 2
              ring
      have hsecondCoefficient :
          dTerm q.1 q.2 n * ‖Real.log n‖ ≤
            dTerm corner.1 corner.2 n / delta := by
        unfold dTerm
        rw [if_neg hn, if_neg hn]
        calc
          _ ≤ (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-(corner.2 + delta)) *
                  ((n : ℝ) ^ delta / delta) := by
              gcongr
          _ = (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-corner.2) / delta := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              rw [show
                (nS n : ℝ) ^ (-corner.1) *
                      (n : ℝ) ^ (-(corner.2 + delta)) *
                        ((n : ℝ) ^ delta * delta⁻¹) =
                    (nS n : ℝ) ^ (-corner.1) *
                      ((n : ℝ) ^ (-(corner.2 + delta)) *
                        (n : ℝ) ^ delta) * delta⁻¹ by ring]
              rw [← Real.rpow_add (by positivity)]
              congr 2
              ring
      have hellNorm :
          ‖ell n‖ ≤ ‖Real.log (nS n)‖ + ‖Real.log n‖ := by
        dsimp [ell]
        calc
          _ ≤ ‖Real.log (nS n) •
                -(ContinuousLinearMap.fst ℝ ℝ ℝ)‖ +
              ‖Real.log n •
                -(ContinuousLinearMap.snd ℝ ℝ ℝ)‖ := norm_add_le _ _
          _ ≤ ‖Real.log (nS n)‖ * 1 + ‖Real.log n‖ * 1 := by
            rw [norm_smul, norm_neg, norm_smul, norm_neg]
            gcongr
            · exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
            · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
          _ = _ := by simp only [Real.norm_eq_abs, mul_one]
      have hexp : Real.exp (ell n q) = dTerm q.1 q.2 n := by
        simpa only [f, hn, ↓reduceIte] using hfEq n q
      simp only [f', hn, ↓reduceIte, u1]
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, hexp]
      calc
        dTerm q.1 q.2 n * ‖ell n‖ ≤
            dTerm q.1 q.2 n *
              (‖Real.log (nS n)‖ + ‖Real.log n‖) := by
          gcongr
          exact dTerm_nonneg q.1 q.2 n
        _ = dTerm q.1 q.2 n * ‖Real.log (nS n)‖ +
              dTerm q.1 q.2 n * ‖Real.log n‖ := by ring
        _ ≤ dTerm corner.1 corner.2 n / delta +
              dTerm corner.1 corner.2 n / delta :=
          add_le_add hfirstCoefficient hsecondCoefficient
        _ = (2 / delta) * dTerm corner.1 corner.2 n := by ring
  let u2 : ℕ → ℝ := fun n =>
    (4 / delta ^ 2) * dTerm corner.1 corner.2 n
  have hu2Summable : Summable u2 :=
    hcornerSummable.mul_left (4 / delta ^ 2)
  have hf''Bound : ∀ n q, q ∈ region → ‖f'' n q‖ ≤ u2 n := by
    intro n q hq
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [f'', u2, dTerm_zero, ↓reduceIte, mul_zero]
      change ‖(0 : ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ))‖ ≤ 0
      exact ((norm_eq_zero (a := (0 : ℝ × ℝ →L[ℝ]
        (ℝ × ℝ →L[ℝ] ℝ)))).mpr rfl).le
    · have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnSOne : (1 : ℝ) ≤ nS n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (GoldenSubstitutionOrbit.nS_ne_zero n)
      change midpoint.1 < q.1 ∧ midpoint.2 < q.2 at hq
      dsimp [midpoint] at hq
      have hqFirst : corner.1 + 2 * delta ≤ q.1 := by
        dsimp [corner]
        linarith [hq.1, hdelta]
      have hqSecond : corner.2 + 2 * delta ≤ q.2 := by
        dsimp [corner]
        linarith [hq.2, hdelta]
      have hfirstRpow :
          (nS n : ℝ) ^ (-q.1) ≤
            (nS n : ℝ) ^ (-(corner.1 + 2 * delta)) :=
        Real.rpow_le_rpow_of_exponent_le hnSOne (neg_le_neg hqFirst)
      have hsecondRpow :
          (n : ℝ) ^ (-q.2) ≤
            (n : ℝ) ^ (-(corner.2 + 2 * delta)) :=
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
      have hfirstSqCoefficient :
          dTerm q.1 q.2 n * ‖Real.log (nS n)‖ ^ 2 ≤
            dTerm corner.1 corner.2 n / delta ^ 2 := by
        unfold dTerm
        rw [if_neg hn, if_neg hn]
        calc
          _ ≤ (nS n : ℝ) ^ (-(corner.1 + 2 * delta)) *
                (n : ℝ) ^ (-corner.2) *
                  ((nS n : ℝ) ^ delta / delta) ^ 2 := by
              gcongr
          _ = (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-corner.2) / delta ^ 2 := by
              have hrpow :
                  (nS n : ℝ) ^ (-(corner.1 + 2 * delta)) *
                      ((nS n : ℝ) ^ delta) ^ 2 =
                    (nS n : ℝ) ^ (-corner.1) := by
                rw [pow_two, ← Real.rpow_add (by positivity),
                  ← Real.rpow_add (by positivity)]
                congr 1
                ring
              rw [div_pow, div_eq_mul_inv]
              rw [show
                (nS n : ℝ) ^ (-(corner.1 + 2 * delta)) *
                      (n : ℝ) ^ (-corner.2) *
                        (((nS n : ℝ) ^ delta) ^ 2 *
                          (delta ^ 2)⁻¹) =
                    ((nS n : ℝ) ^ (-(corner.1 + 2 * delta)) *
                        ((nS n : ℝ) ^ delta) ^ 2) *
                      (n : ℝ) ^ (-corner.2) *
                        (delta ^ 2)⁻¹ by ring, hrpow, div_eq_mul_inv]
      have hsecondSqCoefficient :
          dTerm q.1 q.2 n * ‖Real.log n‖ ^ 2 ≤
            dTerm corner.1 corner.2 n / delta ^ 2 := by
        unfold dTerm
        rw [if_neg hn, if_neg hn]
        calc
          _ ≤ (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-(corner.2 + 2 * delta)) *
                  ((n : ℝ) ^ delta / delta) ^ 2 := by
              gcongr
          _ = (nS n : ℝ) ^ (-corner.1) *
                (n : ℝ) ^ (-corner.2) / delta ^ 2 := by
              have hrpow :
                  (n : ℝ) ^ (-(corner.2 + 2 * delta)) *
                      ((n : ℝ) ^ delta) ^ 2 =
                    (n : ℝ) ^ (-corner.2) := by
                rw [pow_two, ← Real.rpow_add (by positivity),
                  ← Real.rpow_add (by positivity)]
                congr 1
                ring
              rw [div_pow, div_eq_mul_inv]
              rw [show
                (nS n : ℝ) ^ (-corner.1) *
                      (n : ℝ) ^ (-(corner.2 + 2 * delta)) *
                        (((n : ℝ) ^ delta) ^ 2 * (delta ^ 2)⁻¹) =
                    (nS n : ℝ) ^ (-corner.1) *
                      ((n : ℝ) ^ (-(corner.2 + 2 * delta)) *
                        ((n : ℝ) ^ delta) ^ 2) *
                          (delta ^ 2)⁻¹ by ring, hrpow, div_eq_mul_inv]
      have hellNorm :
          ‖ell n‖ ≤ ‖Real.log (nS n)‖ + ‖Real.log n‖ := by
        dsimp [ell]
        calc
          _ ≤ ‖Real.log (nS n) •
                -(ContinuousLinearMap.fst ℝ ℝ ℝ)‖ +
              ‖Real.log n •
                -(ContinuousLinearMap.snd ℝ ℝ ℝ)‖ := norm_add_le _ _
          _ ≤ ‖Real.log (nS n)‖ * 1 + ‖Real.log n‖ * 1 := by
            rw [norm_smul, norm_neg, norm_smul, norm_neg]
            gcongr
            · exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
            · exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
          _ = _ := by simp only [Real.norm_eq_abs, mul_one]
      have hexp : Real.exp (ell n q) = dTerm q.1 q.2 n := by
        simpa only [f, hn, ↓reduceIte] using hfEq n q
      simp only [f'', hn, ↓reduceIte, u2]
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos _).le, hexp]
      calc
        dTerm q.1 q.2 n * ‖ell n‖ * ‖ell n‖ =
            dTerm q.1 q.2 n * ‖ell n‖ ^ 2 := by ring
        _ ≤ dTerm q.1 q.2 n *
              (‖Real.log (nS n)‖ + ‖Real.log n‖) ^ 2 := by
          gcongr
          · exact dTerm_nonneg q.1 q.2 n
        _ ≤ dTerm q.1 q.2 n *
              (2 * ‖Real.log (nS n)‖ ^ 2 +
                2 * ‖Real.log n‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (dTerm_nonneg q.1 q.2 n)
          nlinarith [sq_nonneg
              (‖Real.log (nS n)‖ - ‖Real.log n‖)]
        _ = 2 * (dTerm q.1 q.2 n * ‖Real.log (nS n)‖ ^ 2) +
              2 * (dTerm q.1 q.2 n * ‖Real.log n‖ ^ 2) := by ring
        _ ≤ 2 * (dTerm corner.1 corner.2 n / delta ^ 2) +
              2 * (dTerm corner.1 corner.2 n / delta ^ 2) := by
          gcongr
        _ = (4 / delta ^ 2) * dTerm corner.1 corner.2 n := by ring
  have hf''Continuous : ∀ n, Continuous (f'' n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [f'', ↓reduceIte]
      fun_prop
    · simp only [f'', hn, ↓reduceIte]
      change Continuous (fun q =>
        ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ)
          (ℝ × ℝ →L[ℝ] ℝ) (Real.exp (ell n q) • ell n) (ell n))
      fun_prop
  let sumF : ℝ × ℝ → ℝ := fun q => ∑' n, f n q
  let sumF' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun q =>
    ∑' n, f' n q
  let sumF'' : ℝ × ℝ →
      (ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ)) := fun q =>
    ∑' n, f'' n q
  have hfPSummable : Summable (fun n => f n p) := by
    exact hp.congr fun n => (hfEq n p).symm
  have hf'PSummable : Summable (fun n => f' n p) :=
    Summable.of_norm_bounded hu1Summable fun n =>
      hf'Bound n p hpRegion
  have hsumFDeriv : ∀ q, q ∈ region →
      HasFDerivAt sumF (sumF' q) q := by
    intro q hq
    exact hasFDerivAt_tsum_of_isPreconnected hu1Summable
      hregionOpen hregionPreconnected
      (fun n y _ => hf n y) hf'Bound hpRegion hfPSummable hq
  have hsumF'Deriv : ∀ q, q ∈ region →
      HasFDerivAt sumF' (sumF'' q) q := by
    intro q hq
    exact hasFDerivAt_tsum_of_isPreconnected hu2Summable
      hregionOpen hregionPreconnected
      (fun n y _ => hf' n y) hf''Bound hpRegion hf'PSummable hq
  have hsumF''ContinuousOn : ContinuousOn sumF'' region := by
    exact continuousOn_tsum (f := f'') (s := region)
      (fun n => (hf''Continuous n).continuousOn) hu2Summable hf''Bound
  have hsumF'ContDiffAt : ContDiffAt ℝ 1 sumF' p := by
    apply contDiffAt_one_iff.mpr
    exact ⟨sumF'', region, hregionOpen.mem_nhds hpRegion,
      hsumF''ContinuousOn, hsumF'Deriv⟩
  have hsumFContDiffAt : ContDiffAt ℝ 2 sumF p := by
    change ContDiffAt ℝ ((1 : ℕ) + 1) sumF p
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    exact ⟨sumF', ⟨region, hregionOpen.mem_nhds hpRegion, hsumFDeriv⟩,
      hsumF'ContDiffAt⟩
  simp only [sumF] at hsumFContDiffAt
  simp_rw [hfEq] at hsumFContDiffAt
  exact hsumFContDiffAt.contDiffWithinAt

end D5.S3.Analytic.Regularity.GoldenDisplacementSeriesSecondOrderRegularity
