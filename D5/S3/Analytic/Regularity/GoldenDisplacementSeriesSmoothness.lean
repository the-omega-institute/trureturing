/- GID: D5/S3/Analytic/Regularity/GoldenDisplacementSeriesSmoothness
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenDisplacementSeriesSmoothness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Smoothness of the golden displacement sum on its exact convergence region. -/

/- Library-search audit trail (2026-08-27):
   * Searches over D5/**/*.lean and Blueprint/** found no smoothness theorem for
     the golden displacement sum beyond the existing order-two result.
   * Across all pinned Mathlib Lean files, `iteratedFDerivWithin_tsum` has no
     declaration. The one `iteratedDerivWithin_tsum` declaration is restricted
     to a one-variable domain, and the one `contDiffOn_tsum`-named declaration
     is the concrete upper-half-plane exponential series theorem.
   * `contDiff_tsum` and `iteratedFDeriv_tsum` are global. This proof instead
     localizes their induction with `hasFDerivAt_tsum_of_isPreconnected`.
   * The real logarithm estimate used below is
     `Real.log_natCast_le_rpow_div`. Pinned Mathlib has a norm variant only for
     `Complex.log`; the private real wrapper records the needed positivity step.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion
open GoldenDesubstitutionLength
open scoped ContDiff

namespace D5.S3.Analytic.Regularity.GoldenDisplacementSeriesSmoothness

private theorem local_contDiffOn_tsum
    {α E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : α → E → F} {v : ℕ → α → ℝ} {s : Set E} {x0 : E} (N : ℕ)
    (hs : IsOpen s) (hsc : IsPreconnected s) (hx0 : x0 ∈ s)
    (hf0 : Summable (fun i => f i x0))
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hv : ∀ k, k ≤ N → Summable (v k))
    (hbound : ∀ k i x, k ≤ N → x ∈ s →
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ContDiffOn ℝ N (fun x => ∑' i, f i x) s := by
  induction N generalizing F f v x0 with
  | zero =>
      change ContDiffOn ℝ 0 (fun x => ∑' i, f i x) s
      rw [contDiffOn_zero]
      exact continuousOn_tsum
        (fun i => (hf i).continuous.continuousOn) (hv 0 le_rfl)
        (fun i x hx => by
          simpa only [norm_iteratedFDeriv_zero] using hbound 0 i x le_rfl hx)
  | succ N ih =>
      change ContDiffOn ℝ ((N : ℕ∞) + 1) (fun x => ∑' i, f i x) s
      apply (contDiffOn_succ_iff_fderiv_of_isOpen hs).2
      let f' : α → E → (E →L[ℝ] F) := fun i x => fderiv ℝ (f i) x
      have hf'Deriv : ∀ i x, HasFDerivAt (f i) (f' i x) x := by
        intro i x
        exact (hf i).differentiable (by simp) x |>.hasFDerivAt
      have hf'Bound : ∀ i x, x ∈ s → ‖f' i x‖ ≤ v 1 i := by
        intro i x hx
        rw [← norm_iteratedFDeriv_one (f i)]
        exact hbound 1 i x (Nat.succ_le_succ (Nat.zero_le N)) hx
      have hf'0 : Summable (fun i => f' i x0) :=
        Summable.of_norm_bounded (hv 1 (Nat.succ_le_succ (Nat.zero_le N)))
          (fun i => hf'Bound i x0 hx0)
      have hsumDeriv : ∀ x, x ∈ s →
          HasFDerivAt (fun y => ∑' i, f i y) (∑' i, f' i x) x := by
        intro x hx
        exact hasFDerivAt_tsum_of_isPreconnected
          (hv 1 (Nat.succ_le_succ (Nat.zero_le N))) hs hsc
          (fun i y _ => hf'Deriv i y) hf'Bound hx0 hf0 hx
      refine ⟨fun x hx => (hsumDeriv x hx).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      have hrec : ContDiffOn ℝ N (fun x => ∑' i, f' i x) s := by
        apply ih (f := f') (v := fun k => v (k + 1)) (x0 := x0) hx0 hf'0
        · intro i
          exact (hf i).fderiv_right (by simp)
        · intro k hk
          exact hv (k + 1) (Nat.succ_le_succ hk)
        · intro k i x hk hx
          rw [norm_iteratedFDeriv_fderiv]
          exact hbound (k + 1) i x (Nat.succ_le_succ hk) hx
      exact hrec.congr fun x hx => (hsumDeriv x hx).fderiv

private lemma norm_log_natCast_pow_le_rpow (n k : ℕ) (hn : 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) :
    ‖Real.log n‖ ^ k ≤ ((n : ℝ) ^ ε / ε) ^ k := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ k
  rw [Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]
  exact Real.log_natCast_le_rpow_div n hε

/-- The golden displacement sum is smooth throughout its exact convergence region. -/
theorem golden_displacement_series_contDiffOn_infty :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => ∑' n, dTerm p.1 p.2 n)
      {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
  rw [contDiffOn_infty]
  intro order p hp
  have hpConstraints :=
    (dTerm_summable_iff_two_constraints p.1 p.2).mp hp
  let scale : ℝ := order + 1
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  let delta : ℝ :=
    min ((2 * p.1 + p.2 - 1) / (6 * scale))
      ((3 * p.1 + 2 * p.2 - 1) / (10 * scale))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (div_pos (by linarith [hpConstraints.1]) (by positivity))
      (div_pos (by linarith [hpConstraints.2]) (by positivity))
  let corner : ℝ × ℝ :=
    (p.1 - scale * delta, p.2 - scale * delta)
  have hcornerConstraints :
      1 < 2 * corner.1 + corner.2 ∧
        1 < 3 * corner.1 + 2 * corner.2 := by
    have hfirst := min_le_left
      ((2 * p.1 + p.2 - 1) / (6 * scale))
      ((3 * p.1 + 2 * p.2 - 1) / (10 * scale))
    have hsecond := min_le_right
      ((2 * p.1 + p.2 - 1) / (6 * scale))
      ((3 * p.1 + 2 * p.2 - 1) / (10 * scale))
    have hfirst' : 6 * scale * delta ≤ 2 * p.1 + p.2 - 1 := by
      rw [show 6 * scale * delta = delta * (6 * scale) by ring]
      exact (le_div_iff₀ (by positivity)).mp hfirst
    have hsecond' : 10 * scale * delta ≤ 3 * p.1 + 2 * p.2 - 1 := by
      rw [show 10 * scale * delta = delta * (10 * scale) by ring]
      exact (le_div_iff₀ (by positivity)).mp hsecond
    dsimp [corner]
    constructor <;> nlinarith
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
  have hfSmooth : ∀ n, ContDiff ℝ ∞ (f n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [f, ↓reduceIte]
      fun_prop
    · simp only [f, hn, ↓reduceIte]
      fun_prop
  let v : ℕ → ℕ → ℝ := fun j n =>
    (2 / delta) ^ j * dTerm corner.1 corner.2 n
  have hvSummable : ∀ j, j ≤ order → Summable (v j) := by
    intro j _
    exact hcornerSummable.mul_left ((2 / delta) ^ j)
  have hbound : ∀ j n q, j ≤ order → q ∈ region →
      ‖iteratedFDeriv ℝ j (f n) q‖ ≤ v j n := by
    intro j n q hj hq
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f, v, dTerm_zero]
    · have hnOne : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnSOne : (1 : ℝ) ≤ nS n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (GoldenSubstitutionOrbit.nS_ne_zero n)
      have hjReal : (j : ℝ) ≤ order := by exact_mod_cast hj
      have hjGap : 0 ≤ ((order : ℝ) - j) * delta :=
        mul_nonneg (sub_nonneg.mpr hjReal) hdelta.le
      change midpoint.1 < q.1 ∧ midpoint.2 < q.2 at hq
      dsimp [midpoint] at hq
      have hqFirst : corner.1 + j * delta ≤ q.1 := by
        dsimp [corner, scale]
        nlinarith [hq.1, hjGap]
      have hqSecond : corner.2 + j * delta ≤ q.2 := by
        dsimp [corner, scale]
        nlinarith [hq.2, hjGap]
      have hfirstRpow :
          (nS n : ℝ) ^ (-q.1) ≤
            (nS n : ℝ) ^ (-(corner.1 + j * delta)) :=
        Real.rpow_le_rpow_of_exponent_le hnSOne (neg_le_neg hqFirst)
      have hsecondRpow :
          (n : ℝ) ^ (-q.2) ≤
            (n : ℝ) ^ (-(corner.2 + j * delta)) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (neg_le_neg hqSecond)
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
      have hlogFirst :
          ‖Real.log (nS n)‖ ≤ (nS n : ℝ) ^ delta / delta := by
        simpa only [pow_one] using
          norm_log_natCast_pow_le_rpow (nS n) 1
            (Nat.one_le_iff_ne_zero.mpr (GoldenSubstitutionOrbit.nS_ne_zero n)) hdelta
      have hlogSecond :
          ‖Real.log n‖ ≤ (n : ℝ) ^ delta / delta := by
        simpa only [pow_one] using
          norm_log_natCast_pow_le_rpow n 1
            (Nat.one_le_iff_ne_zero.mpr hn) hdelta
      have hfirstPowerOne : 1 ≤ (nS n : ℝ) ^ delta :=
        Real.one_le_rpow hnSOne hdelta.le
      have hsecondPowerOne : 1 ≤ (n : ℝ) ^ delta :=
        Real.one_le_rpow hnOne hdelta.le
      have hlogSum :
          ‖Real.log (nS n)‖ + ‖Real.log n‖ ≤
            2 * (((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) / delta) := by
        have hfirstProduct :
            (nS n : ℝ) ^ delta / delta ≤
              ((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) / delta := by
          gcongr
          exact le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _)
            hsecondPowerOne
        have hsecondProduct :
            (n : ℝ) ^ delta / delta ≤
              ((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) / delta := by
          gcongr
          exact le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _)
            hfirstPowerOne
        linarith
      have hellPow :
          ‖ell n‖ ^ j ≤
            (2 * (((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) / delta)) ^ j :=
        pow_le_pow_left₀ (norm_nonneg _) (hellNorm.trans hlogSum) j
      have hfirstCancel :
          (nS n : ℝ) ^ (-(corner.1 + j * delta)) *
              ((nS n : ℝ) ^ delta) ^ j =
            (nS n : ℝ) ^ (-corner.1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_add (by positivity)]
        congr 1
        ring
      have hsecondCancel :
          (n : ℝ) ^ (-(corner.2 + j * delta)) *
              ((n : ℝ) ^ delta) ^ j =
            (n : ℝ) ^ (-corner.2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_add (by positivity)]
        congr 1
        ring
      have hexp : Real.exp (ell n q) = dTerm q.1 q.2 n := by
        simpa only [f, hn, ↓reduceIte] using hfEq n q
      have hiterated :
          iteratedFDeriv ℝ j (f n) q =
            (iteratedFDeriv ℝ j Real.exp (ell n q)).compContinuousLinearMap
              (fun _ => ell n) := by
        simp only [f, hn, ↓reduceIte]
        exact (ell n).iteratedFDeriv_comp_right
          (Real.contDiff_exp (n := ∞)) q (by
            exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
      rw [hiterated]
      calc
        _ ≤ ‖iteratedFDeriv ℝ j Real.exp (ell n q)‖ *
              ∏ _ : Fin j, ‖ell n‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = dTerm q.1 q.2 n * ‖ell n‖ ^ j := by
          rw [Fin.prod_const, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
            iteratedDeriv_eq_iterate, Real.iter_deriv_exp, hexp,
            Real.norm_of_nonneg (dTerm_nonneg q.1 q.2 n)]
        _ ≤ dTerm q.1 q.2 n *
              (2 * (((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) / delta)) ^ j := by
          gcongr
          exact dTerm_nonneg q.1 q.2 n
        _ ≤ (2 / delta) ^ j * dTerm corner.1 corner.2 n := by
          unfold dTerm
          rw [if_neg hn, if_neg hn]
          calc
            _ ≤ ((nS n : ℝ) ^ (-(corner.1 + j * delta)) *
                    (n : ℝ) ^ (-(corner.2 + j * delta))) *
                  (2 * (((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) /
                    delta)) ^ j := by
                gcongr
            _ = (2 / delta) ^ j *
                  ((nS n : ℝ) ^ (-corner.1) *
                    (n : ℝ) ^ (-corner.2)) := by
                rw [mul_pow, div_pow]
                rw [show
                  ((nS n : ℝ) ^ (-(corner.1 + j * delta)) *
                        (n : ℝ) ^ (-(corner.2 + j * delta))) *
                      (2 ^ j *
                        ((((nS n : ℝ) ^ delta * (n : ℝ) ^ delta) ^ j) /
                          delta ^ j)) =
                    (2 / delta) ^ j *
                      (((nS n : ℝ) ^ (-(corner.1 + j * delta)) *
                          ((nS n : ℝ) ^ delta) ^ j) *
                        ((n : ℝ) ^ (-(corner.2 + j * delta)) *
                          ((n : ℝ) ^ delta) ^ j)) by
                    rw [div_pow]
                    ring]
                rw [hfirstCancel, hsecondCancel]
  have hf0 : Summable (fun n => f n p) :=
    hp.congr fun n => (hfEq n p).symm
  have hlocal := local_contDiffOn_tsum order hregionOpen hregionPreconnected
    hpRegion hf0 hfSmooth hvSummable hbound
  have hpoint : ContDiffAt ℝ order (fun q => ∑' n, f n q) p :=
    hlocal.contDiffAt (hregionOpen.mem_nhds hpRegion)
  simp_rw [hfEq] at hpoint
  exact hpoint.contDiffWithinAt

end D5.S3.Analytic.Regularity.GoldenDisplacementSeriesSmoothness
