/- GID: D5/S1/Digit/Infinite/ResetCodebookGrowth
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Row growth and simultaneous departure observation bounds. -/

import D5.S1.Digit.Infinite.ResetCodebookOrder
import Mathlib.Tactic.LinearCombination
local notation "g_bounds" => And.intro (And.left (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)) (And.left (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)))
local notation "g_relation" => (And.left D5.S1.Digit.Infinite.SixWindowForcing.algebra)
local notation "g_eq" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations))))
local notation "t_sq" => (And.right (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "t_linear" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "complexify" => Complex.ofRealHom.mapMatrix
local notation "radius" => fun A => ENNReal.toReal (spectralRadius ℂ (Complex.ofRealHom.mapMatrix A))
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology ENNReal NNReal
open Filter
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
lemma radius_smul (A : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c) :
    radius (c • A) = c * radius A := by
  have hh : complexify (c • A) = c • complexify A := by
    ext i j
    simp [RingHom.mapMatrix_apply, smul_eq_mul, Complex.ofReal_mul]
  apply tendsto_nhds_unique (gelfand (c • A))
  have he : ∀ᶠ k : ℕ in atTop,
      ‖complexify (c • A)^k‖ ^ (1/(k:ℝ)) = c * ‖complexify A^k‖ ^ (1/(k:ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    rw [hh, smul_pow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc _),
      Real.mul_rpow (pow_nonneg hc _) (norm_nonneg _), one_div, Real.pow_rpow_inv_natCast hc (by omega)]
  exact (tendsto_const_nhds.mul (gelfand A)).congr' (he.mono (fun k hk => hk.symm))
lemma positive_row_le_norm (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (i : ι) :
    (∑ j, A i j) ≤ ‖complexify A‖ := by
  have he (j : ι) : ‖(complexify A) i j‖ = A i j := by
    simp [RingHom.mapMatrix_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j)]
  calc
    _ = ∑ j, ‖(complexify A) i j‖ := by simp_rw [he]
    _ = ((∑ j : ι, ‖(complexify A) i j‖₊) : ℝ) := by simp
    _ ≤ (((Finset.univ.sup fun i : ι => ∑ j, ‖(complexify A) i j‖₊) : ℝ≥0) : ℝ) := by
      exact_mod_cast (Finset.le_sup (f := fun x : ι => ∑ j, ‖(complexify A) x j‖₊) (Finset.mem_univ i))
    _ = _ := (Matrix.linfty_opNorm_def _).symm
lemma row_power_lower (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (r : ℝ) (hr : 0 ≤ r) (hrow : ∀ i, r ≤ ∑ j, A i j) (k : ℕ) :
    ∀ i, r^k ≤ ∑ j, (A^k) i j := by
  induction k with
  | zero => intro i; simp [Matrix.one_apply]
  | succ k ih =>
    intro i
    rw [show A^(k+1)=A*A^k from pow_succ' _ _]
    simp_rw [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum]
    calc
      _ ≤ (∑ x, A i x)*r^k := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right (hrow i) (pow_nonneg hr _)
      _ ≤ ∑ x, A i x * ∑ j, (A^k) x j := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (ih x) (hA i x))
lemma row_lower_radius (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (r : ℝ) (hr : 0 ≤ r) (hrow : ∀ i, r ≤ ∑ j, A i j) : r ≤ radius A := by
  apply ge_of_tendsto (gelfand A)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hl := (row_power_lower A hA r hr hrow k (Classical.choice ‹Nonempty ι›)).trans
    (positive_row_le_norm (A^k) (positive_pow A hA k) _)
  have he : complexify (A^k)=complexify A ^ k := map_pow Complex.ofRealHom.mapMatrix A k
  rw [he] at hl
  have hh := Real.rpow_le_rpow (pow_nonneg hr _) hl (by positivity : 0 ≤ 1/(k:ℝ))
  rw [one_div, Real.pow_rpow_inv_natCast hr (by omega)] at hh
  simpa only [one_div] using hh
lemma radius_sq (A : Matrix ι ι ℝ) : radius (A^2) = radius A ^ 2 := by
  have he : complexify (A^2)=complexify A ^ 2 := map_pow Complex.ofRealHom.mapMatrix A 2
  have hm : Tendsto (fun k : ℕ => 2*k) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b,fun k hk => by omega⟩
  have hh := ((gelfand A).comp hm).pow 2
  apply tendsto_nhds_unique (gelfand (A^2))
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  dsimp only [Function.comp_def]
  rw [he, ←pow_mul, ←Real.rpow_natCast, ←Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  field_simp
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Words.Powers (wordPower)
namespace D5.S1.Digit.Infinite.ResetCodebook
theorem small_powers (n : ℕ) : 0 ≤ g^n ∧ g^n ≤ (1/4:ℝ)^n := by
  have hg := g_bounds
  exact ⟨pow_nonneg (by linarith) n, pow_le_pow_left₀ (by linarith) (by linarith) n⟩
private theorem rho_small : rho ≤ 1/4096 := by
  have hh:=(small_powers 6).2
  norm_num at hh
  exact hh
private theorem perturb_bound (n : ℕ) (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    |(-g)^n*(z-c0)| ≤ (1/4:ℝ)^(n+1) := by
  rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (by have := g_bounds; linarith)]
  calc
    _ ≤ (1/4:ℝ)^n * (1/4:ℝ) :=
      mul_le_mul (small_powers n).2 hz (abs_nonneg _) (by positivity)
    _ = _ := (pow_succ _ _).symm
theorem auto_positive : 0 < lambda-rho := by
  have hb:=g_bounds
  have hr:=rho_small
  rw [lambda_linear]
  linarith
private theorem U_slot_0 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (U.drop 0) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 6 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [U_scalar_0]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem U_slot_1 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (U.drop 1) z) (cellLower 1) (cellUpper 1) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 5 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [U_scalar_1]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem U_slot_2 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (U.drop 2) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 4 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [U_scalar_2]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem U_slot_3 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (U.drop 3) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 3 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [U_scalar_3]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem U_slot_5 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (U.drop 5) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 1 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [U_scalar_5]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem V_slot_0 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (V.drop 0) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 6 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [V_scalar_0]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem V_slot_1 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (V.drop 1) z) (cellLower 1) (cellUpper 1) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 5 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [V_scalar_1]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem V_slot_2 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (V.drop 2) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 4 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [V_scalar_2]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem V_slot_3 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (V.drop 3) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 3 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [V_scalar_3]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem V_slot_5 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (V.drop 5) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 1 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [V_scalar_5]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_0 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 0) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 20 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_0]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_1 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 1) z) (cellLower 3) (cellUpper 3) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 19 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_1]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_2 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 2) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 18 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_2]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_3 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 3) z) (cellLower 3) (cellUpper 3) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 17 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_3]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_4 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 4) z) (cellLower 4) (cellUpper 4) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 16 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_4]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_5 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 5) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 15 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_5]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_6 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 6) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 14 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_6]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_7 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 7) z) (cellLower 1) (cellUpper 1) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 13 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_7]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_8 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 8) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 12 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_8]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_9 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 9) z) (cellLower 5) (cellUpper 5) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 11 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_9]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_10 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 10) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 10 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_10]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_11 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 11) z) (cellLower 1) (cellUpper 1) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 9 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_11]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_12 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 12) z) (cellLower 1) (cellUpper 1) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 8 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_12]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_13 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 13) z) (cellLower 3) (cellUpper 3) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 7 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_13]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_14 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 14) z) (cellLower 3) (cellUpper 3) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 6 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_14]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_15 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 15) z) (cellLower 5) (cellUpper 5) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 5 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_15]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_16 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 16) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 4 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_16]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_17 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 17) z) (cellLower 0) (cellUpper 0) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 3 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_17]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_18 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 18) z) (cellLower 1) (cellUpper 1) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 2 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_18]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem C_slot_19 (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    intervalDistance (wordScalar (C.drop 19) z) (cellLower 2) (cellUpper 2) ≤ lambda-rho := by
  have hp := abs_le.mp (perturb_bound 1 z hz)
  have hb := g_tight
  have hr := rho_small
  rw [C_scalar_19]
  unfold intervalDistance
  simp only [max_le_iff]
  norm_num [cellLower,cellUpper,cuts] at *
  simp only [lambda_linear,t_sq] at *
  try simp only [t_linear] at *
  norm_num at *
  constructor
  · linarith
  · constructor
    · have ha:=auto_positive
      rw [lambda_linear] at ha
      linarith
    · linarith
private theorem U_active (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) :
    intervalDistance (wordScalar (U.drop 4) (coord false D)) (cellLower 1) (cellUpper 1)
      = lambda-g^2*D := by
  have hb := g_bounds
  have hg0 : 0 ≤ g := by linarith
  have hg2 := (small_powers 2).2
  have hp := mul_nonneg (sq_nonneg g) hD
  have hu : g^2*D ≤ 1/64 := by nlinarith
  rw [U_scalar_4]
  norm_num [coord,center,cellLower,cellUpper,cuts]
  simp only [lambda_linear,t_sq]
  try simp only [t_linear]
  norm_num
  unfold intervalDistance
  ring_nf
  apply le_antisymm
  · simp only [max_le_iff]
    constructor
    · nlinarith
    · constructor <;> nlinarith
  · exact le_max_left _ _
private theorem V_active (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) :
    intervalDistance (wordScalar (V.drop 4) (coord true D)) (cellLower 1) (cellUpper 1)
      = lambda-g^2*D := by
  have hb := g_bounds
  have hg0 : 0 ≤ g := by linarith
  have hg2 := (small_powers 2).2
  have hp := mul_nonneg (sq_nonneg g) hD
  have hu : g^2*D ≤ 1/64 := by nlinarith
  rw [V_scalar_4]
  norm_num [coord,center,cellLower,cellUpper,cuts]
  simp only [lambda_linear,t_sq]
  try simp only [t_linear]
  norm_num
  unfold intervalDistance
  ring_nf
  apply le_antisymm
  · simp only [max_le_iff]
    constructor
    · nlinarith
    · constructor <;> nlinarith
  · exact (le_max_right _ _).trans (le_max_right _ _)
theorem U_cost (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) :
    wordCost U sixColor (coord false D) ≤ max (lambda-g^2*D) (lambda-rho) := by
  have hz : |coord false D-c0| ≤ 1/4 := by
    simp only [coord, Bool.false_eq_true, if_false, if_true]
    rw [abs_le]; constructor <;> linarith
  have hs0 := U_slot_0 (coord false D) hz
  have hs1 := U_slot_1 (coord false D) hz
  have hs2 := U_slot_2 (coord false D) hz
  have hs3 := U_slot_3 (coord false D) hz
  have hs4 := U_active D hD hD1
  have hs5 := U_slot_5 (coord false D) hz
  change max _ _ ≤ _
  exact (max_le (hs0.trans (le_max_right _ _)) (max_le (hs1.trans (le_max_right _ _)) (max_le (hs2.trans (le_max_right _ _)) (max_le (hs3.trans (le_max_right _ _)) (max_le ((le_of_eq hs4).trans (le_max_left _ _)) (max_le (hs5.trans (le_max_right _ _)) (auto_positive.le.trans (le_max_right _ _))))))))
theorem V_cost (D : ℝ) (hD : 0 ≤ D) (hD1 : D ≤ 1/4) :
    wordCost V sixColor (coord true D) ≤ max (lambda-g^2*D) (lambda-rho) := by
  have hz : |coord true D-c0| ≤ 1/4 := by
    simp only [coord, Bool.false_eq_true, if_false, if_true]
    rw [abs_le]; constructor <;> linarith
  have hs0 := V_slot_0 (coord true D) hz
  have hs1 := V_slot_1 (coord true D) hz
  have hs2 := V_slot_2 (coord true D) hz
  have hs3 := V_slot_3 (coord true D) hz
  have hs4 := V_active D hD hD1
  have hs5 := V_slot_5 (coord true D) hz
  change max _ _ ≤ _
  exact (max_le (hs0.trans (le_max_right _ _)) (max_le (hs1.trans (le_max_right _ _)) (max_le (hs2.trans (le_max_right _ _)) (max_le (hs3.trans (le_max_right _ _)) (max_le ((le_of_eq hs4).trans (le_max_left _ _)) (max_le (hs5.trans (le_max_right _ _)) (auto_positive.le.trans (le_max_right _ _))))))))
theorem C_cost (z : ℝ) (hz : |z-c0| ≤ 1/4) :
    wordCost C twentyColor z ≤ lambda-rho := by
  have hs0 := C_slot_0 z hz
  have hs1 := C_slot_1 z hz
  have hs2 := C_slot_2 z hz
  have hs3 := C_slot_3 z hz
  have hs4 := C_slot_4 z hz
  have hs5 := C_slot_5 z hz
  have hs6 := C_slot_6 z hz
  have hs7 := C_slot_7 z hz
  have hs8 := C_slot_8 z hz
  have hs9 := C_slot_9 z hz
  have hs10 := C_slot_10 z hz
  have hs11 := C_slot_11 z hz
  have hs12 := C_slot_12 z hz
  have hs13 := C_slot_13 z hz
  have hs14 := C_slot_14 z hz
  have hs15 := C_slot_15 z hz
  have hs16 := C_slot_16 z hz
  have hs17 := C_slot_17 z hz
  have hs18 := C_slot_18 z hz
  have hs19 := C_slot_19 z hz
  change max _ _ ≤ _
  exact (max_le hs0 (max_le hs1 (max_le hs2 (max_le hs3 (max_le hs4 (max_le hs5 (max_le hs6 (max_le hs7 (max_le hs8 (max_le hs9 (max_le hs10 (max_le hs11 (max_le hs12 (max_le hs13 (max_le hs14 (max_le hs15 (max_le hs16 (max_le hs17 (max_le hs18 (max_le hs19 auto_positive.le))))))))))))))))))))
end D5.S1.Digit.Infinite.ResetCodebook
