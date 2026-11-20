/- GID: D5/S3/Observer/Linear/ReflectingHeatStripBound
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/ReflectingHeatStripBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Analytic.Hardy.FiniteStripMomentBound]
   utility: none
   digest: The strip estimate gives a lower bound on inverse diagonal entries of the reflecting heat Gramian in physical time. -/

import D5.S3.Analytic.Hardy.FiniteStripMomentBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Function.L2Space

/-! # The reflecting heat Gramian at the critical time -/

open Set MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace D5.S3.Observer.Linear.ReflectingHeatStripBound

open D5.S3.Analytic.Hardy.FiniteStripMomentBound

/-- The positive frequencies omit the constant cell mode. -/
abbrev Mode (n : ℕ) := Fin (n - 1)

private def angle (n : ℕ) (j : Mode n) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)

/-- Dimensionless rate of the cell-centered mode with frequency `j + 1`. -/
def rate (n : ℕ) (j : Mode n) : ℝ := 2 - 2 * Real.cos (angle n j)

/-- Readout of the mass-normalized cosine mode at the first cell. -/
def weight (n : ℕ) (j : Mode n) : ℝ := Real.sqrt (2 - rate n j / 2)

/-- Decay per unit of physical time. -/
def physicalRate (n : ℕ) (j : Mode n) : ℝ := (n : ℝ) ^ 2 * rate n j

private theorem angle_mem (n : ℕ) (j : Mode n) : angle n j ∈ Ioo 0 Real.pi := by
  have hn : 0 < (n : ℝ) := by
    have := j.isLt
    exact_mod_cast (show 0 < n by omega)
  have hj : ((j.val + 1 : ℕ) : ℝ) < (n : ℝ) := by
    have := j.isLt
    exact_mod_cast (show j.val + 1 < n by omega)
  unfold angle
  exact ⟨by positivity, (div_lt_iff₀ hn).2
    (by simpa [mul_comm] using mul_lt_mul_of_pos_right hj Real.pi_pos)⟩

private theorem rate_pos (n : ℕ) (j : Mode n) : 0 < rate n j := by
  have hj := angle_mem n j
  have ht := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hj.2.le hj.1
  rw [Real.cos_zero] at ht
  unfold rate
  linarith

private theorem weight_pos (n : ℕ) (j : Mode n) : 0 < weight n j := by
  have hj := angle_mem n j
  have ht := Real.cos_lt_cos_of_nonneg_of_le_pi hj.1.le le_rfl hj.2
  rw [Real.cos_pi] at ht
  unfold weight rate
  exact Real.sqrt_pos.2 (by linarith)

private theorem rate_injective {n : ℕ} (hn : 0 < n) : Function.Injective (rate n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro j k hjk
  have hcos : Real.cos (angle n j) = Real.cos (angle n k) := by
    unfold rate at hjk
    linarith
  have ht := Real.strictAntiOn_cos.injOn
    (Ioo_subset_Icc_self (angle_mem n j)) (Ioo_subset_Icc_self (angle_mem n k)) hcos
  unfold angle at ht
  apply Fin.ext
  have hcast : ((j.val + 1 : ℕ) : ℝ) = ((k.val + 1 : ℕ) : ℝ) :=
    mul_right_cancel₀ Real.pi_pos.ne' ((div_left_inj' hn'.ne').mp ht)
  exact Nat.succ.inj (by exact_mod_cast hcast)

private def cellProfile (n : ℕ) (j : Mode n) (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.cos ((x + 1 / 2) * angle n j)

/-- Cosine mode evaluated at the centers of the (n) cells. -/
def cellMode (n : ℕ) (j : Mode n) (i : Fin n) : ℝ := cellProfile n j i.val

private def leftCell {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, (Nat.sub_le ..).trans_lt i.isLt⟩

private def rightCell {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i

/-- The heat generator with mesh (1/n) and endpoint ghost cells equal to the
adjacent endpoint values. -/
def reflectingGenerator (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ) ^ 2 * (x (leftCell i) + x (rightCell i) - 2 * x i)

private theorem angle_mul_cells (n : ℕ) (j : Mode n) :
    (n : ℝ) * angle n j = ((j.val + 1 : ℕ) : ℝ) * Real.pi := by
  have hn : (n : ℝ) ≠ 0 := by
    have := j.isLt
    exact_mod_cast (show n ≠ 0 by omega)
  unfold angle
  field_simp

/-- The mass-normalized cell-center mode decays at the physical rate (n^2q_j). -/
theorem reflectingGenerator_cellMode (n : ℕ) (j : Mode n) (i : Fin n) :
    reflectingGenerator n (cellMode n j) i = -physicalRate n j * cellMode n j i := by
  have hleft : cellMode n j (leftCell i) = cellProfile n j ((i.val : ℝ) - 1) := by
    by_cases hi : i.val = 0
    · simp [cellMode, leftCell, hi, cellProfile]
      rw [show ((-1 : ℝ) + (2 : ℝ)⁻¹) * angle n j =
        -((2 : ℝ)⁻¹ * angle n j) by ring, Real.cos_neg]
    · have hcast : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
        simp
      exact congrArg (cellProfile n j) hcast
  have hright : cellMode n j (rightCell i) = cellProfile n j ((i.val : ℝ) + 1) := by
    unfold rightCell
    split
    · simp [cellMode, Nat.cast_add]
    · rename_i hi
      have hiv : i.val + 1 = n := by have := i.isLt; omega
      have harg : ((i.val : ℝ) + 1) * angle n j =
          ((j.val + 1 : ℕ) : ℝ) * Real.pi := by
        have he : (i.val : ℝ) + 1 = n := by exact_mod_cast hiv
        rw [he, angle_mul_cells]
      unfold cellMode cellProfile
      have h₁ : ((i.val : ℝ) + 1 / 2) * angle n j =
          ((j.val + 1 : ℕ) : ℝ) * Real.pi - angle n j / 2 := by linarith
      have h₂ : ((i.val : ℝ) + 1 + 1 / 2) * angle n j =
          angle n j / 2 + ((j.val + 1 : ℕ) : ℝ) * Real.pi := by linarith
      rw [h₁, h₂, Real.cos_nat_mul_pi_sub, Real.cos_add_nat_mul_pi]
  unfold reflectingGenerator physicalRate
  rw [hleft, hright]
  unfold cellMode cellProfile rate
  rw [show ((i.val : ℝ) - 1 + 1 / 2) * angle n j =
      ((i.val : ℝ) + 1 / 2) * angle n j - angle n j by ring,
    show ((i.val : ℝ) + 1 + 1 / 2) * angle n j =
      ((i.val : ℝ) + 1 / 2) * angle n j + angle n j by ring,
    Real.cos_sub, Real.cos_add]
  ring

private theorem cellMode_first (n : ℕ) (j : Mode n) (i : Fin n) (hi : i.val = 0) :
    cellMode n j i = weight n j := by
  have hangle := angle_mem n j
  have hcos : 0 < Real.cos (angle n j / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [hangle.1, Real.pi_pos], by linarith [hangle.2]⟩
  unfold cellMode cellProfile weight rate
  simp only [hi, Nat.cast_zero, zero_add]
  rw [show (1 / 2 : ℝ) * angle n j = angle n j / 2 by ring]
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
  have hdouble : Real.cos (angle n j) = 2 * Real.cos (angle n j / 2) ^ 2 - 1 := by
    conv_lhs => rw [show angle n j = 2 * (angle n j / 2) by ring]
    rw [Real.cos_two_mul]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by linarith [Real.neg_one_le_cos (angle n j)]), hdouble]
  ring

private theorem centered_cos_sum (n p : ℕ) (hp : 0 < p) (hpn : p < 2 * n) :
    (∑ i : Fin n, Real.cos (((i.val : ℝ) + 1 / 2) * ((p : ℝ) * Real.pi / n))) = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let θ := (p : ℝ) * Real.pi / (n : ℝ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ / 2 < Real.pi := by
    have hr : (p : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hpn
    dsimp [θ]
    rw [div_div, div_lt_iff₀ (by positivity : 0 < (n : ℝ) * 2)]
    nlinarith only [mul_lt_mul_of_pos_right hr Real.pi_pos]
  have hs := Real.sin_mul_sum_cos n θ (θ / 2)
  have harr : (n : ℝ) * θ / 2 = (p : ℝ) * Real.pi / 2 := by
    dsimp [θ]
    field_simp
  have harg : ((n : ℝ) - 1) * θ / 2 + θ / 2 = n * θ / 2 := by ring
  rw [harg, harr] at hs
  have hsc : Real.sin ((p : ℝ) * Real.pi / 2) * Real.cos ((p : ℝ) * Real.pi / 2) = 0 := by
    have he := Real.sin_two_mul ((p : ℝ) * Real.pi / 2)
    rw [show 2 * ((p : ℝ) * Real.pi / 2) = p * Real.pi by ring, Real.sin_nat_mul_pi] at he
    linarith only [he]
  rw [hsc] at hs
  have hsum := (mul_eq_zero.mp hs).resolve_left
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) hθπ).ne'
  change (∑ i : Fin n, Real.cos (((i.val : ℝ) + 1 / 2) * θ)) = 0
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => Real.cos (((i : ℝ) + 1 / 2) * θ))]
  refine (Finset.sum_congr rfl (fun i _ => ?_)).trans hsum
  congr 1
  ring

/-- The constant mode is absent, as each retained cosine mode has zero cell mass. -/
theorem cellMode_sum_zero (n : ℕ) (j : Mode n) : (∑ i, cellMode n j i) = 0 := by
  simp only [cellMode, cellProfile, ← Finset.mul_sum, angle]
  rw [centered_cos_sum n (j.val + 1) (by omega) (by have := j.isLt; omega), mul_zero]

/-- The retained modes are orthonormal for the cell mass (1/n). -/
theorem cellMode_mass_inner (n : ℕ) (j k : Mode n) :
    (∑ i, cellMode n j i * cellMode n k i) / (n : ℝ) = if j = k then 1 else 0 := by
  have hn : (0 : ℝ) < n := by
    have := j.isLt
    exact_mod_cast (show 0 < n by omega)
  have hsum : (∑ i : Fin n, Real.cos (((i.val : ℝ) + 1 / 2) *
      (angle n j + angle n k))) = 0 := by
    have hj := j.isLt
    have hk := k.isLt
    have he : angle n j + angle n k =
        ((j.val + 1 + (k.val + 1) : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
      unfold angle
      push_cast
      ring
    simp_rw [he]
    exact centered_cos_sum n _ (by omega) (by omega)
  have hdiff : ∀ j k : Mode n, j.val < k.val →
      (∑ i : Fin n, Real.cos (((i.val : ℝ) + 1 / 2) * (angle n j - angle n k))) = 0 := by
    intro u v huv
    have hv := v.isLt
    have he : angle n u - angle n v =
        -(((v.val - u.val : ℕ) : ℝ) * Real.pi / (n : ℝ)) := by
      unfold angle
      rw [Nat.cast_sub huv.le]
      push_cast
      ring
    simp only [he, mul_neg, Real.cos_neg]
    exact centered_cos_sum n _ (by omega) (by omega)
  have hsplit : (∑ i, cellMode n j i * cellMode n k i) =
      (∑ i : Fin n, Real.cos (((i.val : ℝ) + 1 / 2) * (angle n j - angle n k))) +
      (∑ i : Fin n, Real.cos (((i.val : ℝ) + 1 / 2) * (angle n j + angle n k))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold cellMode cellProfile
    rw [show Real.sqrt 2 * Real.cos (((i.val : ℝ) + 1 / 2) * angle n j) *
        (Real.sqrt 2 * Real.cos (((i.val : ℝ) + 1 / 2) * angle n k)) =
        (Real.sqrt 2) ^ 2 * Real.cos (((i.val : ℝ) + 1 / 2) * angle n j) *
          Real.cos (((i.val : ℝ) + 1 / 2) * angle n k) by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.two_mul_cos_mul_cos, mul_sub, mul_add]
  rw [hsplit, hsum, add_zero]
  rcases lt_trichotomy j.val k.val with hjk | hjk | hkj
  · rw [hdiff _ _ hjk, zero_div, if_neg (fun he => hjk.ne (congrArg Fin.val he))]
  · have he : j = k := Fin.ext hjk
    subst k
    simp [hn.ne']
  · have he : angle n j - angle n k = -(angle n k - angle n j) := by ring
    simp only [he, mul_neg, Real.cos_neg]
    rw [hdiff _ _ hkj, zero_div, if_neg (fun he => hkj.ne' (congrArg Fin.val he))]

/-- Heat evolution of the initial positive-mode coefficients on the reflecting cells. -/
def reflectingHeatFlow (n : ℕ) (c : Mode n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  ∑ j, (c j * Real.exp (-physicalRate n j * t)) * cellMode n j i

/-- The modal evolution solves the physical heat equation on the cells, preserves zero mean
and has the stated mass coordinates at every time. -/
theorem reflectingHeatFlow_spec (n : ℕ) (c : Mode n → ℝ) (t : ℝ) :
    (∀ i, HasDerivAt (fun s => reflectingHeatFlow n c s i)
      (reflectingGenerator n (reflectingHeatFlow n c t) i) t) ∧
    (∑ i, reflectingHeatFlow n c t i) = 0 ∧
    ∀ j, (∑ i, reflectingHeatFlow n c t i * cellMode n j i) / (n : ℝ) =
      c j * Real.exp (-physicalRate n j * t) := by
  constructor
  · intro i
    have hd (j : Mode n) : HasDerivAt
        (fun s : ℝ => (c j * Real.exp (-physicalRate n j * s)) * cellMode n j i)
        ((c j * Real.exp (-physicalRate n j * t)) *
          (-physicalRate n j * cellMode n j i)) t := by
      have hlin : HasDerivAt (fun s : ℝ => -physicalRate n j * s) (-physicalRate n j) t := by
        simpa using (hasDerivAt_id t).const_mul (-physicalRate n j)
      convert (hlin.exp.const_mul (c j)).mul_const (cellMode n j i) using 1
      ring
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
    apply hsum.congr_deriv
    simp_rw [← reflectingGenerator_cellMode]
    unfold reflectingGenerator reflectingHeatFlow
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  constructor
  · unfold reflectingHeatFlow
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, cellMode_sum_zero, mul_zero, Finset.sum_const_zero]
  · intro j
    unfold reflectingHeatFlow
    simp_rw [Finset.sum_mul, mul_assoc (c _ * _)]
    rw [Finset.sum_comm, Finset.sum_div]
    simp_rw [← Finset.mul_sum, mul_div_assoc, cellMode_mass_inner, mul_ite, mul_one, mul_zero]
    simp

private def signal {m : ℕ} (decay b : Fin m → ℝ) (k : Fin m) (t : ℝ) : ℝ :=
  b k * Real.exp (-decay k * t)

private def synthesis {m : ℕ} (decay b c : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ k, c k * signal decay b k t

private def gram {m : ℕ} (T : ℝ) (decay b : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  .of fun k i => ∫ t in Ioo 0 T, signal decay b k t * signal decay b i t

/-- Gramian of the first-cell observation in Lebesgue physical time, in the
orthonormal mean-zero cosine coordinates of the reflecting path. -/
def physicalGramian (n : ℕ) (T : ℝ) : Matrix (Mode n) (Mode n) ℝ :=
  .of fun j k => ∫ t in Ioo 0 T,
    (if hn : 0 < n then cellMode n j ⟨0, hn⟩ else 0) * Real.exp (-physicalRate n j * t) *
      ((if hn : 0 < n then cellMode n k ⟨0, hn⟩ else 0) *
        Real.exp (-physicalRate n k * t))

private theorem continuous_signal {m : ℕ} (decay b : Fin m → ℝ) (k : Fin m) :
    Continuous (signal decay b k) := by
  unfold signal
  fun_prop

private theorem continuous_synthesis {m : ℕ} (decay b c : Fin m → ℝ) :
    Continuous (synthesis decay b c) :=
  continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_signal decay b k)

private theorem continuous_integrable_window {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) :
    Integrable f (volume.restrict (Ioo 0 T)) :=
  (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

private theorem integral_signal_synthesis {m : ℕ} (T : ℝ) (decay b c : Fin m → ℝ) (k : Fin m) :
    (∫ t in Ioo 0 T, signal decay b k t * synthesis decay b c t) = (gram T decay b *ᵥ c) k := by
  unfold synthesis
  simp_rw [Finset.mul_sum, mul_left_comm (signal decay b k _)]
  rw [integral_finsetSum (f := fun i t => c i * (signal decay b k t * signal decay b i t))
    Finset.univ (fun i _ => continuous_integrable_window
      (continuous_const.mul ((continuous_signal decay b k).mul (continuous_signal decay b i))) T)]
  simp only [integral_const_mul, Matrix.mulVec, dotProduct, gram, Matrix.of_apply, mul_comm]

private theorem integral_synthesis_sq {m : ℕ} (T : ℝ) (decay b c : Fin m → ℝ) :
    (∫ t in Ioo 0 T, synthesis decay b c t ^ 2) = ∑ k, c k * (gram T decay b *ᵥ c) k := by
  trans ∫ t in Ioo 0 T, ∑ k, c k * (signal decay b k t * synthesis decay b c t)
  · apply integral_congr_ae
    filter_upwards with t
    simp only [← mul_assoc, ← Finset.sum_mul, pow_two, synthesis]
  rw [integral_finsetSum
    (f := fun i t => c i * (signal decay b i t * synthesis decay b c t))
    Finset.univ (fun i _ => continuous_integrable_window
      (continuous_const.mul ((continuous_signal decay b i).mul (continuous_synthesis decay b c))) T)]
  simp only [integral_const_mul, integral_signal_synthesis]

private theorem synthesis_zero {m : ℕ} {T : ℝ} (hT : 0 < T)
    {decay b c : Fin m → ℝ} (hdecay : Function.Injective decay) (hb : ∀ k, b k ≠ 0)
    (hz : ∀ t ∈ Ioo 0 T, synthesis decay b c t = 0) : c = 0 := by
  let δ : ℝ := T / ((m : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let f (k : Fin m) := Real.exp (-decay k * δ)
  have hf : Function.Injective f := by
    intro k i hki
    apply hdecay
    have h := Real.exp_injective hki
    exact neg_injective (mul_right_cancel₀ hδ.ne' h)
  let v (k : Fin m) := c k * b k * f k
  have hv : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro i
    have hi : ((i : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast i.isLt
    have ht : ((i.val + 1 : ℕ) : ℝ) * δ ∈ Ioo 0 T := by
      refine ⟨by positivity, ?_⟩
      change ((i.val + 1 : ℕ) : ℝ) * (T / ((m : ℝ) + 1)) < T
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)]
      have hi' : ((i.val + 1 : ℕ) : ℝ) < (m : ℝ) + 1 := by push_cast; linarith
      simpa [mul_comm] using mul_lt_mul_of_pos_right hi' hT
    have hx := hz _ ht
    unfold synthesis signal at hx
    rw [← hx]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [v, f]
    rw [mul_assoc (c k * b k), ← pow_succ', ← Real.exp_nat_mul, ← mul_assoc,
      show ((i.val + 1 : ℕ) : ℝ) * -decay k * δ =
        -decay k * (((i.val + 1 : ℕ) : ℝ) * δ) by ring, mul_assoc]
  funext k
  have he : c k * b k * f k = 0 := congrFun hv k
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (Real.exp_ne_zero _))).resolve_right (hb k)

private theorem gram_det_isUnit {m : ℕ} {T : ℝ} (hT : 0 < T)
    {decay b : Fin m → ℝ} (hdecay : Function.Injective decay) (hb : ∀ k, b k ≠ 0) :
    IsUnit (gram T decay b).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro c d hcd
  have hx : gram T decay b *ᵥ (c - d) = 0 := by rw [Matrix.mulVec_sub, hcd, sub_self]
  suffices heq : c - d = 0 by exact sub_eq_zero.mp heq
  apply synthesis_zero hT hdecay hb
  intro t ht
  by_contra! ht'
  have hi : (∫ t in Ioo 0 T, synthesis decay b (c - d) t ^ 2) = 0 := by
    rw [integral_synthesis_sq, hx]
    simp
  have hpos : 0 < (∫ t in Ioo 0 T, synthesis decay b (c - d) t ^ 2) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (continuous_integrable_window ((continuous_synthesis decay b (c - d)).pow 2) T)).2
    exact ((continuous_synthesis decay b (c - d)).pow 2).isOpen_support.inter isOpen_Ioo
      |>.measure_pos volume ⟨t, pow_ne_zero _ ht', ht⟩
  exact hpos.ne' hi

private theorem radius_scale {c : ℝ} (hc : 0 ≤ c) (β q : ℝ) :
    radius (c * β) (c * q) = c * radius β q := by
  unfold radius
  rw [show (c * q) ^ 2 + (c * β) ^ 2 = c ^ 2 * (q ^ 2 + β ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The lower bound in physical units for each nonconstant mode at time (a/n).
The mode factor is the first-cell weight and the rescaled duration is (na). -/
theorem inverse_diagonal_lower_bound (n : ℕ) (hn : 2 ≤ n) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (j : Mode n) :
    (n : ℝ) / weight n j *
        ((∏ k ∈ Finset.univ.erase j, (radius β (rate n j) + radius β (rate n k)) /
          |rate n j - rate n k|) * Real.exp (-(n : ℝ) * a * (radius β (rate n j) - rate n j) / 2) /
          Real.sqrt ((n : ℝ) * a)) ≤
      Real.sqrt ((physicalGramian n (a / (n : ℝ)))⁻¹ j j) := by
  let N : ℝ := n
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < n by omega)
  let T := a / N
  have hT : 0 < T := div_pos ha hN
  let decay := physicalRate n
  let b := weight n
  have hb (k : Mode n) : 0 < b k := weight_pos n k
  have hq := rate_injective (show 0 < n by omega)
  have hdecay : Function.Injective decay := fun _ _ h =>
    hq (mul_left_cancel₀ (pow_ne_zero 2 hN.ne') h)
  have hdecaypos (k : Mode n) : 0 ≤ decay k :=
    mul_nonneg (sq_nonneg N) (rate_pos n k).le
  let W := physicalGramian n T
  have hW : W = gram T decay b := by
    ext k i
    dsimp only [W, physicalGramian, gram, Matrix.of_apply, signal, decay, b]
    simp [show 0 < n by omega, cellMode_first]
  have hdet : IsUnit W.det :=
    hW ▸ gram_det_isUnit hT hdecay (fun k => (hb k).ne')
  let c (k : Mode n) := W⁻¹ k j
  let G := synthesis decay b c
  let h (t : ℝ) := b j * G t
  have hcolumn (k : Mode n) : (W *ᵥ c) k = if k = j then 1 else 0 := by
    have he := congrFun (congrFun (Matrix.mul_nonsing_inv W hdet) k) j
    simpa only [c, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply] using he
  have hsignal (k : Mode n) :
      (∫ t in Ioo 0 T, signal decay b k t * G t) = if k = j then 1 else 0 := by
    dsimp only [G]
    rw [integral_signal_synthesis, ← hW, hcolumn]
  have hm (k : Mode n) : (∫ t in Ioo 0 T, h t * Real.exp (-decay k * t)) =
      if k = j then 1 else 0 := by
    have hid : b k * (∫ t in Ioo 0 T, h t * Real.exp (-decay k * t)) =
        b j * (∫ t in Ioo 0 T, signal decay b k t * G t) := by
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [h, signal]
      ring
    rw [hsignal] at hid
    by_cases hek : k = j
    · subst k
      simp only [ite_true, mul_one] at hid ⊢
      exact mul_left_cancel₀ (hb j).ne' (hid.trans (mul_one _).symm)
    · simp only [ite_eq_right hek, mul_zero] at hid ⊢
      exact (mul_eq_zero.mp hid).resolve_left (hb k).ne'
  have hnrm : windowNorm T h = b j * Real.sqrt (W⁻¹ j j) := by
    have he : (∫ t in Ioo 0 T, G t ^ 2) = W⁻¹ j j := by
      dsimp only [G]
      rw [integral_synthesis_sq, ← hW]
      simp [hcolumn, c]
    unfold windowNorm
    simp only [h, mul_pow, integral_const_mul, he, Real.sqrt_mul (sq_nonneg (b j)),
      Real.sqrt_sq (hb j).le]
  have hcont : Continuous h := continuous_const.mul (continuous_synthesis decay b c)
  have hlp : MemLp h 2 (volume.restrict (Ioo 0 T)) := by
    have hi := continuous_integrable_window (hcont.pow 2) T
    exact (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hi
  have lower := windowNorm_lower_bound hT (show 0 < N ^ 2 * β by positivity)
    decay hdecaypos hdecay j h hlp hm
  rw [hnrm] at lower
  have hscale (k : Mode n) : radius (N ^ 2 * β) (decay k) = N ^ 2 * radius β (rate n k) :=
    radius_scale (sq_nonneg N) β (rate n k)
  simp_rw [hscale] at lower
  have hp (k : Mode n) :
      (N ^ 2 * radius β (rate n j) + N ^ 2 * radius β (rate n k)) / |decay j - decay k| =
        (radius β (rate n j) + radius β (rate n k)) / |rate n j - rate n k| := by
    change _ / |N ^ 2 * rate n j - N ^ 2 * rate n k| = _
    rw [← mul_add, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg N)]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hN.ne')
  simp_rw [hp] at lower
  have htime : -T * (N ^ 2 * radius β (rate n j) - decay j) / 2 =
      -N * a * (radius β (rate n j) - rate n j) / 2 := by
    change -(a / N) * (N ^ 2 * radius β (rate n j) - N ^ 2 * rate n j) / 2 = _
    field_simp
    <;> ring
  have hsqrt : Real.sqrt (N * a) = N * Real.sqrt T := by
    rw [show N * a = N ^ 2 * T by dsimp [T]; field_simp,
      Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
  rw [htime] at lower
  rw [mul_comm (b j) (Real.sqrt (W⁻¹ j j))] at lower
  have hr := (div_le_iff₀ (hb j)).2 lower
  change N / b j * (_ / Real.sqrt (N * a)) ≤ Real.sqrt (W⁻¹ j j)
  rw [hsqrt]
  convert hr using 1
  field_simp [hN.ne', (hb j).ne', (Real.sqrt_pos.2 hT).ne']
  <;> ring

#print axioms inverse_diagonal_lower_bound

end D5.S3.Observer.Linear.ReflectingHeatStripBound
