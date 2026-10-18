/- GID: D5/S3/Entropy/RenyiCombining/CachinElasticityMonotone
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinElasticityMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real-power elasticity certificate for binary Renyi information combining. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-! A real-power monotonicity certificate, including the boundary parameter n = 1. -/

open Set

namespace D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone

noncomputable def T (n r : ℝ) : ℝ := (1 - r ^ n) / (1 + r ^ n)
noncomputable def A (n r : ℝ) : ℝ := n * r ^ (n - 1) * (1 - r ^ (2 : ℕ)) /
  (1 - r ^ (2 * n))
noncomputable def B (n r : ℝ) : ℝ := ((1 - r) / (1 + r)) * T n r
noncomputable def F (n r : ℝ) : ℝ := (A n r - B n r) / (1 + B n r)

private noncomputable def J (n z : ℝ) : ℝ :=
  (n - 1) - (n + 1) * z + (n + 1) * z ^ n - (n - 1) * z ^ (n + 1)
private noncomputable def J₁ (n z : ℝ) : ℝ :=
  (n + 1) * (-1 + n * z ^ (n - 1) - (n - 1) * z ^ n)

private theorem J_hasDerivAt (n z : ℝ) (hz : 0 < z) :
    HasDerivAt (J n) (J₁ n z) z := by
  have hn := Real.hasDerivAt_rpow_const (p := n) (Or.inl hz.ne')
  have hn1 := Real.hasDerivAt_rpow_const (p := n + 1) (Or.inl hz.ne')
  convert (((hasDerivAt_const z (n - 1)).sub ((hasDerivAt_id z).const_mul (n + 1))).add
    (hn.const_mul (n + 1))).sub (hn1.const_mul (n - 1)) using 1 <;>
    dsimp [J, J₁] <;> congr 1 <;> ring_nf

private theorem J1_hasDerivAt (n z : ℝ) (hz : 0 < z) :
    HasDerivAt (J₁ n) (n * (n ^ (2 : ℕ) - 1) * z ^ (n - 2) * (1 - z)) z := by
  have hn := Real.hasDerivAt_rpow_const (p := n) (Or.inl hz.ne')
  have hn1 := Real.hasDerivAt_rpow_const (p := n - 1) (Or.inl hz.ne')
  have he : z ^ (n - 1) = z ^ (n - 2) * z := by
    calc
      z ^ (n - 1) = z ^ ((n - 2) + 1) := by congr 1; ring
      _ = z ^ (n - 2) * z := by rw [Real.rpow_add hz, Real.rpow_one]
  convert (((hasDerivAt_const z (-1)).add (hn1.const_mul n)).sub
    (hn.const_mul (n - 1))).const_mul (n + 1) using 1
  · rfl
  · rw [show n - 1 - 1 = n - 2 by ring, he]
    ring

private theorem J_nonneg (n z : ℝ) (hn : 0 ≤ n * (n ^ (2 : ℕ) - 1)) (hz : z ∈ Ioo 0 1) :
    0 ≤ J n z := by
  have hder₁ : ∀ x ∈ Icc z 1, HasDerivAt (J₁ n)
      (n * (n ^ (2 : ℕ) - 1) * x ^ (n - 2) * (1 - x)) x := by
    intro x hx
    exact J1_hasDerivAt n x (hz.1.trans_le hx.1)
  have hm₁ : MonotoneOn (J₁ n) (Icc z 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x hx => (hder₁ x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hder₁ x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hder₁ x (interior_subset hx)).deriv]
        have hx' := interior_subset hx
        have hnn : 0 ≤ n * (n ^ (2 : ℕ) - 1) := hn
        exact mul_nonneg (mul_nonneg hnn (Real.rpow_nonneg (le_of_lt (hz.1.trans_le hx'.1)) _))
          (sub_nonneg.mpr hx'.2))
  have hj₁ : ∀ x ∈ Icc z 1, J₁ n x ≤ 0 := by
    intro x hx
    have h := hm₁ hx ⟨hz.2.le, le_rfl⟩ hx.2
    have hone : J₁ n 1 = 0 := by simp only [J₁, Real.one_rpow]; ring
    simpa only [hone] using h
  have hder : ∀ x ∈ Icc z 1, HasDerivAt (J n) (J₁ n x) x :=
    fun x hx => J_hasDerivAt n x (hz.1.trans_le hx.1)
  have hm : AntitoneOn (J n) (Icc z 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hder x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [(hder x (interior_subset hx)).deriv]; exact hj₁ x (interior_subset hx))
  have h := hm ⟨le_rfl, hz.2.le⟩ ⟨hz.2.le, le_rfl⟩ hz.2.le
  simpa [J] using h

private theorem T_pos (n r : ℝ) (hn : 1 ≤ n) (hr : r ∈ Ioo 0 1) : 0 < T n r := by
  have hp := Real.rpow_pos_of_pos hr.1 n
  have hlt := Real.rpow_lt_one hr.1.le hr.2 (by linarith : 0 < n)
  exact div_pos (sub_pos.mpr hlt) (by linarith)

theorem T_hasDerivAt (n r : ℝ) (hr : 0 < r) :
    HasDerivAt (T n) (-2 * n * r ^ (n - 1) / (1 + r ^ n) ^ (2 : ℕ)) r := by
  have hp := Real.rpow_pos_of_pos hr n
  have hd := Real.hasDerivAt_rpow_const (p := n) (Or.inl hr.ne')
  convert ((hasDerivAt_const r 1).sub hd).div ((hasDerivAt_const r 1).add hd)
    (by linarith : 1 + r ^ n ≠ 0) using 1
  · rfl
  · dsimp
    ring

theorem A_eq (n r : ℝ) (hr : 0 < r) :
    A n r = n * r ^ (n - 1) * (1 - r ^ (2 : ℕ)) / ((1 - r ^ n) * (1 + r ^ n)) := by
  have he : r ^ (2 * n) = (r ^ n) ^ (2 : ℕ) := by
    rw [mul_comm (2 : ℝ), Real.rpow_mul hr.le, Real.rpow_two]
  unfold A
  rw [he]
  congr 1
  ring

private theorem A_pos (n r : ℝ) (hn : 1 ≤ n) (hr : r ∈ Ioo 0 1) : 0 < A n r := by
  rw [A_eq n r hr.1]
  have hp := Real.rpow_pos_of_pos hr.1 n
  have hlt := Real.rpow_lt_one hr.1.le hr.2 (by linarith : 0 < n)
  exact div_pos
    (mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hr.1 _)) (by nlinarith [hr.1, hr.2]))
    (mul_pos (sub_pos.mpr hlt) (by linarith))

private theorem B_pos (n r : ℝ) (hn : 1 ≤ n) (hr : r ∈ Ioo 0 1) : 0 < B n r := by
  exact mul_pos (div_pos (sub_pos.mpr hr.2) (by linarith [hr.1])) (T_pos n r hn hr)

private theorem A_hasDerivAt (n r : ℝ) (hn : n ≠ 0) (hr : r ∈ Ioo 0 1) :
    HasDerivAt (A n) (n * r ^ (n - 2) * J n (r ^ (2 : ℕ)) /
      (1 - r ^ (2 * n)) ^ (2 : ℕ)) r := by
  have hne : 1 - r ^ (2 * n) ≠ 0 := by
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hlt : 1 < r ^ (2 * n) := by
        have h := Real.rpow_lt_rpow_of_exponent_gt hr.1 hr.2 (by linarith : 2 * n < 0)
        simpa using h
      exact sub_ne_zero.mpr (ne_of_lt hlt)
    · exact sub_ne_zero.mpr (ne_of_gt (Real.rpow_lt_one hr.1.le hr.2 (by linarith)))
  have hd := Real.hasDerivAt_rpow_const (p := n - 1) (Or.inl hr.1.ne')
  have hd2 := Real.hasDerivAt_rpow_const (p := 2 * n) (Or.inl hr.1.ne')
  have he₁ : r ^ (n - 1) = r ^ n / r := by
    rw [Real.rpow_sub hr.1, Real.rpow_one]
  have he₂ : r ^ (n - 2) = r ^ n / r ^ (2 : ℕ) := by
    rw [Real.rpow_sub hr.1, Real.rpow_two]
  have he₃ : r ^ (2 * n - 1) = r ^ (2 * n) / r := by
    rw [Real.rpow_sub hr.1, Real.rpow_one]
  have he₄ : (r ^ (2 : ℕ)) ^ n = r ^ (2 * n) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hr.1.le]
  have he₅ : (r ^ (2 : ℕ)) ^ (n + 1) = r ^ (2 * n) * r ^ (2 : ℕ) := by
    rw [Real.rpow_add (sq_pos_of_pos hr.1), he₄, Real.rpow_one]
  have hraw := ((hd.const_mul n).mul ((hasDerivAt_const r 1).sub (hasDerivAt_pow 2 r))).div
    ((hasDerivAt_const r 1).sub hd2) hne
  convert hraw using 1
  · rfl
  · dsimp [J]
    rw [show n - 1 - 1 = n - 2 by ring, he₁, he₂, he₃, he₄, he₅]
    field_simp [hr.1.ne', hne]
    <;> ring

private noncomputable def B₁ (n r : ℝ) : ℝ :=
  -2 * T n r / (1 + r) ^ (2 : ℕ) -
    2 * n * ((1 - r) / (1 + r)) * r ^ (n - 1) / (1 + r ^ n) ^ (2 : ℕ)

private theorem B_hasDerivAt (n r : ℝ) (hr : r ∈ Ioo 0 1) :
    HasDerivAt (B n) (B₁ n r) r := by
  have hne : 1 + r ≠ 0 := by linarith [hr.1]
  have hd := (((hasDerivAt_const r 1).sub (hasDerivAt_id r)).div
    ((hasDerivAt_const r 1).add (hasDerivAt_id r)) hne).mul (T_hasDerivAt n r hr.1)
  convert hd using 1
  · rfl
  · dsimp [B₁]
    ring

private theorem B₁_neg (n r : ℝ) (hn : 1 ≤ n) (hr : r ∈ Ioo 0 1) :
    B₁ n r < 0 := by
  have hT := T_pos n r hn hr
  have hτ : 0 < (1 - r) / (1 + r) := div_pos (sub_pos.mpr hr.2) (by linarith [hr.1])
  have hp := Real.rpow_pos_of_pos hr.1 n
  have hs₁ : 0 < (1 + r) ^ (2 : ℕ) := sq_pos_of_pos (by linarith [hr.1])
  have hs₂ : 0 < (1 + r ^ n) ^ (2 : ℕ) := sq_pos_of_pos (by linarith)
  have hterm : 0 < 2 * n * ((1 - r) / (1 + r)) * r ^ (n - 1) /
      (1 + r ^ n) ^ (2 : ℕ) :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) hτ)
      (Real.rpow_pos_of_pos hr.1 _)) hs₂
  have hfirst : -2 * T n r / (1 + r) ^ (2 : ℕ) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hT) hs₁
  dsimp [B₁]
  linarith

private noncomputable def A₁ (n r : ℝ) : ℝ :=
  n * r ^ (n - 2) * J n (r ^ (2 : ℕ)) / (1 - r ^ (2 * n)) ^ (2 : ℕ)

private theorem A₁_nonneg (n r : ℝ) (hn : 1 ≤ n) (hr : r ∈ Ioo 0 1) :
    0 ≤ A₁ n r := by
  have hr₂ : r ^ (2 : ℕ) ∈ Ioo (0 : ℝ) 1 := ⟨sq_pos_of_pos hr.1, by nlinarith [hr.1, hr.2]⟩
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hr.1.le _))
    (J_nonneg n _ (by nlinarith) hr₂)) (sq_nonneg _)

private noncomputable def F₁ (n r : ℝ) : ℝ :=
  A₁ n r / (1 + B n r) - (1 + A n r) * B₁ n r / (1 + B n r) ^ (2 : ℕ)

private theorem F_hasDerivAt (n r : ℝ) (hn : n ≠ 0) (hr : r ∈ Ioo 0 1)
    (hB : 0 < 1 + B n r) :
    HasDerivAt (F n) (F₁ n r) r := by
  have hne : 1 + B n r ≠ 0 := ne_of_gt hB
  have hdA : HasDerivAt (A n) (A₁ n r) r := A_hasDerivAt n r hn hr
  convert (hdA.sub (B_hasDerivAt n r hr)).div
    ((hasDerivAt_const r 1).add (B_hasDerivAt n r hr)) hne using 1
  · rfl
  · dsimp [F₁]
    field_simp [hne]
    ring

private theorem F₁_pos (n r : ℝ) (hn : 1 ≤ n) (hr : r ∈ Ioo 0 1) :
    0 < F₁ n r := by
  have hA := A_pos n r hn hr
  have hB := B_pos n r hn hr
  have hA₁ := A₁_nonneg n r hn hr
  have hB₁ := B₁_neg n r hn hr
  have hterm : (1 + A n r) * B₁ n r / (1 + B n r) ^ (2 : ℕ) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hB₁)
      (sq_pos_of_pos (by linarith))
  have hfirst : 0 ≤ A₁ n r / (1 + B n r) := div_nonneg hA₁ (by linarith)
  dsimp [F₁]
  linarith

theorem monotoneOn_F (n : ℝ) (hn : 1 ≤ n) : MonotoneOn (F n) (Ioo 0 1) := by
  apply (strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun r hr => (F_hasDerivAt n r (by linarith) hr (by have h := B_pos n r hn hr; linarith)).continuousAt.continuousWithinAt) _).monotoneOn
  intro r hr
  have hr' : r ∈ Ioo (0 : ℝ) 1 := interior_subset hr
  rw [(F_hasDerivAt n r (by linarith) hr' (by have h := B_pos n r hn hr'; linarith)).deriv]
  exact F₁_pos n r hn hr'

end D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone

open Set
open D5.S3.Entropy.RenyiCombining.CachinElasticityMonotone

namespace D5.S3.Entropy.RenyiCombining.CachinNegativeBranch

private theorem power_gt_one (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    1 < r ^ n := by
  have h := Real.rpow_lt_rpow_of_exponent_gt hr.1 hr.2 hn
  simpa using h

private theorem T_neg (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    T n r < 0 := by
  have hp := power_gt_one n r hn hr
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

private theorem A_pos (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    0 < A n r := by
  rw [A_eq n r hr.1]
  have hp := power_gt_one n r hn hr
  exact div_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hn (Real.rpow_pos_of_pos hr.1 _))
      (by nlinarith [hr.1, hr.2]))
    (mul_neg_of_neg_of_pos (by linarith) (by linarith))

private theorem B_bounds (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    -1 < B n r ∧ B n r < 0 := by
  have hp := Real.rpow_pos_of_pos hr.1 n
  have ht := T_neg n r hn hr
  have ht₀ : -1 < T n r := by
    dsimp [T]
    apply (lt_div_iff₀ (by linarith : 0 < 1 + r ^ n)).mpr
    linarith
  have hτ₀ : 0 < (1 - r) / (1 + r) := div_pos (by linarith [hr.2]) (by linarith [hr.1])
  have hτ₁ : (1 - r) / (1 + r) < 1 := by
    apply (div_lt_one (by linarith [hr.1] : 0 < 1 + r)).mpr
    linarith [hr.1]
  have hprod : T n r < ((1 - r) / (1 + r)) * T n r := by nlinarith
  exact ⟨ht₀.trans hprod, mul_neg_of_pos_of_neg hτ₀ ht⟩

private theorem B₁_pos (n r : ℝ) (hn : n < 0) (hr : r ∈ Ioo 0 1) :
    0 < B₁ n r := by
  have ht := T_neg n r hn hr
  have hp := Real.rpow_pos_of_pos hr.1 n
  have hτ : 0 < (1 - r) / (1 + r) := div_pos (by linarith [hr.2]) (by linarith [hr.1])
  have hfirst : 0 < -2 * T n r / (1 + r) ^ (2 : ℕ) :=
    div_pos (mul_pos_of_neg_of_neg (by norm_num) ht) (sq_pos_of_pos (by linarith [hr.1]))
  have hsecond : 2 * n * ((1 - r) / (1 + r)) * r ^ (n - 1) /
      (1 + r ^ n) ^ (2 : ℕ) < 0 :=
    div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hτ)
        (Real.rpow_pos_of_pos hr.1 _)) (sq_pos_of_pos (by linarith))
  dsimp [B₁]
  linarith

private theorem A₁_nonpos (n r : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0)
    (hr : r ∈ Ioo 0 1) : A₁ n r ≤ 0 := by
  have hr₂ : r ^ (2 : ℕ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨sq_pos_of_pos hr.1, by nlinarith [hr.1, hr.2]⟩
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hn₁.le (Real.rpow_nonneg hr.1.le _))
      (J_nonneg n _ (mul_nonneg_of_nonpos_of_nonpos hn₁.le (by nlinarith)) hr₂)) (sq_nonneg _)

private theorem F₁_neg (n r : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0)
    (hr : r ∈ Ioo 0 1) : F₁ n r < 0 := by
  have hA := A_pos n r hn₁ hr
  have hB := (B_bounds n r hn₁ hr).1
  have hA₁ := A₁_nonpos n r hn₀ hn₁ hr
  have hB₁ := B₁_pos n r hn₁ hr
  have hfirst : A₁ n r / (1 + B n r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hA₁ (by linarith)
  have hsecond : 0 < (1 + A n r) * B₁ n r / (1 + B n r) ^ (2 : ℕ) :=
    div_pos (mul_pos (by linarith) hB₁) (sq_pos_of_pos (by linarith))
  dsimp [F₁]
  linarith

theorem antitoneOn_F_neg (n : ℝ) (hn₀ : -1 < n) (hn₁ : n < 0) :
    AntitoneOn (F n) (Ioo 0 1) := by
  apply (strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun r hr => (F_hasDerivAt n r hn₁.ne hr
      (by have h := (B_bounds n r hn₁ hr).1; linarith)).continuousAt.continuousWithinAt) _).antitoneOn
  intro r hr
  have hr' : r ∈ Ioo (0 : ℝ) 1 := interior_subset hr
  rw [(F_hasDerivAt n r hn₁.ne hr'
    (by have h := (B_bounds n r hn₁ hr').1; linarith)).deriv]
  exact F₁_neg n r hn₀ hn₁ hr'

end D5.S3.Entropy.RenyiCombining.CachinNegativeBranch
