import OmegaBuild.Commands
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fintype.Fin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

compile_only_with_mathlib

/-! Omega original.

Balanced cuts give sharp finite-dimensional real L1 radius configurations.
-/

namespace ChordalL1

open Finset

variable {m : ℕ}

private def side (m : ℕ) (a : Fin (2 * m)) : ℝ :=
  if a.val < m then 0 else 1

private theorem side_dist_sum (a : Fin (2 * m)) :
    ∑ b : Fin (2 * m), |side m a - side m b| = (m : ℝ) := by
  have hcard : ((univ : Finset (Fin (2 * m))).filter (fun b => b.val < m)).card = m := by
    rw [Fin.card_filter_val_lt, min_eq_right]
    omega
  have hother : ((univ : Finset (Fin (2 * m))).filter (fun b => ¬ b.val < m)).card = m := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * m))))
      (fun b => b.val < m)
    rw [hcard, card_univ, Fintype.card_fin] at h
    omega
  by_cases h : a.val < m
  · have he (b : Fin (2 * m)) :
        |side m a - side m b| = if ¬ b.val < m then (1 : ℝ) else 0 := by
      by_cases hb : b.val < m <;> simp [side, h, hb]
    simp only [he, sum_ite, sum_const, sum_const_zero, nsmul_eq_mul, mul_one, hother]
  · have he (b : Fin (2 * m)) :
        |side m a - side m b| = if b.val < m then (1 : ℝ) else 0 := by
      by_cases hb : b.val < m <;> simp [side, h, hb]
    simp [he, hcard]

private theorem side_radius_sum (z : ℝ) :
    (m : ℝ) ≤ ∑ b : Fin (2 * m), |side m b - z| := by
  have hcard : ((univ : Finset (Fin (2 * m))).filter (fun b => b.val < m)).card = m := by
    rw [Fin.card_filter_val_lt, min_eq_right]
    omega
  have hother : ((univ : Finset (Fin (2 * m))).filter (fun b => ¬ b.val < m)).card = m := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * m))))
      (fun b => b.val < m)
    rw [hcard, card_univ, Fintype.card_fin] at h
    omega
  have he (b : Fin (2 * m)) :
      |side m b - z| = if b.val < m then |z| else |1 - z| := by
    by_cases hb : b.val < m <;> simp [side, hb]
  have h : (1 : ℝ) ≤ |z| + |1 - z| := by
    simpa only [show z + (1 - z) = 1 by ring, abs_one] using abs_add_le z (1 - z)
  simp only [he, sum_ite, sum_const, hcard, hother, nsmul_eq_mul]
  rw [← mul_add]
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m))

private theorem pair_perm {I : Type*} [DecidableEq I] {a b c d : I}
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm I, σ a = c ∧ σ b = d := by
  let τ := Equiv.swap a c
  have hτ : τ a = c := Equiv.swap_apply_left _ _
  have hne : τ b ≠ c := fun h => hab (τ.injective (hτ.trans h.symm))
  refine ⟨τ.trans (Equiv.swap (τ b) d), ?_, ?_⟩
  · rw [Equiv.trans_apply, hτ]
    exact Equiv.swap_apply_of_ne_of_ne hne.symm hcd
  · exact Equiv.swap_apply_left _ _

abbrev BalancedCutCoordinate (m : ℕ) := Equiv.Perm (Fin (2 * m))

private def cutSum (m : ℕ) (a b : Fin (2 * m)) : ℝ :=
  ∑ σ : BalancedCutCoordinate m, |side m (σ a) - side m (σ b)|

private theorem cutSum_eq {a b c d : Fin (2 * m)} (hab : a ≠ b) (hcd : c ≠ d) :
    cutSum m a b = cutSum m c d := by
  obtain ⟨τ, ht₁, ht₂⟩ := pair_perm hab hcd
  let e : Equiv.Perm (BalancedCutCoordinate m) :=
    ⟨fun σ => τ.trans σ, fun σ => τ.symm.trans σ,
      fun σ => by ext i; simp, fun σ => by ext i; simp⟩
  simpa [cutSum, e, ht₁, ht₂] using
    (Equiv.sum_comp e (fun σ => |side m (σ a) - side m (σ b)|)).symm

private theorem cutSum_value (hm : 0 < m) {a b : Fin (2 * m)} (hab : a ≠ b) :
    cutSum m a b = (Fintype.card (BalancedCutCoordinate m) : ℝ) * m / (2 * (m : ℝ) - 1) := by
  let d := cutSum m a b
  have hk : (1 : ℝ) < 2 * (m : ℝ) := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m from hm)
    linarith
  have hs (i : Fin (2 * m)) :
      ∑ j : Fin (2 * m), cutSum m i j = (2 * (m : ℝ) - 1) * d := by
    have he (j : Fin (2 * m)) : cutSum m i j = if j = i then 0 else d := by
      by_cases hj : j = i
      · subst j
        simp [cutSum]
      · simp [hj, d, cutSum_eq (Ne.symm hj) hab]
    rw [show (∑ j : Fin (2 * m), cutSum m i j) = ∑ j : Fin (2 * m), if j = i then 0 else d from
      sum_congr rfl fun j _ => he j]
    have hcard : ((univ : Finset (Fin (2 * m))).filter (fun j => ¬ j = i)).card + 1 = 2 * m := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * m))))
        (fun j => j = i)
      rw [show ((univ : Finset (Fin (2 * m))).filter (fun j => j = i)) = {i} by ext j; simp,
        card_singleton, card_univ, Fintype.card_fin, add_comm] at h
      exact h
    simp only [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    congr 1
    have hcardR : ((((univ : Finset (Fin (2 * m))).filter (fun j => ¬ j = i)).card : ℕ) : ℝ)
        + 1 = 2 * (m : ℝ) := by exact_mod_cast hcard
    linarith
  have hσ (i : Fin (2 * m)) (σ : BalancedCutCoordinate m) :
      (∑ j : Fin (2 * m), |side m (σ i) - side m (σ j)|) = (m : ℝ) :=
    (Equiv.sum_comp σ (fun j => |side m (σ i) - side m j|)).trans (side_dist_sum (σ i))
  have h := hs a
  unfold cutSum at h
  rw [sum_comm] at h
  simp_rw [hσ a] at h
  simp only [sum_const, card_univ, nsmul_eq_mul] at h
  exact (eq_div_iff (by linarith : 2 * (m : ℝ) - 1 ≠ 0)).2 (by linarith [mul_comm d (2 * (m : ℝ) - 1)])

/-- The balanced-cut configuration attains the finite L1 radius ratio at each
positive even cardinality. -/
theorem exists_balanced_l1_family (m : ℕ) (hm : 0 < m) :
    ∃ x : Fin (2 * m) → PiLp 1 (fun _ : BalancedCutCoordinate m => ℝ),
      (∀ a b, ‖x a - x b‖ ≤ 1) ∧
      ∀ y, ∃ a, 2 - 2 / (2 * (m : ℝ)) ≤ ‖(2 : ℝ) • x a - y‖ := by
  let P : ℝ := Fintype.card (BalancedCutCoordinate m)
  have hP : 0 < P := Nat.cast_pos.mpr Fintype.card_pos
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m from hm)
  let A : ℝ := (2 * (m : ℝ) - 1) / (P * m)
  have hAp : 0 < A := div_pos (by linarith) (mul_pos hP hmR)
  have hA := hAp.le
  let x (a : Fin (2 * m)) : PiLp 1 (fun _ : BalancedCutCoordinate m => ℝ) :=
    A • WithLp.toLp 1 (fun σ : BalancedCutCoordinate m => side m (σ a))
  have get (a : Fin (2 * m)) (σ : BalancedCutCoordinate m) : x a σ = A * side m (σ a) := rfl
  refine ⟨x, ?_, ?_⟩
  · intro a b
    by_cases hab : a = b
    · simp [hab]
    rw [PiLp.norm_eq_of_L1]
    simp only [PiLp.sub_apply, get, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hA,
      ← mul_sum]
    change A * cutSum m a b ≤ 1
    rw [cutSum_value hm hab]
    change ((2 * (m : ℝ) - 1) / (P * m)) * (P * m / (2 * (m : ℝ) - 1)) ≤ 1
    have hden : 2 * (m : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    exact le_rfl
  · intro y
    let T : ℝ := 2 - 2 / (2 * (m : ℝ))
    let : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
    obtain ⟨a, _, ha⟩ := exists_max_image univ
      (fun i => ‖(2 : ℝ) • x i - y‖) univ_nonempty
    refine ⟨a, ?_⟩
    have hpos : (0 : ℝ) < 2 * A := by positivity
    have hcoord (σ : BalancedCutCoordinate m) :
        2 * A * (m : ℝ) ≤ ∑ i : Fin (2 * m), |2 * x i σ - y σ| := by
      let t := y σ / (2 * A)
      have hterms (i : Fin (2 * m)) :
          2 * x i σ - y σ = (2 * A) * (side m (σ i) - t) := by
        rw [get, mul_sub, mul_div_cancel₀ _ hpos.ne']
        ring
      simp only [hterms, abs_mul, abs_of_nonneg hpos.le, ← mul_sum,
        Equiv.sum_comp σ (fun i => |side m i - t|)]
      exact mul_le_mul_of_nonneg_left (side_radius_sum t) hpos.le
    have hlo : P * (2 * A * (m : ℝ)) ≤ ∑ i : Fin (2 * m), ‖(2 : ℝ) • x i - y‖ := by
      rw [show P * (2 * A * (m : ℝ)) = ∑ _ : BalancedCutCoordinate m, 2 * A * (m : ℝ) by
        simp [P]]
      simp only [PiLp.norm_eq_of_L1, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul, Real.norm_eq_abs]
      rw [sum_comm]
      exact sum_le_sum fun i _ => hcoord i
    have hhi : (∑ i : Fin (2 * m), ‖(2 : ℝ) • x i - y‖) ≤
        (2 * (m : ℝ)) * ‖(2 : ℝ) • x a - y‖ := by
      convert sum_le_sum (s := (univ : Finset (Fin (2 * m)))) (fun i hi => ha i hi) using 1
      simp
    have he : P * (2 * A * (m : ℝ)) = (2 * (m : ℝ)) * T := by
      dsimp [A, T]
      field_simp
      <;> ring
    rw [he] at hlo
    exact le_of_mul_le_mul_left (hlo.trans hhi) (by positivity)

end ChordalL1
