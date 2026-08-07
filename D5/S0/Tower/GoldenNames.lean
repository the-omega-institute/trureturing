/- GID: D5/S0/Tower/GoldenNames
   generality: I
   mirror-B: D5/B/S0/Tower/GoldenNames
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bounded Zeckendorf strings have Fibonacci cardinality. -/

import D5.S0.Conventions.WDigits
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace D5.S0.Tower.GoldenNames

open D5.S0.Conventions

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- Length-`Q` golden names, represented by their occupied Fibonacci indices. -/
def GoldenName (Q : ℕ) :=
  {digits : WDigitString // ∀ k ∈ digits.1, k < Q + 2}

private theorem wdigits_bounded_of_lt_fib {Q n : ℕ} (hn : n < Nat.fib (Q + 2)) :
    ∀ k ∈ wdigits n, k < Q + 2 := by
  intro k hk
  have hk_mem : Nat.fib k ∈ (wdigits n).map Nat.fib := List.mem_map.mpr ⟨k, hk, rfl⟩
  have hk_le : Nat.fib k ≤ ((wdigits n).map Nat.fib).sum := List.le_sum_of_mem hk_mem
  rw [decode_wdigits] at hk_le
  by_contra hk_bound
  have hindex : Q + 2 ≤ k := Nat.le_of_not_gt hk_bound
  have hfib : Nat.fib (Q + 2) ≤ Nat.fib k := Nat.fib_mono hindex
  omega

private theorem sum_fib_lt_of_bounded {Q : ℕ} (name : GoldenName Q) :
    (name.1.1.map Nat.fib).sum < Nat.fib (Q + 2) := by
  apply name.1.2.sum_fib_lt
  intro k hk
  have hk_mem := List.mem_of_mem_head? hk
  rw [List.mem_append, List.mem_singleton] at hk_mem
  rcases hk_mem with hk_digits | rfl
  · exact name.2 k hk_digits
  · omega

/-- Bounded Zeckendorf encoding identifies golden names with an initial Fibonacci interval. -/
noncomputable def goldenNameEquiv (Q : ℕ) :
    Fin (Nat.fib (Q + 2)) ≃ GoldenName Q where
  toFun n := ⟨wEncoding n, wdigits_bounded_of_lt_fib n.2⟩
  invFun name := ⟨wEncoding.symm name.1, sum_fib_lt_of_bounded name⟩
  left_inv n := by
    apply Fin.ext
    exact wEncoding.symm_apply_apply n.1
  right_inv name := Subtype.ext (wEncoding.apply_symm_apply name.1)

noncomputable instance (Q : ℕ) : Fintype (GoldenName Q) :=
  Fintype.ofEquiv (Fin (Nat.fib (Q + 2))) (goldenNameEquiv Q)

/-- There are exactly `Fib (Q + 2)` length-`Q` golden names. -/
theorem golden_name_card (Q : ℕ) :
    Fintype.card (GoldenName Q) = Nat.fib (Q + 2) := by
  simpa using Fintype.card_congr (goldenNameEquiv Q).symm

private def fibValue (digits : List ℕ) : ℕ :=
  (digits.map Nat.fib).sum

private def previousFibValue (digits : List ℕ) : ℕ :=
  (digits.map fun k ↦ Nat.fib (k - 1)).sum

private theorem two_le_of_mem_goldenName {Q : ℕ} (name : GoldenName Q) {k : ℕ}
    (hk : k ∈ name.1.1) : 2 ≤ k := by
  have hall := List.isChain_iff_pairwise.1 name.1.2
  have hparts := List.pairwise_append.1 hall
  exact hparts.2.2 k hk 0 (by simp)

private theorem goldenRatio_pow_eq_fib_pair (k : ℕ) (hk : 2 ≤ k) :
    Real.goldenRatio ^ k =
      Real.goldenRatio * (Nat.fib k : ℝ) + (Nat.fib (k - 1) : ℝ) := by
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
    (Real.goldenRatio_mul_fib_succ_add_fib (k - 1)).symm

private theorem golden_power_sum_eq_aux (digits : List ℕ)
    (hmin : ∀ k ∈ digits, 2 ≤ k) :
    (digits.map fun k ↦ Real.goldenRatio ^ k).sum =
      Real.goldenRatio * (fibValue digits : ℝ) + (previousFibValue digits : ℝ) := by
  induction digits with
  | nil => simp [fibValue, previousFibValue]
  | cons k digits ih =>
      have hk : 2 ≤ k := hmin k (by simp)
      have htail : ∀ j ∈ digits, 2 ≤ j := by
        intro j hj
        exact hmin j (by simp [hj])
      simp only [List.map_cons, List.sum_cons]
      rw [goldenRatio_pow_eq_fib_pair k hk, ih htail]
      simp [fibValue, previousFibValue]
      ring

private theorem golden_power_sum_eq {Q : ℕ} (name : GoldenName Q) :
    (name.1.1.map fun k ↦ Real.goldenRatio ^ k).sum =
      Real.goldenRatio * (fibValue name.1.1 : ℝ) +
        (previousFibValue name.1.1 : ℝ) := by
  exact golden_power_sum_eq_aux name.1.1 fun _ hk ↦ two_le_of_mem_goldenName name hk

/-- The real value `sum d_i * phi^(-i)` of a length-`Q` golden name. -/
noncomputable def nameValue (Q : ℕ) (name : GoldenName Q) : ℝ :=
  (name.1.1.map fun k : ℕ ↦
    Real.goldenRatio ^ ((k : ℤ) - ((Q + 2 : ℕ) : ℤ))).sum

private theorem nameValue_eq_scaled (Q : ℕ) (name : GoldenName Q) :
    nameValue Q name =
      (name.1.1.map fun k ↦ Real.goldenRatio ^ k).sum /
        Real.goldenRatio ^ (Q + 2) := by
  unfold nameValue
  induction name.1.1 with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [zpow_natCast_sub_natCast₀ Real.goldenRatio_ne_zero, ih, add_div]

/-- Distinct admissible golden names have distinct real values. -/
theorem nameValue_injective (Q : ℕ) : Function.Injective (nameValue Q) := by
  intro left right hvalue
  rw [nameValue_eq_scaled, nameValue_eq_scaled] at hvalue
  have hpower :
      (left.1.1.map fun k ↦ Real.goldenRatio ^ k).sum =
        (right.1.1.map fun k ↦ Real.goldenRatio ^ k).sum :=
    (div_left_inj' (pow_ne_zero _ Real.goldenRatio_ne_zero)).mp hvalue
  rw [golden_power_sum_eq left, golden_power_sum_eq right] at hpower
  have hfib : fibValue left.1.1 = fibValue right.1.1 := by
    by_contra hne
    have hcast_ne :
        (fibValue left.1.1 : ℤ) ≠ (fibValue right.1.1 : ℤ) := by
      exact_mod_cast hne
    have hden :
        (fibValue left.1.1 : ℤ) - (fibValue right.1.1 : ℤ) ≠ 0 :=
      sub_ne_zero.mpr hcast_ne
    have hratio :
        Real.goldenRatio =
          (((previousFibValue right.1.1 : ℤ) - (previousFibValue left.1.1 : ℤ) : ℤ) : ℝ) /
            (((fibValue left.1.1 : ℤ) - (fibValue right.1.1 : ℤ) : ℤ) : ℝ) := by
      apply (eq_div_iff (Int.cast_ne_zero.mpr hden)).2
      push_cast
      nlinarith
    exact Real.goldenRatio_irrational.ne_rational
      ((previousFibValue right.1.1 : ℤ) - (previousFibValue left.1.1 : ℤ))
      ((fibValue left.1.1 : ℤ) - (fibValue right.1.1 : ℤ)) hratio
  apply Subtype.ext
  apply Subtype.ext
  calc
    left.1.1 = wdigits (fibValue left.1.1) := by
      apply wdigits_unique left.1.2
      rfl
    _ = wdigits (fibValue right.1.1) := by rw [hfib]
    _ = right.1.1 := by
      symm
      apply wdigits_unique right.1.2
      rfl

end D5.S0.Tower.GoldenNames
