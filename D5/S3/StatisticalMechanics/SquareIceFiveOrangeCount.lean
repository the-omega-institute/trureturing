/- GID: D5/S3/StatisticalMechanics/SquareIceFiveOrangeCount
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/SquareIceFiveOrangeCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Five-orange height functions and finite downsets on the square lattice. -/

module

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Height functions of volume five reduce to five-point downsets of the ground height. -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.SquareIceFiveOrangeCount

/-- The initial height of a width-`ℓ` stack. -/
def ground (ℓ : ℕ) (v : ℤ × ℤ) : ℤ :=
  if v.1 < 0 then |v.1| + |v.2|
  else if v.1 < (ℓ : ℤ) then |v.1 + v.2|
  else |v.2 + (ℓ : ℤ) - 1| + |v.1 - (ℓ : ℤ) + 1|

/-- Finite perturbations above the initial height satisfying the ice rule. -/
def IsHeight (ℓ : ℕ) (h : ℤ × ℤ → ℤ) : Prop :=
  {v | h v ≠ ground ℓ v}.Finite ∧
  (∀ v, ground ℓ v ≤ h v) ∧
  ∀ v, |h v - h (v.1 + 1, v.2)| = 1 ∧ |h v - h (v.1, v.2 + 1)| = 1

/-- The number of removed oranges. -/
noncomputable def volume (ℓ : ℕ) (h : ℤ × ℤ → ℤ) : ℚ :=
  ∑ᶠ v, ((h v - ground ℓ v : ℤ) : ℚ) / 2

/-- The five-orange count of Govindarajan, Guttmann and Subramanyan. -/
def claim : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ →
    (Nat.card {h : ℤ × ℤ → ℤ // IsHeight ℓ h ∧ volume ℓ h = 5} : ℤ) =
      (ℓ.choose 5 : ℤ) + 10 * ℓ.choose 3 - 2 * ℓ.choose 2 + 36 * ℓ - 14

private def Adjacent (u v : ℤ × ℤ) : Prop :=
  |u.1 - v.1| + |u.2 - v.2| = 1

private theorem ground_nonneg (ℓ : ℕ) (v : ℤ × ℤ) : 0 ≤ ground ℓ v := by
  unfold ground
  split_ifs <;> positivity

private theorem ground_nearest (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (v : ℤ × ℤ) :
    (∀ i : ℤ, 0 ≤ i → i < ℓ → ground ℓ v ≤ |v.1 - i| + |v.2 + i|) ∧
    ∃ i : ℤ, 0 ≤ i ∧ i < ℓ ∧ ground ℓ v = |v.1 - i| + |v.2 + i| := by
  constructor
  · intro i hi hil
    unfold ground
    split_ifs <;> simp only [abs_eq_max_neg] <;> omega
  · by_cases hx : v.1 < 0
    · refine ⟨0, by omega, by omega, ?_⟩
      unfold ground
      simp only [ite_eq_left hx, sub_zero, add_zero]
    · by_cases hxl : v.1 < (ℓ : ℤ)
      · refine ⟨v.1, by omega, hxl, ?_⟩
        unfold ground
        simp only [ite_eq_right hx, ite_eq_left hxl, sub_self, abs_zero, zero_add]
        congr 1
        omega
      · refine ⟨(ℓ : ℤ) - 1, by omega, by omega, ?_⟩
        unfold ground
        simp only [ite_eq_right hx, ite_eq_right hxl]
        conv_lhs => rw [add_comm]
        congr 2 <;> omega

private theorem edge_difference (h : ℤ × ℤ → ℤ)
    (hh : ∀ v, |h v - h (v.1 + 1, v.2)| = 1 ∧
      |h v - h (v.1, v.2 + 1)| = 1) (u v : ℤ × ℤ) (huv : Adjacent u v) :
    |h u - h v| = 1 := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  have hc : (z = x + 1 ∧ w = y) ∨ (x = z + 1 ∧ y = w) ∨
      (z = x ∧ w = y + 1) ∨ (x = z ∧ y = w + 1) := by
    unfold Adjacent at huv
    dsimp only at huv
    simp only [abs_eq_max_neg] at huv
    omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hh (x, w)).1
  · simpa only [abs_sub_comm] using (hh (z, y)).1
  · exact (hh (z, y)).2
  · simpa only [abs_sub_comm] using (hh (x, w)).2

private theorem ground_edge (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (u v : ℤ × ℤ)
    (huv : Adjacent u v) : |ground ℓ u - ground ℓ v| = 1 := by
  rcases ground_nearest ℓ hℓ u with ⟨hu, i, hi, hil, hui⟩
  rcases ground_nearest ℓ hℓ v with ⟨hv, j, hj, hjl, hvj⟩
  have dist_step (a b c : ℤ) : |a - c| ≤ |b - c| + |a - b| := by
    simpa only [add_comm] using abs_sub_le a b c
  have add_step (a b c : ℤ) : |a + c| ≤ |b + c| + |a - b| := by
    simpa only [sub_neg_eq_add] using dist_step a b (-c)
  have h1 := hu j hj hjl
  have h2 := hv i hi hil
  have h3 := dist_step u.1 v.1 j
  have h4 := add_step u.2 v.2 j
  have h5 := dist_step v.1 u.1 i
  have h6 := add_step v.2 u.2 i
  have pu : ground ℓ u % 2 = (u.1 + u.2) % 2 := by
    rw [hui]
    simp only [abs_eq_max_neg]
    omega
  have pv : ground ℓ v % 2 = (v.1 + v.2) % 2 := by
    rw [hvj]
    simp only [abs_eq_max_neg]
    omega
  unfold Adjacent at huv
  rw [abs_sub_comm v.1 u.1] at h5
  rw [abs_sub_comm v.2 u.2] at h6
  have hb : ground ℓ u ≤ ground ℓ v + 1 ∧ ground ℓ v ≤ ground ℓ u + 1 := by
    omega
  clear hu hv h1 h2 h3 h4 h5 h6 hui hvj
  simp only [abs_eq_max_neg] at huv ⊢
  omega

private theorem ground_edges (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (v : ℤ × ℤ) :
    |ground ℓ v - ground ℓ (v.1 + 1, v.2)| = 1 ∧
    |ground ℓ v - ground ℓ (v.1, v.2 + 1)| = 1 := by
  constructor <;> apply ground_edge ℓ hℓ <;>
    unfold Adjacent <;> dsimp only <;> simp only [abs_eq_max_neg] <;> omega

private theorem height_even (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : ℤ × ℤ → ℤ)
    (hh : IsHeight ℓ h) (v : ℤ × ℤ) : (h v - ground ℓ v) % 2 = 0 := by
  obtain ⟨b, hb⟩ := (hh.1.image Prod.fst).exists_notMem
  have hb0 : h (b, v.2) = ground ℓ (b, v.2) := by
    by_contra hn
    exact hb ⟨(b, v.2), hn, rfl⟩
  have step (x : ℤ) :
      (h (x + 1, v.2) - ground ℓ (x + 1, v.2)) % 2 =
        (h (x, v.2) - ground ℓ (x, v.2)) % 2 := by
    have ha := (hh.2.2 (x, v.2)).1
    have hg := (ground_edges ℓ hℓ (x, v.2)).1
    simp only [abs_eq_max_neg] at ha hg
    omega
  have all (x : ℤ) :
      (h (b + x, v.2) - ground ℓ (b + x, v.2)) % 2 = 0 := by
    induction x using Int.induction_on with
    | zero => simp only [add_zero, hb0, sub_self, Int.zero_emod]
    | succ n ih =>
      have hs := step (b + n)
      have he : b + (↑n + 1) = b + ↑n + 1 := by omega
      rw [he]
      omega
    | pred n ih =>
      have hs := step (b + (-↑n - 1))
      have he : b + (-↑n - 1) + 1 = b + -↑n := by omega
      rw [he] at hs
      omega
  have hf := all (v.1 - b)
  have he : b + (v.1 - b) = v.1 := by omega
  rwa [he] at hf

private theorem excess_step (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : ℤ × ℤ → ℤ)
    (hh : IsHeight ℓ h) (u v : ℤ × ℤ) (huv : Adjacent u v) :
    h u - ground ℓ u - 2 ≤ h v - ground ℓ v := by
  have ha := edge_difference h hh.2.2 u v huv
  have hg := ground_edge ℓ hℓ u v huv
  simp only [abs_eq_max_neg] at ha hg
  omega

private theorem sum_le_volume (ℓ : ℕ) (h : ℤ × ℤ → ℤ) (hh : IsHeight ℓ h)
    (s : Finset (ℤ × ℤ)) :
    ∑ v ∈ s, ((h v - ground ℓ v : ℤ) : ℚ) / 2 ≤ volume ℓ h := by
  classical
  let t := hh.1.toFinset ∪ s
  unfold volume
  rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
  · apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    intro v _ _
    have hn : (0 : ℤ) ≤ h v - ground ℓ v := sub_nonneg.mpr (hh.2.1 v)
    have hq : (0 : ℚ) ≤ ((h v - ground ℓ v : ℤ) : ℚ) := by exact_mod_cast hn
    exact div_nonneg hq (by norm_num)
  · intro v hv
    apply Finset.mem_union_left
    apply hh.1.mem_toFinset.mpr
    intro he
    apply hv
    simp only [he, sub_self, Int.cast_zero, zero_div]

private theorem height_binary (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : ℤ × ℤ → ℤ)
    (hh : IsHeight ℓ h) (hvol : volume ℓ h = 5) (v : ℤ × ℤ) :
    h v = ground ℓ v ∨ h v = ground ℓ v + 2 := by
  classical
  have he := height_even ℓ hℓ h hh v
  have hn := hh.2.1 v
  by_contra hbad
  have hv : 4 ≤ h v - ground ℓ v := by omega
  have neighbours (w : ℤ × ℤ) (hw : Adjacent v w) :
      (1 : ℚ) ≤ ((h w - ground ℓ w : ℤ) : ℚ) / 2 := by
    have hs := excess_step ℓ hℓ h hh v w hw
    have hz : (2 : ℤ) ≤ h w - ground ℓ w := by omega
    have hq : (2 : ℚ) ≤ ((h w - ground ℓ w : ℤ) : ℚ) := by exact_mod_cast hz
    linarith
  have hc : (2 : ℚ) ≤ ((h v - ground ℓ v : ℤ) : ℚ) / 2 := by
    have hq : (4 : ℚ) ≤ ((h v - ground ℓ v : ℤ) : ℚ) := by exact_mod_cast hv
    linarith
  have hr := neighbours (v.1 + 1, v.2) (by
    unfold Adjacent; dsimp only; simp only [abs_eq_max_neg]; omega)
  have hl := neighbours (v.1 - 1, v.2) (by
    unfold Adjacent; dsimp only; simp only [abs_eq_max_neg]; omega)
  have hu := neighbours (v.1, v.2 + 1) (by
    unfold Adjacent; dsimp only; simp only [abs_eq_max_neg]; omega)
  have hd := neighbours (v.1, v.2 - 1) (by
    unfold Adjacent; dsimp only; simp only [abs_eq_max_neg]; omega)
  have hsum := sum_le_volume ℓ h hh
    {v, (v.1 + 1, v.2), (v.1 - 1, v.2), (v.1, v.2 + 1), (v.1, v.2 - 1)}
  have distinct : v ∉ ({(v.1 + 1, v.2), (v.1 - 1, v.2),
      (v.1, v.2 + 1), (v.1, v.2 - 1)} : Finset (ℤ × ℤ)) ∧
      (v.1 + 1, v.2) ∉ ({(v.1 - 1, v.2), (v.1, v.2 + 1),
        (v.1, v.2 - 1)} : Finset (ℤ × ℤ)) ∧
      (v.1 - 1, v.2) ∉ ({(v.1, v.2 + 1), (v.1, v.2 - 1)} : Finset (ℤ × ℤ)) ∧
      (v.1, v.2 + 1) ∉ ({(v.1, v.2 - 1)} : Finset (ℤ × ℤ)) := by
    rcases v with ⟨x, y⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [Finset.sum_insert distinct.1, Finset.sum_insert distinct.2.1,
    Finset.sum_insert distinct.2.2.1, Finset.sum_insert distinct.2.2.2,
    Finset.sum_singleton, hvol] at hsum
  linarith

private def IsDownset (ℓ : ℕ) (I : Finset (ℤ × ℤ)) : Prop :=
  ∀ u v, Adjacent u v → ground ℓ u + 1 = ground ℓ v → v ∈ I → u ∈ I

theorem result : claim := by
  sorry

end D5.S3.StatisticalMechanics.SquareIceFiveOrangeCount
