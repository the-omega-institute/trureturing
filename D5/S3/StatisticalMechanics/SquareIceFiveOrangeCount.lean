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
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

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

private theorem ground_lipschitz (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (u v : ℤ × ℤ) :
    ground ℓ u ≤ ground ℓ v + |u.1 - v.1| + |u.2 - v.2| := by
  obtain ⟨_, i, hi, hil, hvi⟩ := ground_nearest ℓ hℓ v
  have hu := (ground_nearest ℓ hℓ u).1 i hi hil
  have hx := abs_sub_le u.1 v.1 i
  have hy := abs_sub_le u.2 v.2 (-i)
  simp only [sub_neg_eq_add] at hy
  omega

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

private theorem height_support (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : ℤ × ℤ → ℤ)
    (hh : IsHeight ℓ h) (hvol : volume ℓ h = 5) :
    hh.1.toFinset.card = 5 ∧ IsDownset ℓ hh.1.toFinset := by
  classical
  constructor
  · have he : volume ℓ h = (hh.1.toFinset.card : ℚ) := by
      unfold volume
      rw [finsum_eq_sum_of_support_subset _ (s := hh.1.toFinset) ?_]
      · calc
          _ = ∑ v ∈ hh.1.toFinset, (1 : ℚ) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hn := hh.1.mem_toFinset.mp hv
            rcases height_binary ℓ hℓ h hh hvol v with hz | hz
            · exact (hn hz).elim
            · rw [hz]
              norm_num
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      · intro v hv
        apply hh.1.mem_toFinset.mpr
        intro hz
        apply hv
        simp only [hz, sub_self, Int.cast_zero, zero_div]
    rw [hvol] at he
    exact_mod_cast he.symm
  · intro u v huv hground hv
    apply hh.1.mem_toFinset.mpr
    intro hu
    have hn := hh.1.mem_toFinset.mp hv
    have hb := height_binary ℓ hℓ h hh hvol v
    have hd := edge_difference h hh.2.2 u v huv
    simp only [abs_eq_max_neg] at hd
    change h u = ground ℓ u at hu
    change h v ≠ ground ℓ v at hn
    omega

private def lift (ℓ : ℕ) (I : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℤ :=
  ground ℓ v + if v ∈ I then 2 else 0

private theorem lift_edge (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) (u v : ℤ × ℤ) (huv : Adjacent u v) :
    |lift ℓ I u - lift ℓ I v| = 1 := by
  have hg := ground_edge ℓ hℓ u v huv
  have hsym : Adjacent v u := by
    unfold Adjacent at huv ⊢
    simpa only [abs_sub_comm] using huv
  by_cases hu : u ∈ I
  · by_cases hv : v ∈ I
    · unfold lift
      rw [ite_eq_left hu, ite_eq_left hv]
      simpa only [add_sub_add_right_eq_sub] using hg
    · have hn : ground ℓ v + 1 ≠ ground ℓ u := fun he => hv (hI v u hsym he hu)
      unfold lift
      rw [ite_eq_left hu, ite_eq_right hv]
      simp only [abs_eq_max_neg] at hg ⊢
      omega
  · by_cases hv : v ∈ I
    · have hn : ground ℓ u + 1 ≠ ground ℓ v := fun he => hu (hI u v huv he hv)
      unfold lift
      rw [ite_eq_right hu, ite_eq_left hv]
      simp only [abs_eq_max_neg] at hg ⊢
      omega
    · unfold lift
      simpa only [ite_eq_right hu, ite_eq_right hv, add_zero] using hg

private theorem lift_height (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) : IsHeight ℓ (lift ℓ I) := by
  refine ⟨I.finite_toSet.subset ?_, ?_, ?_⟩
  · intro v hv
    by_contra hn
    change v ∉ I at hn
    apply hv
    unfold lift
    simp only [ite_eq_right hn, add_zero]
  · intro v
    unfold lift
    split_ifs <;> omega
  · intro v
    constructor <;> apply lift_edge ℓ hℓ I hI <;>
      unfold Adjacent <;> dsimp only <;> simp only [abs_eq_max_neg] <;> omega

private theorem lift_volume (ℓ : ℕ) (I : Finset (ℤ × ℤ)) :
    volume ℓ (lift ℓ I) = (I.card : ℚ) := by
  unfold volume
  rw [finsum_eq_sum_of_support_subset _ (s := I) ?_]
  · calc
      _ = ∑ v ∈ I, (1 : ℚ) := by
        apply Finset.sum_congr rfl
        intro v hv
        unfold lift
        simp only [ite_eq_left hv]
        norm_num
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  · intro v hv
    by_contra hn
    change v ∉ I at hn
    apply hv
    unfold lift
    simp only [ite_eq_right hn, add_zero, sub_self, Int.cast_zero, zero_div]

private noncomputable def heightEquiv (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    {h : ℤ × ℤ → ℤ // IsHeight ℓ h ∧ volume ℓ h = 5} ≃
      {I : Finset (ℤ × ℤ) // I.card = 5 ∧ IsDownset ℓ I} where
  toFun h := ⟨h.property.1.1.toFinset, height_support ℓ hℓ h h.property.1 h.property.2⟩
  invFun I := ⟨lift ℓ I, lift_height ℓ hℓ I I.property.2, by
    rw [lift_volume, I.property.1]; norm_num⟩
  left_inv h := by
    apply Subtype.ext
    funext v
    change lift ℓ h.property.1.1.toFinset v = h.val v
    unfold lift
    by_cases hv : h.val v = ground ℓ v
    · have hn : v ∉ h.property.1.1.toFinset := by
        intro hm
        exact (h.property.1.1.mem_toFinset.mp hm) hv
      rw [ite_eq_right hn]
      omega
    · rw [ite_eq_left (h.property.1.1.mem_toFinset.mpr hv)]
      rcases height_binary ℓ hℓ h h.property.1 h.property.2 v with he | he
      · exact (hv he).elim
      · omega
  right_inv I := by
    apply Subtype.ext
    ext v
    change v ∈ (lift_height ℓ hℓ I.val I.property.2).1.toFinset ↔ v ∈ I.val
    rw [Set.Finite.mem_toFinset]
    change lift ℓ I.val v ≠ ground ℓ v ↔ v ∈ I.val
    unfold lift
    by_cases hv : v ∈ I.val
    · rw [ite_eq_left hv]
      exact ⟨fun _ => hv, fun _ => by omega⟩
    · rw [ite_eq_right hv]
      exact ⟨fun hn => (hn (by omega)).elim, fun hm => (hv hm).elim⟩

private theorem geodesic_mem (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) (u v : ℤ × ℤ)
    (he : ground ℓ u + |u.1 - v.1| + |u.2 - v.2| = ground ℓ v)
    (hv : v ∈ I) : u ∈ I := by
  suffices hall : ∀ n : ℕ, ∀ u v : ℤ × ℤ,
      (|u.1 - v.1| + |u.2 - v.2|).toNat = n →
      ground ℓ u + |u.1 - v.1| + |u.2 - v.2| = ground ℓ v → v ∈ I → u ∈ I by
    exact hall _ u v rfl he hv
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hn he hv
    by_cases huv : u = v
    · simpa only [huv] using hv
    have next : ∃ w : ℤ × ℤ, Adjacent v w ∧
        |u.1 - w.1| + |u.2 - w.2| + 1 = |u.1 - v.1| + |u.2 - v.2| := by
      by_cases hx : u.1 < v.1
      · refine ⟨(v.1 - 1, v.2), ?_, ?_⟩ <;>
          (try unfold Adjacent) <;> dsimp only <;> simp only [abs_eq_max_neg] <;> omega
      · by_cases hxr : v.1 < u.1
        · refine ⟨(v.1 + 1, v.2), ?_, ?_⟩ <;>
            (try unfold Adjacent) <;> dsimp only <;> simp only [abs_eq_max_neg] <;> omega
        · have hy : u.2 ≠ v.2 := by
            intro hy
            apply huv
            exact Prod.ext (by omega) hy
          by_cases hyl : u.2 < v.2
          · refine ⟨(v.1, v.2 - 1), ?_, ?_⟩ <;>
              (try unfold Adjacent) <;> dsimp only <;> simp only [abs_eq_max_neg] <;> omega
          · refine ⟨(v.1, v.2 + 1), ?_, ?_⟩ <;>
              (try unfold Adjacent) <;> dsimp only <;> simp only [abs_eq_max_neg] <;> omega
    obtain ⟨w, hw, hd⟩ := next
    have hl := ground_lipschitz ℓ hℓ w u
    rw [abs_sub_comm w.1 u.1, abs_sub_comm w.2 u.2] at hl
    have hg := ground_edge ℓ hℓ v w hw
    have hwg : ground ℓ w + 1 = ground ℓ v := by
      simp only [abs_eq_max_neg] at hg
      omega
    have hwi : w ∈ I := hI w v (by
      unfold Adjacent at hw ⊢
      simpa only [abs_sub_comm] using hw) hwg hv
    apply ih (|u.1 - w.1| + |u.2 - w.2|).toNat (by
      have ha := abs_nonneg (u.1 - w.1)
      have hb := abs_nonneg (u.2 - w.2)
      omega) u w rfl (by omega) hwi

private theorem rectangle_bound (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) (v : ℤ × ℤ) (hv : v ∈ I) (i : ℤ)
    (hi : 0 ≤ i) (hil : i < ℓ) (hvi : ground ℓ v = |v.1 - i| + |v.2 + i|) :
    (|v.1 - i| + 1) * (|v.2 + i| + 1) ≤ (I.card : ℤ) := by
  let r := (Finset.Icc (min i v.1) (max i v.1)).product
    (Finset.Icc (min (-i) v.2) (max (-i) v.2))
  have hs : r ⊆ I := by
    intro u hu
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hu
    obtain ⟨hxa, hxb⟩ := Finset.mem_Icc.mp hx
    obtain ⟨hya, hyb⟩ := Finset.mem_Icc.mp hy
    have segment (a b c : ℤ) (ha : min a c ≤ b) (hb : b ≤ max a c) :
        |b - a| + |b - c| = |c - a| := by
      simp only [abs_eq_max_neg] at *
      omega
    have hdx := segment i u.1 v.1 hxa hxb
    have hdy := segment (-i) u.2 v.2 hya hyb
    simp only [sub_neg_eq_add] at hdy
    have hg := (ground_nearest ℓ hℓ u).1 i hi hil
    have hl := ground_lipschitz ℓ hℓ v u
    rw [abs_sub_comm v.1 u.1, abs_sub_comm v.2 u.2] at hl
    apply geodesic_mem ℓ hℓ I hI u v (by omega) hv
  have hc : (r.card : ℤ) ≤ I.card := by exact_mod_cast Finset.card_le_card hs
  have he : (r.card : ℤ) = (|v.1 - i| + 1) * (|v.2 + i| + 1) := by
    dsimp only [r]
    rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul,
      Int.card_Icc_of_le (a := min i v.1) (b := max i v.1) (by omega),
      Int.card_Icc_of_le (a := min (-i) v.2) (b := max (-i) v.2) (by omega)]
    have hx : max i v.1 + 1 - min i v.1 = |v.1 - i| + 1 := by
      have hm := max_sub_min_eq_abs i v.1
      omega
    have hy : max (-i) v.2 + 1 - min (-i) v.2 = |v.2 + i| + 1 := by
      have hm := max_sub_min_eq_abs (-i) v.2
      rw [sub_neg_eq_add] at hm
      omega
    rw [hx, hy]
  omega

private theorem rank_bound (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) (v : ℤ × ℤ) (hv : v ∈ I) : ground ℓ v < I.card := by
  obtain ⟨_, i, hi, hil, hvi⟩ := ground_nearest ℓ hℓ v
  have hb := rectangle_bound ℓ hℓ I hI v hv i hi hil hvi
  have hx := abs_nonneg (v.1 - i)
  have hy := abs_nonneg (v.2 + i)
  nlinarith [mul_nonneg hx hy]

private theorem positive_triangle (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) (hcard : I.card = 5) (v : ℤ × ℤ) (hv : v ∈ I)
    (i : ℤ) (hi : 0 ≤ i) (hil : i + 2 < ℓ) : ¬(i + 2 ≤ v.1 ∧ -i ≤ v.2) := by
  intro hpos
  have hgv : ground ℓ v = v.1 + v.2 := by
    unfold ground
    split_ifs <;> simp only [abs_eq_max_neg] <;> omega
  let t : Finset (ℤ × ℤ) := {(i, -i), (i+1, -i-1), (i+2, -i-2), (i+1, -i), (i+2, -i-1), (i+2, -i)}
  have hs : t ⊆ I := by
    intro u hu
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply geodesic_mem ℓ hℓ I hI _ v ?_ hv
      rw [hgv]
      unfold ground
      dsimp only
      split_ifs <;> simp only [abs_eq_max_neg] <;> omega
  have hc : t.card = 6 := by
    have inj : Function.Injective (fun p : ℤ × ℤ => (p.1 + i, p.2 - i)) := by
      intro p q hpq
      apply Prod.ext <;> have h1 := congrArg Prod.fst hpq <;>
        have h2 := congrArg Prod.snd hpq <;> dsimp only at h1 h2 <;> omega
    have hm : t = ({(0,0), (1,-1), (2,-2), (1,0), (2,-1), (2,0)} :
        Finset (ℤ × ℤ)).image (fun p => (p.1 + i, p.2 - i)) := by
      simp only [Finset.image_insert, Finset.image_singleton, t]
      ext p
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      omega
    rw [hm, Finset.card_image_of_injective _ inj]
    decide
  have hn := Finset.card_le_card hs
  omega

private theorem negative_triangle (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (I : Finset (ℤ × ℤ))
    (hI : IsDownset ℓ I) (hcard : I.card = 5) (v : ℤ × ℤ) (hv : v ∈ I)
    (i : ℤ) (hi : 0 ≤ i) (hil : i + 2 < ℓ) : ¬(v.1 ≤ i ∧ v.2 ≤ -i - 2) := by
  intro hpos
  have hgv : ground ℓ v = -v.1 - v.2 := by
    unfold ground
    split_ifs <;> simp only [abs_eq_max_neg] <;> omega
  let t : Finset (ℤ × ℤ) := {(i, -i), (i+1, -i-1), (i+2, -i-2), (i, -i-1), (i+1, -i-2), (i, -i-2)}
  have hs : t ⊆ I := by
    intro u hu
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply geodesic_mem ℓ hℓ I hI _ v ?_ hv
      rw [hgv]
      unfold ground
      dsimp only
      split_ifs <;> simp only [abs_eq_max_neg] <;> omega
  have hc : t.card = 6 := by
    have inj : Function.Injective (fun p : ℤ × ℤ => (p.1 + i, p.2 - i)) := by
      intro p q hpq
      apply Prod.ext <;> have h1 := congrArg Prod.fst hpq <;>
        have h2 := congrArg Prod.snd hpq <;> dsimp only at h1 h2 <;> omega
    have hm : t = ({(0,0), (1,-1), (2,-2), (0,-1), (1,-2), (0,-2)} :
        Finset (ℤ × ℤ)).image (fun p => (p.1 + i, p.2 - i)) := by
      simp only [Finset.image_insert, Finset.image_singleton, t]
      ext p
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
      omega
    rw [hm, Finset.card_image_of_injective _ inj]
    decide
  have hn := Finset.card_le_card hs
  omega

private def EndVertex (ℓ : ℕ) (v : ℤ × ℤ) : Prop :=
  (-4 ≤ v.1 ∧ v.1 ≤ -2 ∧ v.2 = 0) ∨
  (v.1 = 0 ∧ 2 ≤ v.2 ∧ v.2 ≤ 4) ∨
  ((ℓ : ℤ) + 1 ≤ v.1 ∧ v.1 ≤ (ℓ : ℤ) + 3 ∧ v.2 = 1 - (ℓ : ℤ)) ∨
  (v.1 = (ℓ : ℤ) - 1 ∧ -(ℓ : ℤ) - 3 ≤ v.2 ∧ v.2 ≤ -(ℓ : ℤ) - 1) ∨
  v = (-1, 1) ∨ v = ((ℓ : ℤ), -(ℓ : ℤ)) ∨
  v = (-1, -1) ∨ v = (1, 1) ∨
  v = ((ℓ : ℤ), 2 - (ℓ : ℤ)) ∨ v = ((ℓ : ℤ) - 2, -(ℓ : ℤ))

set_option maxHeartbeats 2000000 in
-- The twenty-two offset cases normalize absolute values and endpoint inequalities.
private theorem vertex_classification (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    (I : Finset (ℤ × ℤ)) (hI : IsDownset ℓ I) (hcard : I.card = 5)
    (v : ℤ × ℤ) (hv : v ∈ I) : ground ℓ v ≤ 1 ∨ EndVertex ℓ v := by
  have hwidth : 1 ≤ ℓ := by omega
  obtain ⟨hmin, i, hi, hil, hvi⟩ := ground_nearest ℓ hwidth v
  have hbound := rectangle_bound ℓ hwidth I hI v hv i hi hil hvi
  have hrank := rank_bound ℓ hwidth I hI v hv
  rw [hcard] at hbound hrank
  norm_num at hbound hrank
  generalize hdx : v.1 - i = dx at hvi hbound
  generalize hdy : v.2 + i = dy at hvi hbound
  have hdx_range : -4 ≤ dx ∧ dx ≤ 4 := by
    simp only [abs_eq_max_neg] at hvi
    omega
  have hdy_range : -4 ≤ dy ∧ dy ≤ 4 := by
    simp only [abs_eq_max_neg] at hvi
    omega
  have hshape : dx = 0 ∨ dy = 0 ∨ (dx = 1 ∨ dx = -1) ∧ (dy = 1 ∨ dy = -1) := by
    have ha := abs_nonneg dx
    have hb := abs_nonneg dy
    by_cases hxa : |dx| = 0
    · left
      exact abs_eq_zero.mp hxa
    · by_cases hya : |dy| = 0
      · right; left
        exact abs_eq_zero.mp hya
      · have hax : 1 ≤ |dx| := by omega
        have hby : 1 ≤ |dy| := by omega
        have hp := mul_nonneg (by omega : 0 ≤ |dx| - 1) (by omega : 0 ≤ |dy| - 1)
        have hs : 2 * (|dx| + |dy|) ≤ 5 := by nlinarith
        have heq : |dx| = 1 ∧ |dy| = 1 := by omega
        right; right
        simp only [abs_eq_max_neg] at heq
        omega
  have lmin : 0 < i → |dx| + |dy| ≤ |dx + 1| + |dy - 1| := by
    intro hl
    have hm := hmin (i - 1) (by omega) (by omega)
    have hx : v.1 - (i - 1) = dx + 1 := by omega
    have hy : v.2 + (i - 1) = dy - 1 := by omega
    rw [hx, hy, hvi] at hm
    exact hm
  have rmin : i + 1 < ℓ → |dx| + |dy| ≤ |dx - 1| + |dy + 1| := by
    intro hl
    have hm := hmin (i + 1) (by omega) hl
    have hx : v.1 - (i + 1) = dx - 1 := by omega
    have hy : v.2 + (i + 1) = dy + 1 := by omega
    rw [hx, hy, hvi] at hm
    exact hm
  have lrect : 0 < i → |dx + 1| + |dy - 1| = |dx| + |dy| →
      (|dx + 1| + 1) * (|dy - 1| + 1) ≤ 5 := by
    intro hl he
    have hx : v.1 - (i - 1) = dx + 1 := by omega
    have hy : v.2 + (i - 1) = dy - 1 := by omega
    have hm := rectangle_bound ℓ hwidth I hI v hv (i - 1) (by omega) (by omega)
      (by rw [hx, hy, he]; exact hvi)
    rwa [hx, hy, hcard] at hm
  have rrect : i + 1 < ℓ → |dx - 1| + |dy + 1| = |dx| + |dy| →
      (|dx - 1| + 1) * (|dy + 1| + 1) ≤ 5 := by
    intro hl he
    have hx : v.1 - (i + 1) = dx - 1 := by omega
    have hy : v.2 + (i + 1) = dy + 1 := by omega
    have hm := rectangle_bound ℓ hwidth I hI v hv (i + 1) (by omega) hl
      (by rw [hx, hy, he]; exact hvi)
    rwa [hx, hy, hcard] at hm
  have no_pos (j : ℤ) : ¬(0 ≤ j ∧ j + 2 < ℓ ∧ j + 2 ≤ v.1 ∧ -j ≤ v.2) := by
    rintro ⟨hj, hjl, hx, hy⟩
    exact positive_triangle ℓ hwidth I hI hcard v hv j hj hjl ⟨hx, hy⟩
  have no_neg (j : ℤ) : ¬(0 ≤ j ∧ j + 2 < ℓ ∧ v.1 ≤ j ∧ v.2 ≤ -j - 2) := by
    rintro ⟨hj, hjl, hx, hy⟩
    exact negative_triangle ℓ hwidth I hI hcard v hv j hj hjl ⟨hx, hy⟩
  have p0 : ¬(i + 2 < ℓ ∧ 2 ≤ dx ∧ 0 ≤ dy) := by
    have hp := no_pos i
    omega
  have p1 : ¬(1 ≤ i ∧ i + 1 < ℓ ∧ 1 ≤ dx ∧ 1 ≤ dy) := by
    have hp := no_pos (i - 1)
    omega
  have p2 : ¬(2 ≤ i ∧ 0 ≤ dx ∧ 2 ≤ dy) := by
    have hp := no_pos (i - 2)
    omega
  have n0 : ¬(i + 2 < ℓ ∧ dx ≤ 0 ∧ dy ≤ -2) := by
    have hp := no_neg i
    omega
  have n1 : ¬(1 ≤ i ∧ i + 1 < ℓ ∧ dx ≤ -1 ∧ dy ≤ -1) := by
    have hp := no_neg (i - 1)
    omega
  have n2 : ¬(2 ≤ i ∧ dx ≤ -2 ∧ dy ≤ 0) := by
    have hp := no_neg (i - 2)
    omega
  unfold EndVertex
  simp only [Prod.ext_iff]
  obtain ⟨dxlo, dxhi⟩ := hdx_range
  obtain ⟨dylo, dyhi⟩ := hdy_range
  clear hmin no_pos no_neg hwidth hrank hbound
  rcases hshape with hzero | hzero | ⟨hxx, hyy⟩
  · cases hzero
    interval_cases dy <;> norm_num at lmin <;> norm_num at rmin <;>
      norm_num at lrect <;> norm_num at rrect <;> norm_num at hvi <;>
      norm_num at p0 p1 p2 n0 n1 n2 <;> omega
  · cases hzero
    interval_cases dx <;> norm_num at lmin <;> norm_num at rmin <;>
      norm_num at lrect <;> norm_num at rrect <;> norm_num at hvi <;>
      norm_num at p0 p1 p2 n0 n1 n2 <;> omega
  · rcases hxx with rfl | rfl <;> rcases hyy with rfl | rfl <;>
      norm_num at lmin <;> norm_num at rmin <;> norm_num at lrect <;>
      norm_num at rrect <;> norm_num at hvi <;> norm_num at p0 p1 p2 n0 n1 n2 <;> omega

private noncomputable def vertices (ℓ : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc (-4 : ℤ) ((ℓ : ℤ) + 3)).product
    (Finset.Icc (-(ℓ : ℤ) - 3) 4)).filter (fun v => ground ℓ v ≤ 1 ∨ EndVertex ℓ v)

private abbrev FiniteDownsets (ℓ : ℕ) :=
  {J : ↥((vertices ℓ).powersetCard 5) // IsDownset ℓ J.val}

private noncomputable def finiteEquiv (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    {I : Finset (ℤ × ℤ) // I.card = 5 ∧ IsDownset ℓ I} ≃
      {J : ↥((vertices ℓ).powersetCard 5) // IsDownset ℓ J.val} where
  toFun I := ⟨⟨I.val, Finset.mem_powersetCard.mpr ⟨by
    classical
    intro v hv
    unfold vertices
    apply Finset.mem_filter.mpr
    refine ⟨?_, vertex_classification ℓ hℓ I I.property.2 I.property.1 v hv⟩
    have hr := rank_bound ℓ (by omega) I I.property.2 v hv
    obtain ⟨_, i, hi, hil, he⟩ := ground_nearest ℓ (by omega) v
    rw [I.property.1] at hr
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;>
      simp only [abs_eq_max_neg] at he <;> omega,
    I.property.1⟩⟩, I.property.2⟩
  invFun J := ⟨J.val.val, (Finset.mem_powersetCard.mp J.val.property).2, J.property⟩
  left_inv I := by apply Subtype.ext; rfl
  right_inv J := by apply Subtype.ext; apply Subtype.ext; rfl

private abbrev Choices (n k : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard k)
private abbrev RemainingPatterns (ℓ : ℕ) :=
  (Fin (ℓ - 1) × Fin 2 × Choices (ℓ - 2) 2) ⊕
  (Fin 4 × Choices (ℓ - 1) 3) ⊕
  (Fin 2 × Choices (ℓ - 1) 2) ⊕
  (Fin (ℓ - 1) × Fin (ℓ - 2)) ⊕
  (Fin (ℓ - 2) × Fin 4) ⊕
  (Fin 2 × Fin (ℓ - 2) × Fin 4) ⊕
  (Fin 2 × Fin (ℓ - 2) × Fin 4) ⊕
  (Fin (ℓ - 2) × Fin 4) ⊕
  Fin 12 ⊕ Fin 4 ⊕ (Fin 2 × Fin (ℓ + 1)) ⊕
  (Fin 4 × Fin ℓ) ⊕ Fin 2 ⊕ (Fin 4 × Choices (ℓ - 1) 2) ⊕
  (Fin 4 × Fin (ℓ + 3))
private abbrev OtherPatterns (ℓ : ℕ) := Fin 4 ⊕ RemainingPatterns ℓ
private abbrev Patterns (ℓ : ℕ) := Choices ℓ 5 ⊕ OtherPatterns ℓ
private theorem patterns_card (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    (Nat.card (Patterns ℓ) : ℤ) =
      (ℓ.choose 5 : ℤ) + 10 * ℓ.choose 3 - 2 * ℓ.choose 2 + 36 * ℓ - 14 := by
  have hsub1 : (ℓ - 1 : ℕ) + 1 = ℓ := by omega
  have hsub2 : (ℓ - 2 : ℕ) + 1 = ℓ - 1 := by omega
  have hsub3 : (ℓ - 1 : ℕ) - 1 = ℓ - 2 := by omega
  have ha := Nat.add_one_mul_choose_eq (ℓ - 2) 2
  rw [hsub2] at ha
  have hb := Nat.choose_succ_right_eq (ℓ - 1) 1
  rw [Nat.choose_one_right, hsub3] at hb
  have hc := Nat.choose_succ_succ (ℓ - 1) 2
  have hd := Nat.choose_succ_succ (ℓ - 1) 1
  change (ℓ - 1 + 1).choose 3 = (ℓ - 1).choose 2 + (ℓ - 1).choose 3 at hc
  change (ℓ - 1 + 1).choose 2 = (ℓ - 1).choose 1 + (ℓ - 1).choose 2 at hd
  rw [hsub1] at hc hd
  rw [Nat.choose_one_right] at hd
  have haZ : ((ℓ - 1 : ℕ) : ℤ) * ((ℓ - 2).choose 2 : ℤ) =
      ((ℓ - 1).choose 3 : ℤ) * 3 := by exact_mod_cast ha
  have hbZ : ((ℓ - 1).choose 2 : ℤ) * 2 =
      ((ℓ - 1 : ℕ) : ℤ) * ((ℓ - 2 : ℕ) : ℤ) := by exact_mod_cast hb
  have hcZ : (ℓ.choose 3 : ℤ) = ((ℓ - 1).choose 2 : ℤ) + (ℓ - 1).choose 3 := by
    exact_mod_cast hc
  have hdZ : (ℓ.choose 2 : ℤ) = ((ℓ - 1 : ℕ) : ℤ) + (ℓ - 1).choose 2 := by
    exact_mod_cast hd
  have hs1 : ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by omega
  have hs2 : ((ℓ - 2 : ℕ) : ℤ) = (ℓ : ℤ) - 2 := by omega
  unfold Patterns OtherPatterns RemainingPatterns Choices
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hs1, hs2]
  rw [hs1] at haZ hbZ hdZ
  rw [hs2] at hbZ
  nlinarith
private theorem ground_zero (ℓ : ℕ) (v : ℤ × ℤ) :
    ground ℓ v = 0 ↔ 0 ≤ v.1 ∧ v.1 < ℓ ∧ v.2 = -v.1 := by
  unfold ground
  split_ifs <;> simp only [abs_eq_max_neg] <;> omega
private def zeroEquiv (ℓ : ℕ) : {v // ground ℓ v = 0} ≃ Fin ℓ where
  toFun v := ⟨v.val.1.toNat, by
    have hz := (ground_zero ℓ v.val).mp v.property
    omega⟩
  invFun i := ⟨((i.val : ℤ), -(i.val : ℤ)), (ground_zero ℓ _).mpr
    ⟨by dsimp only; omega, by dsimp only; exact_mod_cast i.isLt, rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    have hz := (ground_zero ℓ v.val).mp v.property
    apply Prod.ext <;> dsimp only <;> omega
  right_inv i := by apply Fin.ext; dsimp only; omega
private def zeroFinsetsEquiv (ℓ : ℕ) :
    {I : Finset (ℤ × ℤ) // ∀ v ∈ I, ground ℓ v = 0} ≃ Finset (Fin ℓ) :=
  (Equiv.finsetSubtypeComm (fun v => ground ℓ v = 0)).symm.trans
    (Equiv.finsetCongr (zeroEquiv ℓ))
private theorem zeroFinsets_card (ℓ : ℕ)
    (I : {I : Finset (ℤ × ℤ) // ∀ v ∈ I, ground ℓ v = 0}) :
    (zeroFinsetsEquiv ℓ I).card = I.val.card := by
  unfold zeroFinsetsEquiv
  simp only [Equiv.trans_apply, Equiv.finsetCongr_apply, Finset.card_map,
    Equiv.finsetSubtypeComm_symm_apply, Finset.card_attach]
private def zeroOnly (ℓ : ℕ) (J : FiniteDownsets ℓ) : Prop :=
  ∀ v ∈ J.val.val, ground ℓ v = 0

private noncomputable def lowEquiv (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    {J : FiniteDownsets ℓ // zeroOnly ℓ J} ≃ Choices ℓ 5 where
  toFun J := ⟨zeroFinsetsEquiv ℓ ⟨J.val.val.val, J.property⟩,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      rw [zeroFinsets_card]
      exact (Finset.mem_powersetCard.mp J.val.val.property).2⟩⟩
  invFun S := by
    let T := (zeroFinsetsEquiv ℓ).symm S.val
    have hc : T.val.card = 5 := by
      have hz := zeroFinsets_card ℓ T
      have he : zeroFinsetsEquiv ℓ T = S.val := Equiv.apply_symm_apply _ _
      rw [he] at hz
      have hs := (Finset.mem_powersetCard.mp S.property).2
      omega
    have hd : IsDownset ℓ T.val := by
      intro u v _ he hv
      have hgv := T.property v hv
      have hgu : 0 ≤ ground ℓ u := by unfold ground; split_ifs <;> positivity
      omega
    exact ⟨finiteEquiv ℓ hℓ ⟨T.val, hc, hd⟩, T.property⟩
  left_inv J := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change ((zeroFinsetsEquiv ℓ).symm
      (zeroFinsetsEquiv ℓ ⟨J.val.val.val, J.property⟩)).val = J.val.val.val
    rw [Equiv.symm_apply_apply]
  right_inv S := by
    apply Subtype.ext
    change zeroFinsetsEquiv ℓ ((zeroFinsetsEquiv ℓ).symm S.val) = S.val
    exact Equiv.apply_symm_apply _ _

private def rayPoint (ℓ : ℕ) (d : Fin 4) (k : ℕ) : ℤ × ℤ :=
  if d.val = 0 then (-(k : ℤ), 0)
  else if d.val = 1 then (0, (k : ℤ))
  else if d.val = 2 then ((ℓ : ℤ) - 1 + k, 1 - (ℓ : ℤ))
  else ((ℓ : ℤ) - 1, 1 - (ℓ : ℤ) - k)
private def ray4 (ℓ : ℕ) (d : Fin 4) : Finset (ℤ × ℤ) :=
  (Finset.range 5).image (rayPoint ℓ d)
private theorem ray4_card (ℓ : ℕ) (d : Fin 4) : (ray4 ℓ d).card = 5 := by
  unfold ray4
  rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro a b he
  unfold rayPoint at he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  fin_cases d <;> norm_num at hx hy <;> omega
private theorem ray4_downset (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (d : Fin 4) : IsDownset ℓ (ray4 ℓ d) := by
  intro u v hadj he hv
  unfold ray4 at hv ⊢
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
  have hklt : k < 5 := Finset.mem_range.mp hk
  have hgu : 0 ≤ ground ℓ u := by unfold ground; split_ifs <;> positivity
  let p := k - 1
  unfold rayPoint at hadj he ⊢
  fin_cases d
  all_goals
    norm_num at hadj he
    unfold ground at he
    split_ifs at he <;> simp only [abs_eq_max_neg] at he
    all_goals first
      | omega
      | refine Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr (by dsimp only [p]; omega), ?_⟩
        apply Prod.ext <;> norm_num <;> (try dsimp only [p])
        all_goals
          unfold Adjacent at hadj
          simp only [abs_eq_max_neg] at hadj
          omega
private theorem ray4_tip (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (d : Fin 4) :
    rayPoint ℓ d 4 ∈ ray4 ℓ d ∧ ground ℓ (rayPoint ℓ d 4) = 4 := by
  constructor
  · unfold ray4
    exact Finset.mem_image.mpr ⟨4, by decide, rfl⟩
  · unfold rayPoint ground
    fin_cases d <;> norm_num <;> (try split_ifs) <;> simp only [abs_eq_max_neg] <;> omega
private theorem ray4_injective (ℓ : ℕ) (hℓ : 3 ≤ ℓ) : Function.Injective (ray4 ℓ) := by
  intro d e he
  have hm := (ray4_tip ℓ hℓ d).1
  rw [he] at hm
  unfold ray4 at hm
  obtain ⟨k, hk, hp⟩ := Finset.mem_image.mp hm
  have hklt : k < 5 := Finset.mem_range.mp hk
  have hx := congrArg Prod.fst hp
  have hy := congrArg Prod.snd hp
  unfold rayPoint at hx hy
  fin_cases d <;> fin_cases e <;> try rfl
  all_goals norm_num at hx
  all_goals norm_num at hy
  all_goals omega

private noncomputable def ray4Downset (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (d : Fin 4) :
    {J : FiniteDownsets ℓ // ¬zeroOnly ℓ J} :=
  ⟨finiteEquiv ℓ hℓ ⟨ray4 ℓ d, ray4_card ℓ d, ray4_downset ℓ hℓ d⟩, by
    intro hz
    have he := hz (rayPoint ℓ d 4) (ray4_tip ℓ hℓ d).1
    have ht := (ray4_tip ℓ hℓ d).2
    omega⟩
private theorem ray4Downset_injective (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    Function.Injective (ray4Downset ℓ hℓ) := by
  intro d e he
  apply ray4_injective ℓ hℓ
  exact congrArg (fun J => J.val.val.val) he

private noncomputable def remainingPatternEquiv (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    {J : {J : FiniteDownsets ℓ // ¬zeroOnly ℓ J} //
      J ∉ Set.range (ray4Downset ℓ hℓ)} ≃ RemainingPatterns ℓ := by
  sorry

private noncomputable def nonzeroPatternEquiv (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    {J : FiniteDownsets ℓ // ¬zeroOnly ℓ J} ≃ OtherPatterns ℓ := by
  classical
  exact (Equiv.sumCompl (fun J => J ∈ Set.range (ray4Downset ℓ hℓ))).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective _ (ray4Downset_injective ℓ hℓ)).symm
      (remainingPatternEquiv ℓ hℓ))

private noncomputable def patternEquiv (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    FiniteDownsets ℓ ≃ Patterns ℓ := by
  classical
  exact (Equiv.sumCompl (zeroOnly ℓ)).symm.trans
    (Equiv.sumCongr (lowEquiv ℓ hℓ) (nonzeroPatternEquiv ℓ hℓ))

private theorem finite_count (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    (Nat.card {J : ↥((vertices ℓ).powersetCard 5) // IsDownset ℓ J.val} : ℤ) =
      (ℓ.choose 5 : ℤ) + 10 * ℓ.choose 3 - 2 * ℓ.choose 2 + 36 * ℓ - 14 := by
  rw [Nat.card_congr (patternEquiv ℓ hℓ)]
  exact patterns_card ℓ hℓ

private theorem downset_count (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    (Nat.card {I : Finset (ℤ × ℤ) // I.card = 5 ∧ IsDownset ℓ I} : ℤ) =
      (ℓ.choose 5 : ℤ) + 10 * ℓ.choose 3 - 2 * ℓ.choose 2 + 36 * ℓ - 14 := by
  rw [Nat.card_congr (finiteEquiv ℓ hℓ)]
  exact finite_count ℓ hℓ

theorem result : claim := by
  intro ℓ hℓ
  rw [Nat.card_congr (heightEquiv ℓ (by omega))]
  exact downset_count ℓ hℓ

end D5.S3.StatisticalMechanics.SquareIceFiveOrangeCount
