/- GID: D5/S3/Combinatorics/LatinEulerianPermutations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatinEulerianPermutations
   mirror-E: none(waiver:explicit-row-permutations-for-Latin-Eulerian-multiples)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Three explicit permutation families supply the low targets and odd midpoint. -/

import D5.S3.Combinatorics.LatinEulerianFormula
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatinEulerianMultiples

/-- The entry at index `i` in the special order for target two. -/
def twoVal (n i : ℕ) : ℕ :=
  if i = 0 then 1 else if i = 1 then 0 else if i ≤ n - 3 then n - 1 - i
  else if i = n - 2 then n - 1 else n - 2

/-- The row order `(1,0,n-3,...,2,n-1,n-2)`. -/
noncomputable def twoPermutation (n : ℕ) (hn : 5 ≤ n) : Equiv.Perm (Fin n) := by
  have hbound (i : Fin n) : twoVal n i.val < n := by
    unfold twoVal
    split_ifs <;> omega
  let f : Fin n → Fin n := fun i => ⟨twoVal n i.val, hbound i⟩
  refine Equiv.ofBijective f ?_
  apply Finite.injective_iff_bijective.mp
  intro i j h
  apply Fin.ext
  have hv : twoVal n i.val = twoVal n j.val := congrArg Fin.val h
  unfold twoVal at hv
  split_ifs at hv <;> omega

/-- The entry at index `i` in the four-block low-target order. -/
def lowVal (n k i : ℕ) : ℕ :=
  if i = 0 then k - 1 else if i < k then i - 1
  else if i < n - k - 1 then n - 2 - i else 2 * n - k - 2 - i

/-- The four-block order for `3 ≤ k` and `2k+2 ≤ n`. -/
noncomputable def lowPermutation (n k : ℕ) (hk : 3 ≤ k) (hn : 2 * k + 2 ≤ n) :
    Equiv.Perm (Fin n) := by
  have hbound (i : Fin n) : lowVal n k i.val < n := by
    unfold lowVal
    split_ifs <;> omega
  let f : Fin n → Fin n := fun i => ⟨lowVal n k i.val, hbound i⟩
  refine Equiv.ofBijective f ?_
  apply Finite.injective_iff_bijective.mp
  intro i j h
  apply Fin.ext
  have hv : lowVal n k i.val = lowVal n k j.val := congrArg Fin.val h
  unfold lowVal at hv
  split_ifs at hv <;> omega

/-- The entry at index `i` in the odd-midpoint order of length `2m+1`. -/
def midpointVal (m i : ℕ) : ℕ :=
  if i = 0 then 0 else if i < m then i + 1
  else if i < 2 * m then 3 * m - i else 1

/-- The order `(0,2,...,m,2m,...,m+1,1)` for odd `n`. -/
noncomputable def midpointPermutation (m : ℕ) (hm : 2 ≤ m) :
    Equiv.Perm (Fin (2 * m + 1)) := by
  have hbound (i : Fin (2 * m + 1)) : midpointVal m i.val < 2 * m + 1 := by
    unfold midpointVal
    split_ifs <;> omega
  let f : Fin (2 * m + 1) → Fin (2 * m + 1) :=
    fun i => ⟨midpointVal m i.val, hbound i⟩
  refine Equiv.ofBijective f ?_
  apply Finite.injective_iff_bijective.mp
  intro i j h
  apply Fin.ext
  have hv : midpointVal m i.val = midpointVal m j.val := congrArg Fin.val h
  unfold midpointVal at hv
  split_ifs at hv <;> omega

theorem two_statistics (n : ℕ) (hn : 5 ≤ n) (hpos : 0 < n) :
    let p := twoPermutation n hn
    ordinaryAscents hpos p = 2 ∧ forwardUnits hpos p = 0 ∧
      backwardUnits hpos p = (n - 3 : ℕ) ∧
      (rowAt hpos p 0).val = 1 ∧ (rowAt hpos p (n - 1)).val = n - 2 := by
  let p := twoPermutation n hn
  have hforwardUnit (a b : Fin n) :
      (b - a).val = 1 ↔
        b.val = a.val + 1 ∨ (a.val = n - 1 ∧ b.val = 0) := by
    have hv := Fin.coe_int_sub_eq_ite b a
    by_cases h : a ≤ b
    · simp [h] at hv; omega
    · simp [h] at hv; omega
  have hbackwardUnit (a b : Fin n) :
      (b - a).val = n - 1 ↔
        a.val = b.val + 1 ∨ (a.val = 0 ∧ b.val = n - 1) := by
    have hv := Fin.coe_int_sub_eq_ite b a
    by_cases h : a ≤ b
    · simp [h] at hv; omega
    · simp [h] at hv; omega
  have hasc (j : ℕ) (hj : j < n - 1) :
      (rowAt hpos p j < rowAt hpos p (j + 1)) ↔ j = 1 ∨ j = n - 3 := by
    have hj0 : j < n := by omega
    have hj1 : j + 1 < n := by omega
    change twoVal n (j % n) < twoVal n ((j + 1) % n) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold twoVal
    split_ifs <;> grind
  have hforward (j : ℕ) (hj : j < n - 1) :
      ¬ (rowDelta hpos p j).val = 1 := by
    have hj0 : j < n := by omega
    have hj1 : j + 1 < n := by omega
    rw [rowDelta, hforwardUnit]
    change ¬ (twoVal n ((j + 1) % n) = twoVal n (j % n) + 1 ∨
      (twoVal n (j % n) = n - 1 ∧ twoVal n ((j + 1) % n) = 0))
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold twoVal
    split_ifs <;> grind
  have hbackward (j : ℕ) (hj : j < n - 1) :
      (rowDelta hpos p j).val = n - 1 ↔
        j = 0 ∨ (2 ≤ j ∧ j ≤ n - 4) ∨ j = n - 2 := by
    have hj0 : j < n := by omega
    have hj1 : j + 1 < n := by omega
    rw [rowDelta, hbackwardUnit]
    change (twoVal n (j % n) = twoVal n ((j + 1) % n) + 1 ∨
      (twoVal n (j % n) = 0 ∧ twoVal n ((j + 1) % n) = n - 1)) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold twoVal
    split_ifs <;> grind
  have hsetAsc : (Finset.range (n - 1)).filter
      (fun j => rowAt hpos p j < rowAt hpos p (j + 1)) =
      insert 1 ({n - 3} : Finset ℕ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hp⟩
      exact (hasc j hj).mp hp
    · intro h
      have hj : j < n - 1 := by rcases h with h | h <;> omega
      exact ⟨hj, (hasc j hj).mpr h⟩
  have hsetForward : (Finset.range (n - 1)).filter
      (fun j => (rowDelta hpos p j).val = 1) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hp⟩
      exact (hforward j hj hp).elim
    · intro h
      simp at h
  have hsetBackward : (Finset.range (n - 1)).filter
      (fun j => (rowDelta hpos p j).val = n - 1) =
      insert 0 (insert (n - 2) (Finset.Ico 2 (n - 3))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_Ico]
    by_cases hj : j < n - 1
    · have h := hbackward j hj
      grind
    · grind
  have hAscSum : ordinaryAscents hpos p = 2 := by
    rw [ordinaryAscents, Finset.sum_boole, hsetAsc]
    have hne : 1 ∉ ({n - 3} : Finset ℕ) := by simp; omega
    rw [Finset.card_insert_of_notMem hne]
    simp
  have hForwardSum : forwardUnits hpos p = 0 := by
    rw [forwardUnits, Finset.sum_boole, hsetForward]
    simp
  have hBackwardSum : backwardUnits hpos p = (n - 3 : ℕ) := by
    rw [backwardUnits, Finset.sum_boole, hsetBackward]
    have hne0 : 0 ∉ insert (n - 2) (Finset.Ico 2 (n - 3)) := by
      simp only [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnelast : n - 2 ∉ Finset.Ico 2 (n - 3) := by
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_insert_of_notMem hne0, Finset.card_insert_of_notMem hnelast,
      Nat.card_Ico]
    norm_cast
    omega
  have hfirst : (rowAt hpos p 0).val = 1 := by
    change twoVal n (0 % n) = 1
    simp [twoVal]
  have hlast : (rowAt hpos p (n - 1)).val = n - 2 := by
    change twoVal n ((n - 1) % n) = n - 2
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold twoVal
    split_ifs <;> omega
  exact ⟨hAscSum, hForwardSum, hBackwardSum, hfirst, hlast⟩

theorem low_statistics (n k : ℕ) (hk : 3 ≤ k) (hn : 2 * k + 2 ≤ n)
    (hpos : 0 < n) :
    let p := lowPermutation n k hk hn
    ordinaryAscents hpos p = (k : ℤ) ∧
      forwardUnits hpos p = (k - 2 : ℕ) ∧
      backwardUnits hpos p = (n - k - 2 : ℕ) ∧
      (rowAt hpos p 0).val = k - 1 ∧
      (rowAt hpos p (n - 1)).val = n - k - 1 := by
  let p := lowPermutation n k hk hn
  have hforwardUnit (a b : Fin n) :
      (b - a).val = 1 ↔
        b.val = a.val + 1 ∨ (a.val = n - 1 ∧ b.val = 0) := by
    have hv := Fin.coe_int_sub_eq_ite b a
    by_cases h : a ≤ b
    · simp [h] at hv; omega
    · simp [h] at hv; omega
  have hbackwardUnit (a b : Fin n) :
      (b - a).val = n - 1 ↔
        a.val = b.val + 1 ∨ (a.val = 0 ∧ b.val = n - 1) := by
    have hv := Fin.coe_int_sub_eq_ite b a
    by_cases h : a ≤ b
    · simp [h] at hv; omega
    · simp [h] at hv; omega
  have hasc (j : ℕ) (hj : j < n - 1) :
      (rowAt hpos p j < rowAt hpos p (j + 1)) ↔
        (1 ≤ j ∧ j < k) ∨ j = n - k - 2 := by
    have hj0 : j < n := by omega
    have hj1 : j + 1 < n := by omega
    change lowVal n k (j % n) < lowVal n k ((j + 1) % n) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold lowVal
    split_ifs <;> grind
  have hforward (j : ℕ) (hj : j < n - 1) :
      (rowDelta hpos p j).val = 1 ↔ 1 ≤ j ∧ j < k - 1 := by
    have hj0 : j < n := by omega
    have hj1 : j + 1 < n := by omega
    rw [rowDelta, hforwardUnit]
    change (lowVal n k ((j + 1) % n) = lowVal n k (j % n) + 1 ∨
      (lowVal n k (j % n) = n - 1 ∧ lowVal n k ((j + 1) % n) = 0)) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold lowVal
    split_ifs <;> grind
  have hbackward (j : ℕ) (hj : j < n - 1) :
      (rowDelta hpos p j).val = n - 1 ↔
        (k ≤ j ∧ j < n - k - 2) ∨ (n - k - 1 ≤ j ∧ j < n - 1) := by
    have hj0 : j < n := by omega
    have hj1 : j + 1 < n := by omega
    rw [rowDelta, hbackwardUnit]
    change (lowVal n k (j % n) = lowVal n k ((j + 1) % n) + 1 ∨
      (lowVal n k (j % n) = 0 ∧ lowVal n k ((j + 1) % n) = n - 1)) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold lowVal
    split_ifs <;> grind
  have hsetAsc : (Finset.range (n - 1)).filter
      (fun j => rowAt hpos p j < rowAt hpos p (j + 1)) =
      insert (n - k - 2) (Finset.Ico 1 k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_Ico]
    by_cases hj : j < n - 1
    · have h := hasc j hj
      grind
    · grind
  have hsetForward : (Finset.range (n - 1)).filter
      (fun j => (rowDelta hpos p j).val = 1) = Finset.Ico 1 (k - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    by_cases hj : j < n - 1
    · simpa only [hj, true_and] using hforward j hj
    · grind
  have hsetBackward : (Finset.range (n - 1)).filter
      (fun j => (rowDelta hpos p j).val = n - 1) =
      Finset.Ico k (n - k - 2) ∪ Finset.Ico (n - k - 1) (n - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico]
    by_cases hj : j < n - 1
    · have h := hbackward j hj
      grind
    · grind
  have hAscSum : ordinaryAscents hpos p = (k : ℤ) := by
    rw [ordinaryAscents, Finset.sum_boole, hsetAsc]
    have hne : n - k - 2 ∉ Finset.Ico 1 k := by
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_insert_of_notMem hne, Nat.card_Ico]
    norm_cast
    omega
  have hForwardSum : forwardUnits hpos p = (k - 2 : ℕ) := by
    rw [forwardUnits, Finset.sum_boole, hsetForward, Nat.card_Ico]
    norm_cast
  have hBackwardSum : backwardUnits hpos p = (n - k - 2 : ℕ) := by
    rw [backwardUnits, Finset.sum_boole, hsetBackward]
    have hdis : Disjoint (Finset.Ico k (n - k - 2))
        (Finset.Ico (n - k - 1) (n - 1)) := by
      rw [Finset.disjoint_left]
      intro j hj hnot
      simp only [Finset.mem_Ico] at hj hnot
      omega
    rw [Finset.card_union_of_disjoint hdis, Nat.card_Ico, Nat.card_Ico]
    norm_cast
    omega
  have hfirst : (rowAt hpos p 0).val = k - 1 := by
    change lowVal n k (0 % n) = k - 1
    simp [lowVal]
  have hlast : (rowAt hpos p (n - 1)).val = n - k - 1 := by
    change lowVal n k ((n - 1) % n) = n - k - 1
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold lowVal
    split_ifs <;> omega
  exact ⟨hAscSum, hForwardSum, hBackwardSum, hfirst, hlast⟩

theorem midpoint_statistics (m : ℕ) (hm : 2 ≤ m) (hpos : 0 < 2 * m + 1) :
    let p := midpointPermutation m hm
    ordinaryAscents hpos p = (m : ℤ) ∧
      forwardUnits hpos p = (m - 2 : ℕ) ∧
      backwardUnits hpos p = (m - 1 : ℕ) ∧
      (rowAt hpos p 0).val = 0 ∧
      (rowAt hpos p (2 * m)).val = 1 := by
  let p := midpointPermutation m hm
  have hforwardUnit (a b : Fin (2 * m + 1)) :
      (b - a).val = 1 ↔
        b.val = a.val + 1 ∨ (a.val = 2 * m ∧ b.val = 0) := by
    have hv := Fin.coe_int_sub_eq_ite b a
    by_cases h : a ≤ b
    · simp [h] at hv; omega
    · simp [h] at hv; omega
  have hbackwardUnit (a b : Fin (2 * m + 1)) :
      (b - a).val = 2 * m ↔
        a.val = b.val + 1 ∨ (a.val = 0 ∧ b.val = 2 * m) := by
    have hv := Fin.coe_int_sub_eq_ite b a
    by_cases h : a ≤ b
    · simp [h] at hv; omega
    · simp [h] at hv; omega
  have hasc (j : ℕ) (hj : j < 2 * m) :
      (rowAt hpos p j < rowAt hpos p (j + 1)) ↔ j < m := by
    have hj0 : j < 2 * m + 1 := by omega
    have hj1 : j + 1 < 2 * m + 1 := by omega
    change midpointVal m (j % (2 * m + 1)) <
      midpointVal m ((j + 1) % (2 * m + 1)) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold midpointVal
    split_ifs <;> grind
  have hforward (j : ℕ) (hj : j < 2 * m) :
      (rowDelta hpos p j).val = 1 ↔ 1 ≤ j ∧ j < m - 1 := by
    have hj0 : j < 2 * m + 1 := by omega
    have hj1 : j + 1 < 2 * m + 1 := by omega
    rw [rowDelta, hforwardUnit]
    change (midpointVal m ((j + 1) % (2 * m + 1)) =
      midpointVal m (j % (2 * m + 1)) + 1 ∨
      (midpointVal m (j % (2 * m + 1)) = 2 * m ∧
        midpointVal m ((j + 1) % (2 * m + 1)) = 0)) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold midpointVal
    split_ifs <;> grind
  have hbackward (j : ℕ) (hj : j < 2 * m) :
      (rowDelta hpos p j).val = 2 * m ↔ m ≤ j ∧ j < 2 * m - 1 := by
    have hj0 : j < 2 * m + 1 := by omega
    have hj1 : j + 1 < 2 * m + 1 := by omega
    rw [rowDelta, hbackwardUnit]
    change (midpointVal m (j % (2 * m + 1)) =
      midpointVal m ((j + 1) % (2 * m + 1)) + 1 ∨
      (midpointVal m (j % (2 * m + 1)) = 0 ∧
        midpointVal m ((j + 1) % (2 * m + 1)) = 2 * m)) ↔ _
    rw [Nat.mod_eq_of_lt hj0, Nat.mod_eq_of_lt hj1]
    unfold midpointVal
    split_ifs <;> grind
  have hsetAsc : (Finset.range (2 * m)).filter
      (fun j => rowAt hpos p j < rowAt hpos p (j + 1)) = Finset.range m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases hj : j < 2 * m
    · have h := hasc j hj
      grind
    · grind
  have hsetForward : (Finset.range (2 * m)).filter
      (fun j => (rowDelta hpos p j).val = 1) = Finset.Ico 1 (m - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    by_cases hj : j < 2 * m
    · have h := hforward j hj
      grind
    · grind
  have hsetBackward : (Finset.range (2 * m)).filter
      (fun j => (rowDelta hpos p j).val = 2 * m) =
      Finset.Ico m (2 * m - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    by_cases hj : j < 2 * m
    · have h := hbackward j hj
      grind
    · grind
  have hAscSum : ordinaryAscents hpos p = (m : ℤ) := by
    rw [ordinaryAscents, show 2 * m + 1 - 1 = 2 * m by omega,
      Finset.sum_boole, hsetAsc, Finset.card_range]
  have hForwardSum : forwardUnits hpos p = (m - 2 : ℕ) := by
    rw [forwardUnits, show 2 * m + 1 - 1 = 2 * m by omega,
      Finset.sum_boole, hsetForward, Nat.card_Ico]
    norm_cast
  have hBackwardSum : backwardUnits hpos p = (m - 1 : ℕ) := by
    rw [backwardUnits, show 2 * m + 1 - 1 = 2 * m by omega,
      Finset.sum_boole]
    rw [hsetBackward, Nat.card_Ico]
    norm_cast
    omega
  have hfirst : (rowAt hpos p 0).val = 0 := by
    change midpointVal m (0 % (2 * m + 1)) = 0
    simp [midpointVal]
  have hlast : (rowAt hpos p (2 * m)).val = 1 := by
    change midpointVal m ((2 * m) % (2 * m + 1)) = 1
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold midpointVal
    split_ifs <;> omega
  exact ⟨hAscSum, hForwardSum, hBackwardSum, hfirst, hlast⟩

end D5.S3.Combinatorics.LatinEulerianMultiples
