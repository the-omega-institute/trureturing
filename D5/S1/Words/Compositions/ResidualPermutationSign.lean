/- GID: D5/S1/Words/Compositions/ResidualPermutationSign
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/ResidualPermutationSign
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Interlaced prefix intervals have signed permutation sum supported only at identity. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open scoped BigOperators
open Classical

/-! Prefix lengths are natural numbers, and permutation values are shifted by one.
The proof first removes lower cuts by cancellation and then pairs the upper-bound class. -/
namespace D5.S1.Words.Compositions.ResidualPermutationSign

def prefixSum {n : ℕ} (p : Equiv.Perm (Fin n)) (k : ℕ) : ℕ :=
  ∑ i : Fin n with i.val < k, ((p i).val + 1)

def Upper {n : ℕ} (a b : Equiv.Perm (Fin n)) : Prop :=
  ∀ k : ℕ, k ≤ n → prefixSum b k ≤ prefixSum a k

def LowerFrom {n : ℕ} (a b : Equiv.Perm (Fin n)) (r : ℕ) : Prop :=
  ∀ i : Fin n, r ≤ i.val → prefixSum a i.val < prefixSum b (i.val + 1)

def signInt {n : ℕ} (p : Equiv.Perm (Fin n)) : ℤ := (Equiv.Perm.sign p : ℤ)

@[simp] private theorem prefixSum_zero {n} (p : Equiv.Perm (Fin n)) : prefixSum p 0 = 0 := by
  simp [prefixSum]

private theorem prefixSum_step {n} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    prefixSum p (i.val + 1) = prefixSum p i.val + (p i).val + 1 := by
  classical
  have hset : (Finset.univ.filter fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter fun j : Fin n => j.val < i.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j = i
      · exact Or.inl hj
      · right; have : j.val ≠ i.val := fun e => hj (Fin.ext e); omega
    · rintro (rfl | h) <;> omega
  simp only [prefixSum, hset]
  rw [Finset.sum_insert (by simp)]
  omega

private theorem prefixSum_mono {n} (p : Equiv.Perm (Fin n)) {k l : ℕ} (h : k ≤ l) :
    prefixSum p k ≤ prefixSum p l := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  omega

private theorem prefixSum_pos {n} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    0 < prefixSum p (i.val + 1) := by
  rw [prefixSum_step]
  omega

private theorem prefixSum_swap {n} (p : Equiv.Perm (Fin n)) (u v : Fin n)
    (huv : v.val = u.val + 1) {k : ℕ} (hk : k ≠ v.val) :
    prefixSum (p * Equiv.swap u v) k = prefixSum p k := by
  classical
  have hm (i : Fin n) : (Equiv.swap u v i).val < k ↔ i.val < k := by
    by_cases hiu : i = u
    · subst i; simp only [Equiv.swap_apply_left]; omega
    · by_cases hiv : i = v
      · subst i; simp only [Equiv.swap_apply_right]; omega
      · simp [Equiv.swap_apply_of_ne_of_ne hiu hiv]
  simpa only [prefixSum, Finset.sum_filter, Equiv.Perm.mul_apply, hm] using
    (Equiv.sum_comp (Equiv.swap u v) fun i : Fin n =>
      if i.val < k then (p i).val + 1 else 0)

private theorem swap_twice {n} (p : Equiv.Perm (Fin n)) (u v : Fin n) :
    (p * Equiv.swap u v) * Equiv.swap u v = p := by simp [mul_assoc]

private theorem swap_ne {n} (p : Equiv.Perm (Fin n)) (u v : Fin n) (h : u ≠ v) :
    p * Equiv.swap u v ≠ p := by
  intro he
  have he' := congrArg (fun q : Equiv.Perm (Fin n) => q u) he
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at he'
  exact h (p.injective he').symm

private theorem signInt_swap {n} (p : Equiv.Perm (Fin n)) (u v : Fin n) (h : u ≠ v) :
    signInt (p * Equiv.swap u v) = -signInt p := by
  simp [signInt, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h]

private theorem upper_swap_of_short {n} (a b : Equiv.Perm (Fin n)) (u v : Fin n)
    (huv : v.val = u.val + 1) (hb : Upper a b)
    (hshort : prefixSum b (v.val + 1) ≤ prefixSum a v.val) :
    Upper a (b * Equiv.swap u v) := by
  intro k hk
  by_cases hkv : k = v.val
  · subst k
    have hmono := prefixSum_mono (b * Equiv.swap u v) (Nat.le_succ v.val)
    rw [prefixSum_swap b u v huv (k := v.val + 1) (by omega)] at hmono
    exact hmono.trans hshort
  · rw [prefixSum_swap b u v huv hkv]
    exact hb k hk

private theorem swap_sum_zero {n} (s : Finset (Equiv.Perm (Fin n))) (u v : Fin n)
    (hne : u ≠ v) (hmem : ∀ b ∈ s, b * Equiv.swap u v ∈ s) :
    ∑ b ∈ s, signInt b = 0 := by
  classical
  apply Finset.sum_involution (fun b _ => b * Equiv.swap u v)
  · intro b hb; rw [signInt_swap b u v hne]; omega
  · intro b hb hsign; exact swap_ne b u v hne
  · exact hmem
  · intro b hb; exact swap_twice b u v

noncomputable def rowSum {n} (a : Equiv.Perm (Fin n)) (r : ℕ) : ℤ := by
  classical
  exact ∑ b : Equiv.Perm (Fin n) with Upper a b ∧ LowerFrom a b r, signInt b

/-- Removing the next strict lower cut preserves the signed sum. -/
theorem lower_cut_removal {n} (a : Equiv.Perm (Fin n)) (r : ℕ) :
    rowSum a r = rowSum a (r + 1) := by
  classical
  let s := Finset.univ.filter fun b : Equiv.Perm (Fin n) =>
    Upper a b ∧ LowerFrom a b (r + 1)
  let test := fun b : Equiv.Perm (Fin n) =>
    ∀ i : Fin n, i.val = r → prefixSum a r < prefixSum b (r + 1)
  have hgood : s.filter test = Finset.univ.filter
      (fun b : Equiv.Perm (Fin n) => Upper a b ∧ LowerFrom a b r) := by
    apply Finset.ext
    intro b
    dsimp only [s]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hu, hl⟩, ht⟩
      refine ⟨hu, fun i hi => ?_⟩
      by_cases he : i.val = r
      · simpa [he] using ht i he
      · exact hl i (by omega)
    · rintro ⟨hu, hl⟩
      exact ⟨⟨hu, fun i hi => hl i (by omega)⟩, fun i hi => by
        simpa [hi] using hl i (by omega)⟩
  have hbad : ∑ b ∈ s.filter (fun b => ¬test b), signInt b = 0 := by
    by_cases hr : r < n
    · by_cases hr0 : r = 0
      · subst r
        apply Finset.sum_eq_zero
        intro b hb
        have ht := (Finset.mem_filter.mp hb).2
        exact (ht (by intro i hi; simpa [hi] using prefixSum_pos b i)).elim
      · let u : Fin n := ⟨r - 1, by omega⟩
        let v : Fin n := ⟨r, hr⟩
        have huv : v.val = u.val + 1 := by dsimp [u, v]; omega
        apply swap_sum_zero _ u v (by
          intro he
          have := congrArg Fin.val he
          dsimp [u, v] at this
          omega)
        intro b hb
        obtain ⟨hb, ht⟩ := Finset.mem_filter.mp hb
        obtain ⟨hu, hl⟩ := (Finset.mem_filter.mp hb).2
        have hshort : prefixSum b (r + 1) ≤ prefixSum a r := by
          by_contra h
          exact ht (by intro i hi; omega)
        have hshort' : prefixSum (b * Equiv.swap u v) (r + 1) ≤ prefixSum a r := by
          rw [prefixSum_swap b u v huv (by dsimp [v]; omega)]
          exact hshort
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, upper_swap_of_short a b u v huv hu hshort, ?_⟩
          intro i hi
          rw [prefixSum_swap b u v huv (by dsimp [v]; omega)]
          exact hl i hi
        · intro h
          have := h v rfl
          omega
    · apply Finset.sum_eq_zero
      intro b hb
      have ht := (Finset.mem_filter.mp hb).2
      exact (ht (by intro i hi; have := i.isLt; omega)).elim
  have he := Finset.sum_filter_add_sum_filter_not s test signInt
  rw [hgood, hbad, add_zero] at he
  exact he

private theorem rowSum_eq_upper {n} (a : Equiv.Perm (Fin n)) :
    rowSum a 0 = ∑ b : Equiv.Perm (Fin n) with Upper a b, signInt b := by
  classical
  have hr : ∀ r, rowSum a 0 = rowSum a r := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => exact ih.trans (lower_cut_removal a r)
  rw [hr n]
  simp [rowSum, LowerFrom, show ∀ i : Fin n, ¬n ≤ i.val from fun i => by omega]

private theorem value_ge_of_fixed {n} (p : Equiv.Perm (Fin n)) {r : ℕ}
    (hf : ∀ i : Fin n, i.val < r → p i = i) (i : Fin n) (hi : r ≤ i.val) :
    r ≤ (p i).val := by
  by_contra h
  have hp := hf (p i) (by omega)
  have he : p i = i := p.injective hp
  rw [he] at h
  omega

private theorem prefixSum_congr {n} (a b : Equiv.Perm (Fin n)) (k : ℕ)
    (h : ∀ i : Fin n, i.val < k → a i = b i) : prefixSum a k = prefixSum b k := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_filter.mp hi).2]

private theorem upper_fixed_prefix {n} (a b : Equiv.Perm (Fin n)) (hu : Upper a b)
    {r : ℕ} (ha : ∀ i : Fin n, i.val < r → a i = i) :
    ∀ i : Fin n, i.val < r → b i = i := by
  have aux : ∀ k, k ≤ r → ∀ i : Fin n, i.val < k → b i = i := by
    intro k
    induction k with
    | zero => intro hk i hi; omega
    | succ k ih =>
      intro hk i hi
      have hf := ih (by omega)
      by_cases hik : i.val < k
      · exact hf i hik
      · have hik : i.val = k := by omega
        have hai := ha i (by omega)
        have hp : prefixSum b i.val = prefixSum a i.val := by
          apply prefixSum_congr
          intro j hj
          rw [hf j (by omega), ha j (by omega)]
        have hs := hu (i.val + 1) (by omega)
        rw [prefixSum_step, prefixSum_step, hp, hai] at hs
        have hg := value_ge_of_fixed b hf i (by omega)
        exact Fin.ext (by omega)
  exact aux r le_rfl

private theorem upper_identity {n} (b : Equiv.Perm (Fin n)) : Upper 1 b ↔ b = 1 := by
  constructor
  · intro hu
    apply Equiv.ext
    intro i
    exact upper_fixed_prefix 1 b hu (r := n) (by simp) i i.isLt
  · rintro rfl; intro k hk; exact le_rfl

private theorem exists_min_move {n} (a : Equiv.Perm (Fin n)) (ha : a ≠ 1) :
    ∃ k j : Fin n, k.val < j.val ∧ a j = k ∧
      ∀ i : Fin n, i.val < k.val → a i = i := by
  let s := Finset.univ.filter fun i : Fin n => a i ≠ i
  have hs : s.Nonempty := by
    by_contra h
    apply ha
    apply Equiv.ext
    intro i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hi⟩⟩
  let k := s.min' hs
  have hk : a k ≠ k := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hf : ∀ i : Fin n, i.val < k.val → a i = i := by
    intro i hi
    by_contra hai
    have hki := Finset.min'_le s i (by simp [s, hai])
    have : k.val ≤ i.val := hki
    omega
  let j := a.symm k
  have hj : a j = k := a.apply_symm_apply k
  have hkj : k.val < j.val := by
    by_contra h
    by_cases he : j = k
    · rw [he] at hj
      exact hk hj
    · have hlt : j.val < k.val := by
        have : j.val ≠ k.val := fun e => he (Fin.ext e)
        omega
      have := hf j hlt
      have : j = k := this.symm.trans hj
      exact he this
  exact ⟨k, j, hkj, hj, hf⟩

/-- A nonidentity upper-bound class is closed under one fixed adjacent transposition. -/
theorem upper_sum_vanish {n} (a : Equiv.Perm (Fin n)) (ha : a ≠ 1) :
    (∑ b : Equiv.Perm (Fin n) with Upper a b, signInt b) = 0 := by
  obtain ⟨k, v, hkv, hav, hfix⟩ := exists_min_move a ha
  let u : Fin n := ⟨v.val - 1, by omega⟩
  have huv : v.val = u.val + 1 := by dsimp [u]; omega
  apply swap_sum_zero _ u v (by intro he; have := congrArg Fin.val he; dsimp [u] at this; omega)
  intro b hb
  have hu := (Finset.mem_filter.mp hb).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l hl
  by_cases he : l = v.val
  · subst l
    have hfb := upper_fixed_prefix a b hu hfix
    have hbu := value_ge_of_fixed b hfb u (by dsimp [u]; omega)
    have hbv := hu (v.val + 1) (by omega)
    rw [prefixSum_step a v, hav] at hbv
    have hstep := prefixSum_step (b * Equiv.swap u v) v
    rw [prefixSum_swap b u v huv (k := v.val + 1) (by omega)] at hstep
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right] at hstep
    omega
  · rw [prefixSum_swap b u v huv he]
    exact hu l hl

/-- The one-based values are `a i + 1`; prefix arguments are lengths. -/
def InResidual {n : ℕ} (a b : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, prefixSum a i.val < prefixSum b (i.val + 1) ∧
    prefixSum b (i.val + 1) ≤ prefixSum a (i.val + 1)

private theorem inResidual_iff {n} (a b : Equiv.Perm (Fin n)) :
    InResidual a b ↔ Upper a b ∧ LowerFrom a b 0 := by
  constructor
  · intro h
    refine ⟨?_, fun i _ => (h i).1⟩
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · let i : Fin n := ⟨k - 1, by omega⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      simpa only [hi] using (h i).2
  · rintro ⟨hu, hl⟩ i
    exact ⟨hl i (by omega), hu (i.val + 1) (by omega)⟩

/-- S(a): the signed residual sum is one for the identity and zero otherwise. -/
theorem signed_residual_sum {n : ℕ} (a : Equiv.Perm (Fin n)) :
    (∑ b : Equiv.Perm (Fin n) with InResidual a b, signInt b) =
      if a = 1 then 1 else 0 := by
  have hrow : (∑ b : Equiv.Perm (Fin n) with InResidual a b, signInt b) =
      rowSum a 0 := by simp only [rowSum, inResidual_iff]
  rw [hrow, rowSum_eq_upper]
  by_cases ha : a = 1
  · subst a
    rw [if_pos rfl, Finset.sum_eq_single 1]
    · simp [signInt]
    · intro b hb hne
      exact (hne ((upper_identity b).mp (Finset.mem_filter.mp hb).2)).elim
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => le_rfl⟩)).elim
  · rw [if_neg ha]
    exact upper_sum_vanish a ha

end D5.S1.Words.Compositions.ResidualPermutationSign
