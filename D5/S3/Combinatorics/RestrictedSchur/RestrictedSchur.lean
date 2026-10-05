/- GID: D5/S3/Combinatorics/RestrictedSchur/RestrictedSchur
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RestrictedSchur/RestrictedSchur
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A uniform seven-block colouring refutes Gaiser's Open Question 6.2. -/

import D5.S3.Combinatorics.RestrictedSchur.RestrictedSchurDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RestrictedSchur.RestrictedSchur

open scoped BigOperators

/-- The seven consecutive blocks have colours R, B, R, G, R, B, R. -/
def sevenBlockColouring (k n : ℤ) : Fin 3 :=
  if n ≤ k then 0
  else if n ≤ k ^ 2 + k then 1
  else if n ≤ k ^ 2 + 2 * k - 1 then 0
  else if n ≤ k ^ 3 + 2 * k ^ 2 then 2
  else if n ≤ k ^ 3 + 2 * k ^ 2 + k - 1 then 0
  else if n ≤ k ^ 3 + 3 * k ^ 2 + k - 2 then 1
  else 0

set_option maxHeartbeats 2000000 in
-- The symbolic case analysis covers every pair in the seven-block family.
/-- No restricted solution exists in the seven-block colouring for any `k ≥ 3`. -/
theorem sevenBlock_avoids (k : ℕ) (hk : 3 ≤ k) :
    ¬ RestrictedSchurDefs.HasMonochromaticSolution 3 k 2
      (k ^ 3 + 3 * k ^ 2 + 2 * k - 3) (fun n => sevenBlockColouring k n) := by
  classical
  have obstruction (k a b j t : ℤ) (hk : 3 ≤ k) (ha : 1 ≤ a) (hab : a < b)
      (hj : 1 ≤ j) (hjk : j < k) (ht : t = j * a + (k - j) * b)
      (htM : t ≤ k ^ 3 + 3 * k ^ 2 + 2 * k - 3)
      (hc : sevenBlockColouring k a = sevenBlockColouring k b) :
      sevenBlockColouring k t ≠ sevenBlockColouring k a := by
    have hp : k ^ 2 ≥ 3 * k := by nlinarith
    have hq : k ^ 3 ≥ 3 * k ^ 2 := by
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 3) (sq_nonneg k)]
    have low : (k - 1) * a + b ≤ t := by
      nlinarith [mul_nonneg (by omega : 0 ≤ k - j - 1) (by omega : 0 ≤ b - a)]
    have high : t ≤ a + (k - 1) * b := by
      nlinarith [mul_nonneg (by omega : 0 ≤ j - 1) (by omega : 0 ≤ b - a)]
    have low' : k * a + 1 ≤ t := by nlinarith
    have high' : t ≤ k * b - 1 := by nlinarith
    have twice : k - j ≥ 2 → 2 * b ≤ t := by
      intro h
      nlinarith [mul_nonneg (by omega : 0 ≤ k - j - 2) (by omega : 0 ≤ b),
        mul_nonneg (by omega : 0 ≤ j) (by omega : 0 ≤ a)]
    unfold sevenBlockColouring at hc ⊢
    split_ifs at hc
    all_goals norm_num at hc
    all_goals try omega
    · -- A,A
      rename_i aA bA
      have lo : k < t := by nlinarith
      have hi : t ≤ k ^ 2 := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k) (by omega : 0 ≤ k - b)]
      split_ifs <;> norm_num <;> omega
    · -- A,C
      rename_i aA bA bB bC
      have lo : k ^ 2 + 2 * k - 1 < t := by nlinarith
      have hi : t ≤ k ^ 3 + 2 * k ^ 2 := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k - 1)
          (by omega : 0 ≤ k ^ 2 + 2 * k - 1 - b)]
      split_ifs <;> norm_num <;> omega
    · -- A,E
      rename_i aA bA bB bC bD bE
      have last : j = k - 1 := by
        by_contra h
        have := twice (by omega)
        nlinarith
      have lo : k ^ 3 + 2 * k ^ 2 + k - 1 < t := by nlinarith
      have hi : t ≤ k ^ 3 + 3 * k ^ 2 + k - 2 := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k - 1) (by omega : 0 ≤ k - a)]
      split_ifs <;> norm_num <;> omega
    · -- A,H
      rename_i aA bA bB bC bD bE bF
      have last : j = k - 1 := by
        by_contra h
        have := twice (by omega)
        nlinarith
      nlinarith
    · -- B,B
      rename_i aA aB bA bB
      have lo : k ^ 2 + k < t := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k) (by omega : 0 ≤ a - (k + 1))]
      have hi : t ≤ k ^ 3 + 2 * k ^ 2 + k - 1 := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k)
          (by omega : 0 ≤ k ^ 2 + k - b)]
      split_ifs <;> norm_num <;> omega
    · -- B,F
      rename_i aA aB bA bB bC bD bE bF
      have last : j = k - 1 := by
        by_contra h
        have := twice (by omega)
        nlinarith
      have lo : k ^ 3 + 3 * k ^ 2 + k - 2 < t := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k - 1)
          (by omega : 0 ≤ a - (k + 1))]
      split_ifs <;> norm_num <;> omega
    · -- C,C
      rename_i aA aB aC bA bB bC
      have lo : k ^ 2 + 2 * k - 1 < t := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k)
          (by omega : 0 ≤ a - (k ^ 2 + k + 1))]
      have hi : t ≤ k ^ 3 + 2 * k ^ 2 := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k)
          (by omega : 0 ≤ k ^ 2 + 2 * k - 1 - b)]
      split_ifs <;> norm_num <;> omega
    · -- C,E
      rename_i aA aB aC bA bB bC bD bE
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 1)
        (by omega : 0 ≤ a - (k ^ 2 + k + 1))]
    · -- C,H
      rename_i aA aB aC bA bB bC bD bE bF
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 1)
        (by omega : 0 ≤ a - (k ^ 2 + k + 1))]
    · -- D,D
      rename_i aA aB aC aD bA bB bC bD
      have lo : k ^ 3 + 2 * k ^ 2 < t := by
        nlinarith [mul_nonneg (by omega : 0 ≤ k)
          (by omega : 0 ≤ a - (k ^ 2 + 2 * k))]
      split_ifs <;> norm_num <;> omega
    · -- E,E
      rename_i aA aB aC aD aE bA bB bC bD bE
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 3)
        (by omega : 0 ≤ a), mul_nonneg (by omega : 0 ≤ k)
        (by omega : 0 ≤ a - (k ^ 3 + 2 * k ^ 2 + 1))]
    · -- E,H
      rename_i aA aB aC aD aE bA bB bC bD bE bF
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 3) (by omega : 0 ≤ a)]
    · -- F,F
      rename_i aA aB aC aD aE aF bA bB bC bD bE bF
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 3) (by omega : 0 ≤ a)]
    · -- H,H
      rename_i aA aB aC aD aE aF bA bB bC bD bE bF
      nlinarith [mul_nonneg (by omega : 0 ≤ k - 3) (by omega : 0 ≤ a)]
  intro h
  obtain ⟨x, hx, hsum, hcard, hmono⟩ := h
  let t := x (Fin.last k)
  let y : Fin k → ℕ := fun i => x i.castSucc
  let s := Finset.univ.image y
  have hlt (i : Fin k) : y i < t := by
    let z : Fin k := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hzi : z ≠ i := by
      dsimp [z]
      split_ifs with hi <;> intro he
      · have := congrArg Fin.val he
        simp only at this
        omega
      · have := congrArg Fin.val he
        simp only at this
        omega
    have hh := Finset.single_lt_sum (f := y) hzi (Finset.mem_univ i)
      (Finset.mem_univ z) (by have := (hx z.castSucc).1; dsimp [y]; omega)
      (fun _ _ _ => Nat.zero_le _)
    simpa only [y, t, hsum] using hh
  have ht_not : t ∉ s := by
    intro hm
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    have := hlt i
    omega
  have hfull : Finset.univ.image x = insert t s := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      · exact Or.inl rfl
    · rintro (rfl | hm)
      · exact ⟨Fin.last k, rfl⟩
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
        exact ⟨i.castSucc, hi⟩
  have htwo : s.card = 2 := by
    rw [hfull, Finset.card_insert_of_notMem ht_not] at hcard
    omega
  obtain ⟨u, v, huv, huv_set⟩ := Finset.card_eq_two.mp htwo
  have sorted : ∃ a b : ℕ, a < b ∧ s = {a, b} := by
    rcases lt_or_gt_of_ne huv with huv | hvu
    · exact ⟨u, v, huv, huv_set⟩
    · exact ⟨v, u, hvu, by rw [huv_set, Finset.pair_comm]⟩
  obtain ⟨a, b, hab, hs⟩ := sorted
  obtain ⟨ia, _, hia⟩ := Finset.mem_image.mp (show a ∈ s by rw [hs]; simp)
  obtain ⟨ib, _, hib⟩ := Finset.mem_image.mp (show b ∈ s by rw [hs]; simp)
  have values (i : Fin k) : y i = a ∨ y i = b := by
    have hm : y i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using hm
  let f := Finset.univ.filter (fun i : Fin k => y i = a)
  have hf : ia ∈ f := by simp [f, hia]
  have hnf : ib ∉ f := by simp [f, hib, hab.ne']
  have hj : 1 ≤ f.card := Finset.card_pos.mpr ⟨ia, hf⟩
  have hjk : f.card < k := by
    have hh := Finset.card_lt_card
      ((Finset.ssubset_iff_of_subset (Finset.subset_univ f)).mpr
        ⟨ib, Finset.mem_univ _, hnf⟩)
    simpa using hh
  have hsum' : t = f.card * a + (k - f.card) * b := by
    have hsuma : ∑ i ∈ f, y i = f.card * a := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
      simp [f]
    have hsumb : ∑ i ∈ fᶜ, y i = (k - f.card) * b := by
      have vb (i : Fin k) (hi : i ∈ fᶜ) : y i = b := by
        have hia : y i ≠ a := by
          have : i ∉ f := Finset.mem_compl.mp hi
          simpa [f] using this
        exact (values i).resolve_left hia
      rw [Finset.sum_congr rfl vb]
      simp [Finset.card_compl]
    have hh := Finset.sum_add_sum_compl f y
    rw [hsuma, hsumb] at hh
    exact hsum.symm.trans hh.symm
  have haa : 1 ≤ a := by
    have := (hx ia.castSucc).1
    simpa only [← hia] using this
  have hcab : sevenBlockColouring k a = sevenBlockColouring k b := by
    simpa only [← hia, ← hib, y] using hmono ia.castSucc ib.castSucc
  have hcta : sevenBlockColouring k t = sevenBlockColouring k a := by
    simpa only [← hia, y, t] using hmono (Fin.last k) ia.castSucc
  have htcast := congrArg (fun z : ℕ => (z : ℤ)) hsum'
  push_cast [Nat.cast_sub (Nat.le_of_lt hjk)] at htcast
  have hmpos : 3 ≤ k ^ 3 + 3 * k ^ 2 + 2 * k := by omega
  have htM : (t : ℤ) ≤ ((k ^ 3 + 3 * k ^ 2 + 2 * k - 3 : ℕ) : ℤ) := by
    exact_mod_cast (hx (Fin.last k)).2
  push_cast [Nat.cast_sub hmpos] at htM
  exact (obstruction k a b f.card t (by exact_mod_cast hk) (by exact_mod_cast haa)
    (by exact_mod_cast hab) (by exact_mod_cast hj) (by exact_mod_cast hjk)
    htcast htM hcab) hcta

/-- Gaiser's proposed equality fails for arbitrarily large `k`. -/
theorem result : ¬ RestrictedSchurDefs.claim := by
  classical
  rintro ⟨K, hK⟩
  let k := max K 3
  have hk : 3 ≤ k := le_max_right _ _
  have heq := hK k (le_max_left K 3)
  let s : Set ℕ := {n | ∀ c : ℕ → Fin 3,
    RestrictedSchurDefs.HasMonochromaticSolution 3 k 2 n c}
  have hs : s.Nonempty := by
    by_contra h
    have hempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hzero : RestrictedSchurDefs.schur 3 k 2 = 0 := by
      change sInf s = 0
      rw [hempty, Nat.sInf_empty]
    have hpos : 0 < k ^ 3 + 3 * k ^ 2 + k - 1 := by omega
    omega
  have hmem : k ^ 3 + 3 * k ^ 2 + k - 1 ∈ s := by
    rw [← heq]
    exact Nat.sInf_mem hs
  have hsol := hmem (fun n => sevenBlockColouring k n)
  apply sevenBlock_avoids k hk
  obtain ⟨x, hx, hsum, hcard, hmono⟩ := hsol
  refine ⟨x, ?_, hsum, hcard, hmono⟩
  intro i
  exact ⟨(hx i).1, (hx i).2.trans (by omega)⟩

end D5.S3.Combinatorics.RestrictedSchur.RestrictedSchur
