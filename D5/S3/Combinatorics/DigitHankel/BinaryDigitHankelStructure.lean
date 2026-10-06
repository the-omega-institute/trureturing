/- GID: D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure
   mirror-E: none(waiver:binary-hankel-structural-identities)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Nondegenerate]
   utility: none
   digest: Binary block splitting and the structural identities for Hankel matrices. -/

import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelDefs
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DigitHankel.BinaryDigitHankel

open BinaryDigitHankelDefs
open scoped Matrix

/-- Sparse binary kernels force vanishing at every size outside the endpoint triples. -/
theorem zero_direction (n : ℕ) (hn : 2 ≤ n)
    (hout : ¬∃ k : ℕ, n + 1 = threshold k ∨ n = threshold k ∨ n = threshold k + 1) :
    hankel n (-2) = 0 := by
  classical
  have digitSum_block (k v u : ℕ) (t : ℤ) (hu : u < 2 ^ k) :
      digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
    have shift (l : List ℤ) :
        (l.mapIdx fun j d => (d : ℤ) * t ^ (j + 1)).sum =
          t * (l.mapIdx fun j d => (d : ℤ) * t ^ j).sum := by
      have heq : (l.mapIdx fun j d => (d : ℤ) * t ^ (j + 1)) =
          (l.mapIdx fun j d => (d : ℤ) * t ^ j).map (fun z => t * z) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'
          simp only [List.getElem_map, List.getElem_mapIdx, pow_succ]
          ring
      rw [heq, List.sum_map_mul_left]
      simp
    have step (a : ℕ) (e : ℕ) (he : e < 2) :
        digitSum (2 * a + e) t = (e : ℤ) + t * digitSum a t := by
      by_cases hz : a = 0 ∧ e = 0
      · rcases hz with ⟨rfl, rfl⟩
        simp [digitSum]
      · have hp : 0 < 2 * a + e := by omega
        unfold digitSum
        change ((List.flatMap (fun d : ℕ => [(d : ℤ)]) (Nat.digits 2 (2 * a + e))).mapIdx
          fun j d => d * t ^ j).sum =
            (e : ℤ) + t * ((List.flatMap (fun d : ℕ => [(d : ℤ)])
              (Nat.digits 2 a)).mapIdx fun j d => d * t ^ j).sum
        rw [← List.map_eq_flatMap, ← List.map_eq_flatMap]
        rw [Nat.digits_of_two_le_of_pos (by decide) hp]
        have hm : (2 * a + e) % 2 = e := by omega
        have hd : (2 * a + e) / 2 = a := by omega
        rw [hm, hd]
        rw [List.map_cons, List.mapIdx_cons]
        simpa only [List.sum_cons, pow_zero, mul_one] using
          congrArg ((e : ℤ) + ·) (shift ((Nat.digits 2 a).map Nat.cast))
    induction k generalizing u with
    | zero =>
        have : u = 0 := by simpa using hu
        subst u
        simp [digitSum]
    | succ k ih =>
        have hu' : u / 2 < 2 ^ k := by
          rw [pow_succ] at hu
          omega
        have he : u % 2 < 2 := Nat.mod_lt _ (by decide)
        have hsplit : 2 ^ (k + 1) * v + u =
            2 * (2 ^ k * v + u / 2) + u % 2 := by
          rw [pow_succ]
          calc
            2 ^ k * 2 * v + u = 2 * (2 ^ k * v) + u := by ring
            _ = 2 * (2 ^ k * v + u / 2) + u % 2 := by omega
        rw [hsplit, step _ _ he, ih _ hu']
        have huSplit : u = 2 * (u / 2) + u % 2 := by omega
        have huStep := step (u / 2) (u % 2) he
        rw [← huSplit] at huStep
        rw [huStep, pow_succ]
        ring
  have threshold_residue (k : ℕ) :
      3 * threshold k + k % 2 = 2 ^ (k + 2) + 2 := by
    have rem (j : ℕ) : 2 ^ (j + 2) % 3 = 1 + j % 2 := by
      induction j with
      | zero => decide
      | succ j ih =>
          rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ, Nat.mul_mod, ih]
          have h := Nat.mod_lt j (by decide : 0 < 2)
          rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with he | he
          · have hs : (j + 1) % 2 = 1 := by omega
            rw [he, hs]
          · have hs : (j + 1) % 2 = 0 := by omega
            rw [he, hs]
    have hm : (2 ^ (k + 2) + 2) % 3 = k % 2 := by
      rw [Nat.add_mod, rem]
      have := Nat.mod_lt k (by decide : 0 < 2)
      omega
    unfold threshold
    have := Nat.mod_add_div (2 ^ (k + 2) + 2) 3
    omega
  have hn8 : 8 ≤ n := by
    by_contra h
    have hb : ∀ i : Fin 8, 2 ≤ i.val → ∃ k : Fin 3,
        i.val + 1 = threshold k.val ∨ i.val = threshold k.val ∨
          i.val = threshold k.val + 1 := by decide
    obtain ⟨k, hk⟩ := hb ⟨n, by omega⟩ hn
    exact hout ⟨k.val, hk⟩
  have hexists : ∃ a : ℕ, 3 ≤ a ∧ n ≤ threshold a + 1 := by
    refine ⟨n + 3, by omega, ?_⟩
    have h := threshold_residue (n + 3)
    have hp : 2 ^ (n + 3 + 2) = 32 * 2 ^ n := by
      rw [show n + 3 + 2 = n + 5 by omega, pow_add]
      ring
    rw [hp] at h
    have hb : n < 2 ^ n := Nat.lt_two_pow_self
    have hm := Nat.mod_lt (n + 3) (by decide : 0 < 2)
    omega
  let l := Nat.find hexists
  have hl : 3 ≤ l := (Nat.find_spec hexists).1
  have hupper : n ≤ threshold l + 1 := (Nat.find_spec hexists).2
  have hlo : threshold (l - 1) + 2 ≤ n := by
    by_cases he : l = 3
    · rw [he]
      exact hn8
    · have hp : 3 ≤ l - 1 := by omega
      have hmin := Nat.find_min hexists (show l - 1 < l by omega)
      have hprev : ¬n ≤ threshold (l - 1) + 1 := fun h => hmin ⟨hp, h⟩
      omega
  have hhi : n ≤ threshold l - 2 := by
    have h1 : n + 1 ≠ threshold l := fun h => hout ⟨l, Or.inl h⟩
    have h2 : n ≠ threshold l := fun h => hout ⟨l, Or.inr (Or.inl h)⟩
    have h3 : n ≠ threshold l + 1 := fun h => hout ⟨l, Or.inr (Or.inr h)⟩
    omega
  have split (k q r : ℕ) (hr : r < 2 ^ k) := digitSum_block k q r (-2) hr
  have dot_split (k : ℕ) (v : ℕ → ℤ) (q r : ℕ) (hr : r < 2 ^ k) :
      (∑ j ∈ Finset.range (2 ^ k), digitSum (2 ^ k * q + r + j) (-2) * v j) =
        (∑ j ∈ Finset.range (2 ^ k), digitSum (r + j) (-2) * v j) +
          (-2) ^ k * digitSum q (-2) * (∑ j ∈ Finset.range (2 ^ k), v j) +
          (-2) ^ k * (digitSum (q + 1) (-2) - digitSum q (-2) - 1) *
            (∑ j ∈ Finset.range (2 ^ k), if 2 ^ k ≤ r + j then v j else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < 2 ^ k := Finset.mem_range.mp hj
    by_cases hc : 2 ^ k ≤ r + j
    · have hrem : r + j - 2 ^ k < 2 ^ k := by omega
      have heq : 2 ^ k * q + r + j =
          2 ^ k * (q + 1) + (r + j - 2 ^ k) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have heq' : r + j = 2 ^ k * 1 + (r + j - 2 ^ k) := by omega
      have hbig := split k (q + 1) (r + j - 2 ^ k) hrem
      rw [← heq] at hbig
      have hsmall := split k 1 (r + j - 2 ^ k) hrem
      rw [← heq'] at hsmall
      have hone : digitSum 1 (-2) = 1 := by decide
      rw [hbig, hsmall, hone, if_pos hc]
      ring
    · have hrem : r + j < 2 ^ k := by omega
      rw [show 2 ^ k * q + r + j = 2 ^ k * q + (r + j) by omega,
        split _ _ _ hrem, if_neg hc]
      ring
  have kernel : ∀ a : ℕ, 3 ≤ a → ∃ v : ℕ → ℤ,
      v 0 = 1 ∧
      (∀ j, threshold (a - 1) + 2 ≤ j → v j = 0) ∧
      (∑ j ∈ Finset.range (2 ^ a), v j) = 0 ∧
      (∀ i, i < 2 ^ a →
        (∑ j ∈ Finset.range (2 ^ a), digitSum (i + j) (-2) * v j) = 0) := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro ha
      by_cases h3 : a = 3
      · subst a
        let v : ℕ → ℤ := fun j => [1, -1, -1, 1, 1, -1, -1, 1].getD j 0
        refine ⟨v, by decide, ?_, by decide, ?_⟩
        · intro j hj
          have hj' : 8 ≤ j := by exact hj
          simp only [v, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simpa using hj')]
          rfl
        · have hb : ∀ i : Fin 8,
              (∑ j ∈ Finset.range 8, digitSum (i.val + j) (-2) * v j) = 0 := by
            decide
          intro i hi
          exact hb ⟨i, hi⟩
      by_cases h4 : a = 4
      · subst a
        let v : ℕ → ℤ := fun j =>
          [1, -2, 2, -2, 1, 0, 0, 0, 1, -2, 2, -2, 1].getD j 0
        refine ⟨v, by decide, ?_, by decide, ?_⟩
        · intro j hj
          have hj' : 13 ≤ j := by exact hj
          simp only [v, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simpa using hj')]
          rfl
        · have hb : ∀ i : Fin 16,
              (∑ j ∈ Finset.range 16, digitSum (i.val + j) (-2) * v j) = 0 := by
            decide
          intro i hi
          exact hb ⟨i, hi⟩
      have hm : 3 ≤ a - 2 := by omega
      obtain ⟨v, hv0, hvt, hvs, hvk⟩ := ih (a - 2) (by omega) hm
      let m := a - 2
      let P := 2 ^ m
      change ∀ j, threshold (m - 1) + 2 ≤ j → v j = 0 at hvt
      change (∑ j ∈ Finset.range P, v j) = 0 at hvs
      change ∀ i, i < P →
        (∑ j ∈ Finset.range P, digitSum (i + j) (-2) * v j) = 0 at hvk
      have haeq : a = m + 2 := by dsimp [m]; omega
      have hP : 8 ≤ P := by
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
      have hPpos : 0 < P := by omega
      have hsize : 2 ^ a = 4 * P := by rw [haeq, pow_add]; dsimp [P]; ring
      have ht : threshold (m - 1) + 2 ≤ P := by
        have h := threshold_residue (m - 1)
        have hp : 2 ^ (m - 1 + 2) = 2 * P := by
          rw [show m - 1 + 2 = m + 1 by omega, pow_succ]
          dsimp [P]
          ring
        rw [hp] at h
        omega
      have hnewt : threshold (a - 1) + 2 = 2 * P + (threshold (m - 1) + 2) := by
        have h := threshold_residue (m - 1)
        have h' := threshold_residue (a - 1)
        have hp : 2 ^ (m - 1 + 2) = 2 * P := by
          rw [show m - 1 + 2 = m + 1 by omega, pow_succ]
          dsimp [P]
          ring
        have hp' : 2 ^ (a - 1 + 2) = 8 * P := by
          rw [show a - 1 + 2 = m + 3 by omega, pow_add]
          dsimp [P]
          ring
        rw [hp] at h
        rw [hp'] at h'
        omega
      let V : ℕ → ℤ := fun j =>
        if j < P then v j else if 2 * P ≤ j ∧ j < 3 * P then v (j - 2 * P) else 0
      have V0 (j : ℕ) (hj : j < P) : V j = v j := by simp [V, hj]
      have V1 (j : ℕ) (hj : j < P) : V (P + j) = 0 := by
        have h₁ : ¬P + j < P := by omega
        have h₂ : ¬(2 * P ≤ P + j ∧ P + j < 3 * P) := by omega
        simp [V, h₁, h₂]
      have V2 (j : ℕ) (hj : j < P) : V (2 * P + j) = v j := by
        have h₁ : ¬2 * P + j < P := by omega
        have h₂ : 2 * P ≤ 2 * P + j ∧ 2 * P + j < 3 * P := by omega
        simp [V, h₁, h₂]
      have V3 (j : ℕ) (hj : j < P) : V (3 * P + j) = 0 := by
        have h₁ : ¬3 * P + j < P := by omega
        simp [V, h₁]
      have Vsum (f : ℕ → ℤ) :
          (∑ j ∈ Finset.range (4 * P), f j * V j) =
            (∑ j ∈ Finset.range P, f j * v j) +
              (∑ j ∈ Finset.range P, f (2 * P + j) * v j) := by
        have partition (b : ℕ) :
            (∑ j ∈ Finset.range (b * P), f j * V j) =
              ∑ q ∈ Finset.range b,
                ∑ j ∈ Finset.range P, f (q * P + j) * V (q * P + j) := by
          induction b with
          | zero => simp
          | succ b hb => rw [Nat.succ_mul, Finset.sum_range_add, hb,
              Finset.sum_range_succ]
        rw [partition]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_mul, zero_add, one_mul]
        have e0 := Finset.sum_congr rfl (fun j hj =>
          congrArg (f j * ·) (V0 j (Finset.mem_range.mp hj)))
        have e1 := Finset.sum_congr rfl (fun j hj =>
          congrArg (f (P + j) * ·) (V1 j (Finset.mem_range.mp hj)))
        have e2 := Finset.sum_congr rfl (fun j hj =>
          congrArg (f (2 * P + j) * ·) (V2 j (Finset.mem_range.mp hj)))
        have e3 := Finset.sum_congr rfl (fun j hj =>
          congrArg (f (3 * P + j) * ·) (V3 j (Finset.mem_range.mp hj)))
        rw [e0, e1, e2, e3]
        simp
      refine ⟨V, ?_, ?_, ?_, ?_⟩
      · exact (V0 0 hPpos).trans hv0
      · intro j hj
        rw [hnewt] at hj
        have hjP : ¬j < P := by omega
        dsimp [V]
        rw [if_neg hjP]
        split_ifs with h
        · exact hvt _ (by omega)
        · rfl
      · rw [hsize]
        have h := Vsum (fun _ => 1)
        simpa only [one_mul, hvs, add_zero] using h
      · intro i hi
        rw [hsize] at hi ⊢
        rw [Vsum]
        have hr : i % P < P := Nat.mod_lt _ hPpos
        have heq : i = P * (i / P) + i % P := by
          have := Nat.mod_add_div i P
          omega
        rw [heq]
        conv_lhs => enter [2, 2, j]; rw [show
          P * (i / P) + i % P + (2 * P + j) =
            P * (i / P + 2) + i % P + j by ring]
        rw [dot_split m v (i / P) (i % P) hr,
          dot_split m v (i / P + 2) (i % P) hr, hvs, hvk _ hr]
        have hf : ∀ q : Fin 4,
            (digitSum (q.val + 1) (-2) - digitSum q.val (-2) - 1) +
              (digitSum (q.val + 3) (-2) - digitSum (q.val + 2) (-2) - 1) = 0 := by
          decide
        have hq : i / P < 4 := (Nat.div_lt_iff_lt_mul hPpos).mpr hi
        have hpair := hf ⟨i / P, hq⟩
        rw [show i / P + 2 + 1 = i / P + 3 by omega]
        simp only [mul_zero, add_zero, zero_add]
        rw [← add_mul, ← mul_add, hpair, mul_zero, zero_mul]
  obtain ⟨v, hv0, hvt, hvs, hvk⟩ := kernel l hl
  have hP : 8 ≤ 2 ^ l := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl
  have ht : threshold (l - 1) + 2 ≤ 2 ^ l := by
    have h := threshold_residue (l - 1)
    rw [show l - 1 + 2 = l + 1 by omega, pow_succ] at h
    omega
  have hcover : n ≤ 2 ^ l + (2 ^ l - (threshold (l - 1) + 2)) + 1 := by
    have h := threshold_residue (l - 1)
    have h' := threshold_residue l
    rw [show l - 1 + 2 = l + 1 by omega, pow_succ] at h
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ, pow_succ] at h'
    have := Nat.mod_lt l (by decide : 0 < 2)
    omega
  have hk (i : ℕ) (hi : i < n) :
      (∑ j ∈ Finset.range (2 ^ l), digitSum (i + j) (-2) * v j) = 0 := by
    by_cases hiP : i < 2 ^ l
    · exact hvk i hiP
    · let r := i - 2 ^ l
      have hr : r < 2 ^ l := by dsimp [r]; omega
      have heq : i = 2 ^ l * 1 + r := by dsimp [r]; omega
      rw [heq, dot_split l v 1 r hr, hvs, hvk r hr]
      have hc : (∑ j ∈ Finset.range (2 ^ l), if 2 ^ l ≤ r + j then v j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        split_ifs with h
        · exact hvt j (by dsimp [r] at h; omega)
        · rfl
      rw [hc]
      ring
  have hnpos : 0 < n := by omega
  let x : Fin n → ℤ := fun j => v j.val
  have hx : (Matrix.of fun i j : Fin n => digitSum (i + j) (-2)) *ᵥ x = 0 := by
    ext i
    change (∑ j : Fin n, digitSum (i.val + j.val) (-2) * v j.val) = 0
    rw [Fin.sum_univ_eq_sum_range (fun j => digitSum (i.val + j) (-2) * v j) n]
    have hs : (∑ j ∈ Finset.range n, digitSum (i.val + j) (-2) * v j) =
        ∑ j ∈ Finset.range (2 ^ l), digitSum (i.val + j) (-2) * v j := by
      by_cases hnP : n ≤ 2 ^ l
      · apply Finset.sum_subset (Finset.range_mono hnP)
        intro j hj hjn
        rw [hvt j (by have := Finset.mem_range.not.mp hjn; omega), mul_zero]
      · symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hjP
        rw [hvt j (by have := Finset.mem_range.not.mp hjP; omega), mul_zero]
    rw [hs]
    exact hk i.val i.isLt
  by_contra h
  have hz := Matrix.eq_zero_of_mulVec_eq_zero h hx
  have hz0 := congrFun hz (⟨0, hnpos⟩ : Fin n)
  change v 0 = 0 at hz0
  omega

end D5.S3.Combinatorics.DigitHankel.BinaryDigitHankel
