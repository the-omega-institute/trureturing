/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SignedWeight
   mirror-E: none(waiver:minimum-signed-power-representation)
   anchors: []
   utility: none
   digest: Minimum signed binary weight has exact scaling and odd recurrences. -/

/-
proof_shape: content (signed_weight_arithmetic)
escape_witness: Construction of optimal signed representations and a power-translation lower bound.
admission_basis: escape-witness
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Words.Palindromes.PeriodDoubling
private def greedyWeight (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else if n % 2 = 0 then greedyWeight (n / 2)
  else 1 + min (greedyWeight (n / 2)) (greedyWeight (n / 2 + 1))
termination_by n

noncomputable def signedWeight (x : ℤ) : ℕ :=
  sInf {k : ℕ | ∃ l : List (Bool × ℕ), l.length = k ∧
    (l.map (fun t => if t.1 then (2 : ℤ) ^ t.2 else -(2 : ℤ) ^ t.2)).sum = x}

theorem signed_weight_arithmetic :
    signedWeight 0 = 0 ∧ signedWeight 1 = 1 ∧
    (∀ x : ℤ, signedWeight (-x) = signedWeight x) ∧
    (∀ x y : ℤ, signedWeight (x + y) ≤ signedWeight x + signedWeight y) ∧
    (∀ x : ℤ, signedWeight (2 * x) = signedWeight x) ∧
    (∀ x : ℤ, signedWeight (2 * x + 1) =
      1 + min (signedWeight x) (signedWeight (x + 1))) := by
  have laws :
      (∀ n, greedyWeight (2 * n) = greedyWeight n) ∧
      (∀ n, greedyWeight (2 * n + 1) = 1 + min (greedyWeight n) (greedyWeight (n + 1))) ∧
      (∀ n, greedyWeight n ≤ greedyWeight (n + 1) + 1 ∧
        greedyWeight (n + 1) ≤ greedyWeight n + 1) := by
    have hz : greedyWeight 0 = 0 := by rw [greedyWeight]; rfl
    have ho : greedyWeight 1 = 1 := by rw [greedyWeight]; rfl
    have heven (n : ℕ) : greedyWeight (2 * n) = greedyWeight n := by
      by_cases h : n = 0
      · subst n; rfl
      · rw [greedyWeight, if_neg (by omega), if_pos (by omega)]
        congr 1
        omega
    have hodd (n : ℕ) :
        greedyWeight (2 * n + 1) = 1 + min (greedyWeight n) (greedyWeight (n + 1)) := by
      by_cases h : n = 0
      · subst n; simp [hz, ho]
      · rw [greedyWeight, if_neg (by omega), if_neg (by omega)]
        have hd : (2 * n + 1) / 2 = n := by omega
        rw [hd]
    refine ⟨heven, hodd, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n; simp [hz, ho]
      · let k := n / 2
        have hk : k < n := by dsimp [k]; omega
        have hi := ih k hk
        by_cases hm : n % 2 = 0
        · have he : n = 2 * k := by dsimp [k]; omega
          rw [he, heven, hodd]
          omega
        · have he : n = 2 * k + 1 := by dsimp [k]; omega
          have he' : n + 1 = 2 * (k + 1) := by omega
          rw [he', he, heven, hodd]
          omega
  have gz : greedyWeight 0 = 0 := by rw [greedyWeight]; rfl
  have go : greedyWeight 1 = 1 := by rw [greedyWeight]; rfl
  let C : ℤ → ℕ := fun x => greedyWeight x.natAbs
  have cneg (x : ℤ) : C (-x) = C x := by simp [C]
  have ceven (x : ℤ) : C (2 * x) = C x := by
    simpa [C, Int.natAbs_mul] using laws.1 x.natAbs
  have codd (x : ℤ) : C (2 * x + 1) = 1 + min (C x) (C (x + 1)) := by
    cases x with
    | ofNat n =>
      change C (2 * (n : ℤ) + 1) = 1 + min (C n) (C ((n : ℤ) + 1))
      have ha : 2 * (n : ℤ) + 1 = ((2 * n + 1 : ℕ) : ℤ) := by omega
      have hb : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      rw [ha, hb]
      simpa only [C, Int.natAbs_natCast] using laws.2.1 n
    | negSucc n =>
      have ha : 2 * Int.negSucc n + 1 = -((2 * n + 1 : ℕ) : ℤ) := by omega
      have hb : Int.negSucc n + 1 = -(n : ℤ) := by omega
      rw [ha, hb]
      simpa only [C, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_negSucc, Nat.succ_eq_add_one, Nat.min_comm] using laws.2.1 n
  have cadj (x : ℤ) : C x ≤ C (x + 1) + 1 ∧ C (x + 1) ≤ C x + 1 := by
    cases x with
    | ofNat n =>
      change C (n : ℤ) ≤ C ((n : ℤ) + 1) + 1 ∧ C ((n : ℤ) + 1) ≤ C (n : ℤ) + 1
      have hb : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      rw [hb]
      simpa only [C, Int.natAbs_natCast] using laws.2.2 n
    | negSucc n =>
      have hb : Int.negSucc n + 1 = -(n : ℤ) := by omega
      rw [hb]
      simpa [C, and_comm] using laws.2.2 n
  have cpow (k : ℕ) (x : ℤ) : C (x + 2 ^ k) ≤ C x + 1 := by
    induction k generalizing x with
    | zero => simpa using (cadj x).2
    | succ k ih =>
      let y := x / 2
      have hy0 := ih y
      have hy1 := ih (y + 1)
      by_cases hm : x % 2 = 0
      · have he : x = 2 * y := by dsimp [y]; omega
        have he' : x + 2 ^ (k + 1) = 2 * (y + 2 ^ k) := by rw [he, pow_succ]; ring
        rw [he', he, ceven, ceven]
        exact hy0
      · have he : x = 2 * y + 1 := by dsimp [y]; omega
        have he' : x + 2 ^ (k + 1) = 2 * (y + 2 ^ k) + 1 := by
          rw [he, pow_succ]; ring
        rw [he', he, codd, codd]
        have hsum : y + 2 ^ k + 1 = y + 1 + 2 ^ k := by omega
        rw [hsum]
        omega
  have cpowNeg (k : ℕ) (x : ℤ) : C (x - 2 ^ k) ≤ C x + 1 := by
    have h := cpow k (-x)
    have he : -x + 2 ^ k = -(x - 2 ^ k) := by ring
    simpa only [he, cneg] using h
  let val : Bool × ℕ → ℤ := fun t => if t.1 then 2 ^ t.2 else -2 ^ t.2
  have lower (l : List (Bool × ℕ)) : C (l.map val).sum ≤ l.length := by
    induction l with
    | nil => change greedyWeight 0 ≤ 0; rw [gz]
    | cons t l ih =>
      rcases t with ⟨b, k⟩
      have hp := cpow k (l.map val).sum
      have hn := cpowNeg k (l.map val).sum
      cases b <;> simp only [List.map_cons, List.sum_cons, List.length_cons, val,
        Bool.false_eq_true, ↓reduceIte] <;>
          (first | simpa [add_comm] using (hp.trans (by omega)) |
            simpa [sub_eq_add_neg, add_comm] using (hn.trans (by omega)))
  let up : Bool × ℕ → Bool × ℕ := fun t => (t.1, t.2 + 1)
  let flip : Bool × ℕ → Bool × ℕ := fun t => (!t.1, t.2)
  have valup (t : Bool × ℕ) : val (up t) = 2 * val t := by
    rcases t with ⟨b, k⟩
    cases b <;> simp [val, up, pow_succ] <;> ring
  have valflip (t : Bool × ℕ) : val (flip t) = -val t := by
    rcases t with ⟨b, k⟩
    cases b <;> simp [val, flip]
  have sumup (l : List (Bool × ℕ)) : (l.map up |>.map val).sum = 2 * (l.map val).sum := by
    induction l with
    | nil => simp
    | cons t l ih => simp only [List.map_cons, List.sum_cons, ih, valup, mul_add]
  have sumflip (l : List (Bool × ℕ)) : (l.map flip |>.map val).sum = -(l.map val).sum := by
    induction l with
    | nil => simp
    | cons t l ih => simp only [List.map_cons, List.sum_cons, ih, valflip, neg_add]
  have reps (n : ℕ) : ∃ l : List (Bool × ℕ), l.length = greedyWeight n ∧
      (l.map val).sum = (n : ℤ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hs : n ≤ 1
      · by_cases hz : n = 0
        · subst n
          exact ⟨[], by rw [gz]; rfl, rfl⟩
        · have hn : n = 1 := by omega
          subst n
          exact ⟨[(true, 0)], by rw [go]; rfl, rfl⟩
      · let k := n / 2
        have hk : k < n := by dsimp [k]; omega
        by_cases hm : n % 2 = 0
        · have he : n = 2 * k := by dsimp [k]; omega
          obtain ⟨l, hl, hv⟩ := ih k hk
          refine ⟨l.map up, ?_, ?_⟩
          · rw [List.length_map, hl, he, laws.1]
          · rw [sumup, hv]
            omega
        · have he : n = 2 * k + 1 := by dsimp [k]; omega
          have hk1 : k + 1 < n := by omega
          by_cases hw : greedyWeight k ≤ greedyWeight (k + 1)
          · obtain ⟨l, hl, hv⟩ := ih k hk
            refine ⟨(true, 0) :: l.map up, ?_, ?_⟩
            · simp only [List.length_cons, List.length_map, hl, he, laws.2.1,
                Nat.min_eq_left hw]
              omega
            · simp only [List.map_cons, List.sum_cons, sumup, hv]
              simp only [val, ↓reduceIte, pow_zero]
              omega
          · obtain ⟨l, hl, hv⟩ := ih (k + 1) hk1
            refine ⟨(false, 0) :: l.map up, ?_, ?_⟩
            · simp only [List.length_cons, List.length_map, hl, he, laws.2.1,
                Nat.min_eq_right (by omega : greedyWeight (k + 1) ≤ greedyWeight k)]
              omega
            · simp only [List.map_cons, List.sum_cons, sumup, hv]
              simp only [val, Bool.false_eq_true, ↓reduceIte, pow_zero]
              omega
  have repInt (x : ℤ) : ∃ l : List (Bool × ℕ), l.length = C x ∧ (l.map val).sum = x := by
    cases x with
    | ofNat n => simpa [C] using reps n
    | negSucc n =>
      obtain ⟨l, hl, hv⟩ := reps (n + 1)
      refine ⟨l.map flip, ?_, ?_⟩
      · simpa [C] using hl
      · rw [sumflip, hv]
        omega
  have minimum (x : ℤ) : signedWeight x = C x := by
    change sInf {k : ℕ | ∃ l : List (Bool × ℕ), l.length = k ∧ (l.map val).sum = x} = C x
    obtain ⟨l, hl, hv⟩ := repInt x
    apply Nat.le_antisymm
    · exact Nat.sInf_le ⟨l, hl, hv⟩
    · obtain ⟨ls, hlen, hval⟩ := Nat.sInf_mem (s := {k : ℕ | ∃ l : List (Bool × ℕ), l.length = k ∧ (l.map val).sum = x}) ⟨C x, l, hl, hv⟩
      have h := lower ls
      rw [hval, hlen] at h
      exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [minimum]; exact gz
  · rw [minimum]; exact go
  · intro x
    rw [minimum, minimum, cneg]
  · intro x y
    obtain ⟨l, hl, hv⟩ := repInt x
    obtain ⟨ls, hls, hvs⟩ := repInt y
    have hm : signedWeight (x + y) ≤ C x + C y := by
      apply Nat.sInf_le
      refine ⟨l ++ ls, ?_, ?_⟩
      · simp [hl, hls]
      · change ((l ++ ls).map val).sum = x + y
        simp [hv, hvs]
    simpa only [minimum] using hm
  · intro x
    rw [minimum, minimum, ceven]
  · intro x
    rw [minimum, minimum, minimum, codd]
#check greedyWeight

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.signed_weight_arithmetic
