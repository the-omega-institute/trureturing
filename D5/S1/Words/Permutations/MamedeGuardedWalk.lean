/- GID: D5/S1/Words/Permutations/MamedeGuardedWalk
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeGuardedWalk
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A guarded consecutive walk contains the forced descending block. -/

import D5.S1.Words.Permutations.MamedeAdjacentWords

namespace D5.S1.Words.Permutations.MamedeGuardedWalk

open D5.S1.Words.Permutations.MamedeAdjacentWords

def leftStep (t k : Nat) : Nat := if k + 1 = t then k else t

def traceEnd (t : Nat) : List Nat → Nat
  | [] => t
  | k :: w => traceEnd (leftStep t k) w

def leftOnly (t : Nat) : List Nat → Prop
  | [] => True
  | k :: w => k ≠ t ∧ leftOnly (leftStep t k) w

theorem traceEnd_le (t : Nat) (w : List Nat) : traceEnd t w ≤ t := by
  induction w generalizing t with
  | nil => exact Nat.le_refl t
  | cons k w ih =>
    exact (ih (leftStep t k)).trans (by unfold leftStep; split <;> omega)

private theorem right_barrier (t k : Nat) (w : List Nat)
    (hc : consecutive (k :: w)) (hl : leftOnly t (k :: w)) (hk : t < k) :
    traceEnd t (k :: w) = t ∧ (∀ a, a ∈ k :: w → t < a) := by
  induction w generalizing t k with
  | nil => simp [traceEnd, leftStep, leftOnly] at *; omega
  | cons l w ih =>
    have hs : leftStep t k = t := by simp [leftStep]; omega
    have hne : l ≠ t := by simpa [leftOnly, hs] using hl.2.1
    have hlk : t < l := by obtain h | h := hc.1 <;> omega
    have htail : leftOnly t (l :: w) := by simpa [leftOnly, hs] using hl.2
    obtain ⟨hEnd, hAll⟩ := ih t l hc.2 htail hlk
    exact ⟨by simpa [traceEnd, hs] using hEnd,
      by
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hk
        · exact hAll a (List.mem_cons.mpr ha)⟩

/-- A consecutive word whose strand can only move left from `j+1` to `i`
    contains the full descending run `j,j-1,...,i`. -/
theorem forced_descent (w : List Nat) (i j : Nat) (hij : i ≤ j)
    (hc : consecutive w) (hl : leftOnly (j + 1) w)
    (he : traceEnd (j + 1) w = i) :
    ∃ p q, w = p ++ descending j i ++ q ∧
      (∀ k, k ∈ p → k < j) ∧ (∀ k, k ∈ q → i < k) := by
  have descending_step (a b : Nat) (h : a < b) :
      descending b a = b :: descending (b - 1) a := by
    have hn : b - a + 1 = ((b - 1) - a + 1) + 1 := by omega
    unfold descending
    rw [hn, List.range_succ_eq_map]
    simp only [List.map_cons, Nat.sub_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hb := List.mem_range.mp hk
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  induction w generalizing i j with
  | nil => simp [traceEnd] at he; omega
  | cons a w ih =>
    by_cases haj : a < j
    · have hs : leftStep (j + 1) a = j + 1 := by simp [leftStep]; omega
      have hct : consecutive w := by cases w <;> simp_all [consecutive]
      have hlt : leftOnly (j + 1) w := by simpa [leftOnly, hs] using hl.2
      have het : traceEnd (j + 1) w = i := by simpa [traceEnd, hs] using he
      obtain ⟨p, q, hw, hp, hq⟩ := ih i j hij hct hlt het
      refine ⟨a :: p, q, ?_, ?_, hq⟩
      · simp [hw]
      · intro k hk; simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact haj
        · exact hp k hk
    · by_cases hae : a = j
      · subst a
        have hs : leftStep (j + 1) j = j := by simp [leftStep]
        have hlt : leftOnly j w := by simpa [leftOnly, hs] using hl.2
        have het : traceEnd j w = i := by simpa [traceEnd, hs] using he
        by_cases hei : i = j
        · have hetj : traceEnd j w = j := het.trans hei
          have hq : ∀ k, k ∈ w → j < k := by
            cases w with
            | nil => simp
            | cons k w =>
              have hk : j < k := by
                obtain h | h := hc.1
                · omega
                · have hstep : leftStep j k = k := by simp [leftStep, h]
                  have hb := traceEnd_le k w
                  change traceEnd (leftStep j k) w = j at hetj
                  rw [hstep] at hetj
                  omega
              exact (right_barrier j k w hc.2 hlt hk).2
          refine ⟨[], w, ?_, by simp, ?_⟩
          · simp [hei, descending]
          · simpa only [hei] using hq
        · have hij' : i ≤ j - 1 := by omega
          have hj : (j - 1) + 1 = j := by omega
          have hct : consecutive w := by cases w <;> simp_all [consecutive]
          obtain ⟨p, q, hw, hp, hq⟩ := ih i (j - 1) hij' hct (hj.symm ▸ hlt) (hj.symm ▸ het)
          cases p with
          | nil =>
            refine ⟨[], q, ?_, by simp, hq⟩
            simp only [List.nil_append] at hw
            rw [descending_step i j (by omega), hw]
            simp
          | cons k p =>
            have hk : k < j - 1 := hp k (by simp)
            rw [hw] at hc
            obtain h | h := hc.1 <;> omega
      · have ha : j + 1 < a := by have hn := hl.1; omega
        have hb := (right_barrier (j + 1) a w hc hl ha).1
        omega

#print axioms traceEnd_le
#print axioms right_barrier
#print axioms forced_descent

end D5.S1.Words.Permutations.MamedeGuardedWalk
