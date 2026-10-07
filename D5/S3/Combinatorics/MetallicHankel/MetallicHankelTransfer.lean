/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer
   mirror-E: none(waiver:two-state-transfer-word)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Repeated triples give identity monodromy and bounded intermediate scalar states. -/

import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer

/-- Top coefficients and numerator signs of the rotated metallic block. -/
def topWord (n : ℕ) : List (ℤ × ℤ) :=
  if n = 2 then
    [(2, -1), (0, 1), (0, -1), (1, -1), (0, -1), (0, -1), (2, 1), (-1, -1)]
  else
    [(2, -1), (0, 1)] ++
      (List.replicate (n - 2) [(1, -1), (1, -1), (-1, -1)]).flatten ++
      [(0, -1), (1, -1), (0, -1), (-1, -1)] ++
      (List.replicate (n - 3) [(1, -1), (1, -1), (-1, -1)]).flatten ++
      [(1, -1), (1, -1), (0, -1), (2, 1), (-1, -1)]

/-- Triple induction proves monodromy and bounds every intermediate transfer state. -/
theorem block_transfer (n : ℕ) (hn : 2 ≤ n) (state : ℕ → ℤ × ℤ)
    (initial : state 0 = (1, 0))
    (recurrence : ∀ p, state (p + 1) =
      let a := (topWord n)[p % (topWord n).length]!
      (a.1 * (state p).1 - a.2 * (state p).2, (state p).1)) :
    ∀ p, state (p + (topWord n).length) = state p ∧
      (state p).1 ∈ ({-1, 0, 1, 2} : Finset ℤ) ∧
        (state p).2 ∈ ({-1, 0, 1, 2} : Finset ℤ) := by
  let step (z a : ℤ × ℤ) : ℤ × ℤ := (a.1 * z.1 - a.2 * z.2, z.1)
  let bounded (z : ℤ × ℤ) : Prop :=
    z.1 ∈ ({-1, 0, 1, 2} : Finset ℤ) ∧ z.2 ∈ ({-1, 0, 1, 2} : Finset ℤ)
  let triple : List (ℤ × ℤ) := [(1, -1), (1, -1), (-1, -1)]
  let reps (m : ℕ) := (List.replicate m triple).flatten
  have repeat_action (m : ℕ) (z : ℤ × ℤ) :
      (reps m).foldl step z =
        ((-1) ^ m * z.1, (1 - (-1) ^ m) * z.1 + z.2) := by
    induction m generalizing z with
    | zero => simp [reps]
    | succ m ih =>
      simp only [reps, List.replicate_succ, List.flatten_cons, List.foldl_append]
      rw [ih]
      simp only [triple, List.foldl_cons, List.foldl_nil, step, pow_succ]
      ext <;> ring
  have repeat_safe (m : ℕ) : ∀ z : ℤ × ℤ, z = (-1, 2) ∨ z = (1, 0) →
      ((reps m).foldl step z = (-1, 2) ∨ (reps m).foldl step z = (1, 0)) ∧
        ∀ w ∈ (reps m).scanl step z, bounded w := by
    induction m with
    | zero =>
      intro z hz
      refine ⟨by simpa [reps] using hz, ?_⟩
      intro w hw
      have hwz : w = z := by simpa [reps] using hw
      subst w
      rcases hz with rfl | rfl <;> norm_num [bounded]
    | succ m ih =>
      intro z hz
      have ht : triple.foldl step z = (-1, 2) ∨ triple.foldl step z = (1, 0) := by
        rcases hz with rfl | rfl <;> norm_num [triple, step]
      have hb : ∀ w ∈ triple.scanl step z, bounded w := by
        rcases hz with rfl | rfl <;>
          simp [triple, step, bounded, List.scanl_cons, List.scanl_nil]
      obtain ⟨he, hi⟩ := ih (triple.foldl step z) ht
      refine ⟨by simpa [reps, List.replicate_succ, List.foldl_append] using he, ?_⟩
      intro w hw
      simp only [reps, List.replicate_succ, List.flatten_cons, List.scanl_append,
        List.mem_append] at hw
      rcases hw with hw | hw
      · exact hb w hw
      · exact hi w (List.mem_of_mem_tail hw)
  have append_safe (a b : List (ℤ × ℤ)) (z : ℤ × ℤ)
      (ha : ∀ w ∈ a.scanl step z, bounded w)
      (hb : ∀ w ∈ b.scanl step (a.foldl step z), bounded w) :
      ∀ w ∈ (a ++ b).scanl step z, bounded w := by
    intro w hw
    rw [List.scanl_append, List.mem_append] at hw
    exact hw.elim (ha w) (fun hw => hb w (List.mem_of_mem_tail hw))
  have base : (∀ z, (topWord n).foldl step z = z) ∧
      ∀ z ∈ (topWord n).scanl step (1, 0), bounded z := by
    by_cases hn2 : n = 2
    · subst n
      constructor
      · intro z
        simp only [topWord, ite_true, List.foldl_cons, List.foldl_nil]
        ext <;> ring
      · simp [topWord, step, bounded, List.scanl_cons, List.scanl_nil]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hw : topWord (m + 3) =
          [(2, -1), (0, 1)] ++ reps (m + 1) ++
            [(0, -1), (1, -1), (0, -1), (-1, -1)] ++ reps m ++
            [(1, -1), (1, -1), (0, -1), (2, 1), (-1, -1)] := by
        simp [topWord, reps, triple]
      have hsquare : ((-1 : ℤ) ^ m) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      constructor
      · intro z
        rw [hw]
        simp only [List.foldl_append]
        rw [repeat_action]
        simp only [List.foldl_cons, List.foldl_nil, step]
        rw [repeat_action]
        simp only [pow_succ]
        apply Prod.ext <;> simp only
        all_goals
          ring_nf
          simp
      · let head : List (ℤ × ℤ) := [(2, -1), (0, 1)]
        let middle : List (ℤ × ℤ) := [(0, -1), (1, -1), (0, -1), (-1, -1)]
        let last : List (ℤ × ℤ) := [(1, -1), (1, -1), (0, -1), (2, 1), (-1, -1)]
        have hhead : head.foldl step (1, 0) = (-1, 2) := by norm_num [head, step]
        have head_safe : ∀ w ∈ head.scanl step (1, 0), bounded w := by
          simp [head, step, bounded, List.scanl_cons, List.scanl_nil]
        obtain ⟨ho, hb⟩ := repeat_safe (m + 1) (-1, 2) (Or.inl rfl)
        have middle_action (z : ℤ × ℤ) : middle.foldl step z = z := by
          simp only [middle, List.foldl_cons, List.foldl_nil, step]
          ext <;> ring
        have middle_safe : ∀ w ∈ middle.scanl step ((reps (m + 1)).foldl step (-1, 2)),
            bounded w := by
          rcases ho with he | he <;>
            simp [he, middle, step, bounded, List.scanl_cons, List.scanl_nil]
        have hend :
            (reps m).foldl step ((reps (m + 1)).foldl step (-1, 2)) = (1, 0) := by
          rw [repeat_action, repeat_action]
          simp only [pow_succ]
          apply Prod.ext <;> simp only <;> nlinarith [hsquare]
        obtain ⟨_, hu⟩ := repeat_safe m _ ho
        have last_safe : ∀ w ∈ last.scanl step (1, 0), bounded w := by
          simp [last, step, bounded, List.scanl_cons, List.scanl_nil]
        have h1 := append_safe head (reps (m + 1)) (1, 0) head_safe
          (by simpa [hhead] using hb)
        have h2 := append_safe (head ++ reps (m + 1)) middle (1, 0) h1
          (by simpa only [List.foldl_append, hhead] using middle_safe)
        have h3 := append_safe (head ++ reps (m + 1) ++ middle) (reps m) (1, 0) h2
          (by simpa only [List.foldl_append, hhead, middle_action] using hu)
        have h4 := append_safe (head ++ reps (m + 1) ++ middle ++ reps m) last (1, 0) h3
          (by simpa only [List.foldl_append, hhead, middle_action, hend] using last_safe)
        simpa only [hw] using h4
  have length_pos : 0 < (topWord n).length := by
    by_cases hn2 : n = 2 <;> simp [topWord, hn2]
  have initial_segment : ∀ p, p ≤ (topWord n).length →
      state p = ((topWord n).take p).foldl step (1, 0) := by
    intro p
    induction p with
    | zero => simpa using initial
    | succ p ih =>
      intro hp
      have hlt : p < (topWord n).length := by omega
      rw [recurrence, Nat.mod_eq_of_lt hlt, getElem!_pos (topWord n) p hlt]
      rw [List.take_succ_eq_append_getElem hlt, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
  have period : ∀ p, state (p + (topWord n).length) = state p := by
    intro p
    induction p with
    | zero =>
      simpa [initial, base.1] using initial_segment (topWord n).length (by omega)
    | succ p ih =>
      rw [show p + 1 + (topWord n).length = (p + (topWord n).length) + 1 by omega]
      rw [recurrence, recurrence, ih, Nat.add_mod_right]
  have reduce : ∀ p, state p = state (p % (topWord n).length) := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      by_cases hp : p < (topWord n).length
      · rw [Nat.mod_eq_of_lt hp]
      · have hl : (topWord n).length ≤ p := by omega
        rw [← Nat.sub_add_cancel hl, period]
        rw [ih (p - (topWord n).length) (by omega)]
        rw [Nat.sub_add_cancel hl, ← Nat.mod_eq_sub_mod hl]
  intro p
  refine ⟨period p, ?_⟩
  rw [reduce p, initial_segment _ (Nat.le_of_lt (Nat.mod_lt p length_pos))]
  apply base.2
  have hlt : p % (topWord n).length <
      ((topWord n).scanl step (1, 0)).length := by
    rw [List.length_scanl]
    exact Nat.lt_succ_of_lt (Nat.mod_lt p length_pos)
  rw [← List.getElem_scanl hlt]
  exact List.getElem_mem hlt

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer
