/- GID: D5/S0/Computability/BinaryMachine/StackCompare
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackCompare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Counted all-word comparison of certificate and unary-budget lengths. -/

import D5.S0.Computability.BinaryMachine.StackControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.StackCompare
open StackMachine (Registers branch)
open StackProgram

def check {k : Nat} (src budget : Fin (k + 1)) : Program k (Fin 4) where
  start := 0
  code := fun q => if q = 0 then .pop src 2 1 1
    else if q = 1 then .pop budget 3 0 0
    else if q = 2 then .halt true else .halt false

/-- Every word is accepted exactly when its length fits the given budget. The
run consumes at most the two compared lengths, leaving other registers intact. -/
theorem exec_check {k : Nat} (src budget : Fin (k + 1)) (hne : src ≠ budget)
    (r : Registers k) :
    ∃ t out, t ≤ 2 * (r src).length + 3 ∧
      Exec (check src budget) (check src budget).start r t
        (decide ((r src).length ≤ (r budget).length), out) ∧
      ∀ a, a ≠ src → a ≠ budget → out a = r a := by
  generalize hw : r src = word
  induction word generalizing r with
  | nil =>
    have hs : StackMachine.set r src [] = r := by rw [← hw]; exact StackWords.set_unchanged r src
    refine ⟨2, r, by simp [hw], ?_, by intros; rfl⟩
    have hh : Exec (check src budget) 0 r 2 (true, r) := by
      apply Exec.next (q' := 2) (r' := r)
      · simp [StackProgram.step, check, hw, branch, hs]
      · exact .halt (by simp [StackProgram.step, check])
    simpa [check, hw] using hh
  | cons b word ih =>
    let r₀ := StackMachine.set r src word
    cases hb : r budget with
    | nil =>
      let out := StackMachine.set r₀ budget []
      refine ⟨3, out, by simp [hw], ?_, ?_⟩
      · have hh : Exec (check src budget) 0 r 3 (false, out) := by
          apply Exec.next (q' := 1) (r' := r₀)
          · cases b <;> simp [StackProgram.step, check, hw, branch, r₀]
          · apply Exec.next (q' := 3) (r' := out)
            · simp [StackProgram.step, check, r₀, Ne.symm hne, hb, branch, out]
            · exact .halt (by simp [StackProgram.step, check])
        simpa [check, hw, hb] using hh
      · intro a hs hd; simp [out, r₀, StackMachine.set, hs, hd]
    | cons c budgetTail =>
      let r₁ := StackMachine.set r₀ budget budgetTail
      obtain ⟨t, out, ht, he, hf⟩ := ih r₁ (by simp [r₁, r₀, hne])
      refine ⟨t + 2, out, ?_, ?_, ?_⟩
      · have ht' : t ≤ 2 * word.length + 3 := by simpa [r₁, r₀, hne] using ht
        simp [hw]; omega
      · have hh : Exec (check src budget) 0 r (t + 2)
            (decide (word.length ≤ budgetTail.length), out) := by
          apply Exec.next (q' := 1) (r' := r₀)
          · cases b <;> simp [StackProgram.step, check, hw, branch, r₀]
          · apply Exec.next (q' := 0) (r' := r₁)
            · cases c <;> simp [StackProgram.step, check, r₀, Ne.symm hne, hb, branch, r₁]
            · simpa [check, r₁, r₀, hne] using he
        simpa [check, hw, hb] using hh
      · intro a hs hd
        exact (hf a hs hd).trans (by simp [r₁, r₀, StackMachine.set, hs, hd])

end Complexity.StackCompare
