/- GID: D5/S0/Computability/WindowAcquisitionFidelity
   generality: I
   mirror-B: D5/B/S0/Computability/WindowAcquisitionFidelity
   mirror-E: none(waiver:unbounded-operational-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Read-only source and literal canonical-register endpoint frame. -/

import D5.S0.Computability.WindowCanonicalAcquisition

namespace PhysicalWindowContinuation.CanonicalAcquisition
open RegisterHandoff
open D5.S3.Arith.FibonacciAtomic

theorem program_source_readonly (k : State) :
    match program k with
    | .write t _ _ => t ≠ sourceTrack
    | _ => True := by
  rcases k with k | k
  · cases k <;> simp [program,PhysicalWindowContinuation.program,baseAction,workTrack,sourceTrack]
  · cases k <;> simp only [program,portAction,RegisterHandoff.program]
    all_goals first
      | exact target_ne_source _
      | exact (by decide : workTrack ≠ sourceTrack)
      | trivial
      | split_ifs <;> trivial

theorem step_source (c : Config) : (step c).cell sourceTrack=c.cell sourceTrack := by
  have hs := program_source_readonly c.control
  cases he : program c.control with
  | read t f => simp [step,he]
  | write t b k =>
    simp only [he] at hs
    simp [step,he,Function.update_of_ne hs.symm]
  | move t d k => simp [step,he]
  | halt => simp [step,he]

theorem run_source (c : Config) (n : ℕ) : (run c n).cell sourceTrack=c.cell sourceTrack := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    change (step (run c n)).cell sourceTrack=_
    rw [step_source,ih]

theorem memory_other (m bs k) (t : Track) (ht : ∀ j : Lane,t ≠ target j) :
    memory m bs k t=m t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold memory
    split
    · rw [Function.update_of_ne (ht _),ih]
    · exact ih

theorem endpoint_frame (w : List Window) (e : Bool) :
    (registerEnd w e).cell sourceTrack=inputSource w e ∧
    (registerEnd w e).cell workTrack=word (Original.finalColumns w e) ∧
    (∀ t : Track,(∀ j : Lane,t ≠ target j) → t ≠ sourceTrack → t ≠ workTrack →
      (registerEnd w e).cell t=fun _=>.blank) ∧
    (∀ t : Track,(registerEnd w e).head t=if t=sourceTrack then w.length else 0) ∧
    (∀ j : Lane,(normalized ((Original.finalColumns w e).map (select j))).length ≤
      (Original.finalColumns w e).length+1) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change memory (packedEnd w e).cell (Original.finalColumns w e) 4 sourceTrack=_
    rw [memory_other _ _ _ _ (fun j=>(target_ne_source j).symm)]
    simp [packedEnd,boundary,workTrack,sourceTrack]
  · change memory (packedEnd w e).cell (Original.finalColumns w e) 4 workTrack=_
    rw [memory_work]
    simp [packedEnd,boundary]
  · intro t ht hs hw
    change memory (packedEnd w e).cell (Original.finalColumns w e) 4 t=_
    rw [memory_other _ _ _ _ ht]
    simp [packedEnd,boundary,hs,hw]
  · intro t
    by_cases hs : t=sourceTrack
    · subst t; simp [registerEnd,port,startAt,packedEnd,boundary,sourceTrack,workTrack]
    · simp [registerEnd,port,startAt,packedEnd,boundary,hs]
  · intro j
    simpa only [List.length_map] using normalized_length
      ((Original.finalColumns w e).map (select j))


end PhysicalWindowContinuation.CanonicalAcquisition
