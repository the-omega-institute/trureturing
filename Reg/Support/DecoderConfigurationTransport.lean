import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

namespace Reg.Support.DecoderConfigurationTransport
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
universe u v
variable {C : Type u} {D : Type v} {I O : Type}

/-- Reindex readable configurations without changing acquired inputs or emitted outputs. -/
def frame (e : C ≃ D) (s : Frame C O) : Frame D O :=
  ⟨e s.state,s.acquired,s.output⟩

def action (e : C ≃ D) (a : C → Op C I O) (d : D) : Op D I O :=
  match a (e.symm d) with
  | .internal c out => .internal (e c) out
  | .acquire f => .acquire (fun i => (f i).map (fun q => (e q.1,q.2)))
  | .stopped => .stopped

theorem step (e : C ≃ D) (a : C → Op C I O) (input : ℕ → Option I)
    {s t : Frame C O} (h : Step a input s t) :
    Step (action e a) input (frame e s) (frame e t) := by
  cases h with
  | internal c d q out batch instruction =>
    exact .internal _ _ _ _ _ (by simp [action,instruction])
  | acquire c d q out batch f i instruction available result =>
    exact .acquire _ _ _ _ _ (fun j => (f j).map (fun q => (e q.1,q.2))) i
      (by simp [action,instruction]) available
      (by simp [result])

theorem run (e : C ≃ D) (a : C → Op C I O) (input : ℕ → Option I)
    {s t : Frame C O} (h : Run a input s t) :
    Run (action e a) input (frame e s) (frame e t) := by
  apply run_closure.mpr
  have closure := run_closure.mp h
  clear h
  induction closure with
  | refl => exact .refl
  | tail trace edge ih => exact ih.tail (step e a input edge)

theorem inverse_action (e : C ≃ D) (a : C → Op C I O) :
    action e.symm (action e a) = a := by
  funext c
  simp only [action,Equiv.symm_symm,Equiv.symm_apply_apply]
  cases a c with
  | internal d out => simp
  | stopped => rfl
  | acquire f =>
    dsimp only
    apply congrArg Op.acquire
    funext i
    cases f i with
    | none => rfl
    | some pair => simp

theorem run_inverse (e : C ≃ D) (a : C → Op C I O) (input : ℕ → Option I)
    {s t : Frame D O} (h : Run (action e a) input s t) :
    Run a input (frame e.symm s) (frame e.symm t) := by
  simpa only [inverse_action] using run e.symm (action e a) input h

#print axioms run
#print axioms run_inverse
end Reg.Support.DecoderConfigurationTransport
