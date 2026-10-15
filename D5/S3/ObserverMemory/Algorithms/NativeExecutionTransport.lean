/- GID: D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/NativeExecutionTransport
   mirror-E: none(waiver:native-execution)
   anchors: []
   utility: none
   digest: Native run transport permits address collisions and identifies halt endpoints. -/

import D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

universe u v w
variable {Q : Type u} {A : Type v} {R : Type w}

universe u' v'

/-- Reindex controls and map literal addresses; address collisions are permitted. -/
def Instruction.transport {Q' : Type u'} {A' : Type v'}
    (sigma : Q ≃ Q') (f : A → A') : Instruction Q A R → Instruction Q' A' R
  | .read p k => .read (f p) (sigma ∘ k)
  | .update z => .update (sigma z)
  | .halt => .halt

/-- A transported table consults the original instruction at the inverse control. -/
def transportProgram {Q' : Type u'} {A' : Type v'}
    (sigma : Q ≃ Q') (f : A → A') (prog : Q → Instruction Q A R)
    (x : Q') : Instruction Q' A' R :=
  Instruction.transport sigma f (prog (sigma.symm x))

/-- Exact instruction and observation compatibility transports native runs in both
 directions, with both endpoint epochs unchanged and no inverse on addresses. -/
theorem run_transport_iff {Q' : Type u'} {A' : Type v'}
    (sigma : Q ≃ Q') (f : A → A')
    {prog : Q → Instruction Q A R} {prog' : Q' → Instruction Q' A' R}
    {obs : Nat → A → R} {obs' : Nat → A' → R}
    (instructions : ∀ q, prog' (sigma q) = Instruction.transport sigma f (prog q))
    (responses : ∀ j p, obs' j (f p) = obs j p)
    {x y : Q} {a b : Nat} :
    Run prog obs x a y b ↔ Run prog' obs' (sigma x) a (sigma y) b := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl _ _
    | @read x p k a y b hop tail ih =>
        have step : prog' (sigma x) = .read (f p) (sigma ∘ k) := by
          rw [instructions, hop]; rfl
        exact .read step (by simpa [Function.comp_def, responses] using ih)
    | @update x z a y b hop tail ih =>
        have step : prog' (sigma x) = .update (sigma z) := by
          rw [instructions, hop]; rfl
        exact .update step ih
  · have reverse : ∀ {x' y' : Q'} {a b : Nat}, Run prog' obs' x' a y' b →
          Run prog obs (sigma.symm x') a (sigma.symm y') b := by
      intro x' y' a b path
      induction path with
      | refl => exact .refl _ _
      | @read x' p' k' a y' b hop tail ih =>
          have mapped : Instruction.transport sigma f (prog (sigma.symm x')) =
              .read p' k' := by
            have compatible := instructions (sigma.symm x')
            simp only [Equiv.apply_symm_apply] at compatible
            exact compatible.symm.trans hop
          cases source : prog (sigma.symm x') with
          | read p k =>
              simp only [source, Instruction.transport] at mapped
              cases mapped
              exact .read source (by simpa [Function.comp_def, responses] using ih)
          | update z => simp [source, Instruction.transport] at mapped
          | halt => simp [source, Instruction.transport] at mapped
      | @update x' z' a y' b hop tail ih =>
          have mapped : Instruction.transport sigma f (prog (sigma.symm x')) =
              .update z' := by
            have compatible := instructions (sigma.symm x')
            simp only [Equiv.apply_symm_apply] at compatible
            exact compatible.symm.trans hop
          cases source : prog (sigma.symm x') with
          | read p k => simp [source, Instruction.transport] at mapped
          | update z =>
              simp only [source, Instruction.transport] at mapped
              cases mapped
              exact .update source (by simpa using ih)
          | halt => simp [source, Instruction.transport] at mapped
    intro path
    simpa using reverse path

private theorem run_from_halt {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x y : Q} {a b : Nat} (path : Run prog obs x a y b) (halt : prog x = .halt) :
    x = y ∧ a = b := by
  cases path with
  | refl => exact ⟨rfl, rfl⟩
  | read hop _ => cases halt.symm.trans hop
  | update hop _ => cases halt.symm.trans hop

/-- Determinism identifies halt-ended native runs, not arbitrary finite prefixes. -/
theorem run_halt_unique {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x h h' : Q} {a J J' : Nat}
    (left : Run prog obs x a h J) (right : Run prog obs x a h' J')
    (halt : prog h = .halt) (halt' : prog h' = .halt) : h = h' ∧ J = J' := by
  induction left generalizing h' J' with
  | refl => exact run_from_halt right halt
  | read hop tail ih =>
      cases right with
      | refl => cases hop.symm.trans halt'
      | read other suffix =>
          cases hop.symm.trans other
          exact ih suffix halt halt'
      | update other _ => cases hop.symm.trans other
  | update hop tail ih =>
      cases right with
      | refl => cases hop.symm.trans halt'
      | read other _ => cases hop.symm.trans other
      | update other suffix =>
          cases hop.symm.trans other
          exact ih suffix halt halt'

#print axioms run_transport_iff
#print axioms run_halt_unique

end D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
