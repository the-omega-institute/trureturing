import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum

open _root_.D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := WalkState
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => walk n) (fun e => nomatch e)

def rejected (role : Fin 2) : Realization signature :=
  realize signature (fun i _ n => if i = role then walk 0 else walk n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (_hm : 1 ≤ m) (o : ℤ × ℤ),
    walk (m*m-1) = ⟨o,2*m-2,m-1⟩ →
    (∀ t, t < m → R.readout 0 () (m*m+t) =
      ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) (-1,t),2*m-1,t⟩) ∧
    (∀ t, t ≤ m → R.readout 1 () (m*m+m+t) =
      ⟨frame o (if m%2 = 0 then (-1:ℤ) else 1) ((t:ℤ)-1,m),2*m,t⟩)

private theorem rejected_law (role : Fin 2) : ¬ arena.Law (rejected role) := by
  intro law
  have h := law 1 (by decide) (0, 0) rfl
  fin_cases role
  · have h0 := congrArg WalkState.leg (h.1 0 (by decide))
    change (0 : ℕ) = 1 at h0
    omega
  · have h1 := congrArg WalkState.leg (h.2 0 (by decide))
    change (0 : ℕ) = 2 at h1
    omega

def sourceRegistration : Registration arena (type_of% (@layer_walk)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨layer_walk, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, ?_, rejected_law role⟩
      · intro other different
        funext p n
        exact (ite_eq_right different).symm
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hl := congrArg WalkState.leg he
    change (0 : ℕ) = 1 at hl
    omega

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@layer_walk) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum.layer_walk.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => walk n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "fn"]
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum
