import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d + 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} {A : CountMat n n} {Q : Type}
    (L : IncomingLift A Q),
    L.response 0 = ⊥ ∧ ∀ d, L.response d ≤ L.response (r.readout () () d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A : CountMat 1 1 := fun _ _ => 1
  let L : IncomingLift A Bool := {
    project := fun _ => 0
    onto := by intro i; exact ⟨false, (Fin.eq_zero i).symm⟩
    lift := fun e q => ⟨false, (Fin.eq_zero _).symm⟩ }
  have hstep := (h L).2 1
  have hrel : L.response 1 true false := by
    change L.responseReadout 1 true = L.responseReadout 1 false
    apply Prod.ext
    · rfl
    · funext i j path
      cases path with
      | cons edge tail =>
        simp [IncomingLift.responseReadout, IncomingLift.liftPath, L]
  have hbad := hstep hrel
  change (L.response 0) true false at hbad
  rw [(response_zero_and_step L).1] at hbad
  change (true : Bool) = false at hbad
  cases hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro n A Q L
    simpa [actual, realize] using response_zero_and_step L,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0 : Nat), (1 : Nat), ?_⟩
    change (1 : Nat) ≠ 2
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.response_zero_and_step) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "ResponseQuotientKernel") "response_zero_and_step") "Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel/Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d + 1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
