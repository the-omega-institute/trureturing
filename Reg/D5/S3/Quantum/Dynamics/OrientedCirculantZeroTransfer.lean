import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
open _root_.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State p := ZMod p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v.val) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original claim; only the selected source operand is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ (∀ (n : ℕ) [NeZero n], n % 4 = 2 → ∀ C : Finset (ZMod n),
    Oriented C → Connected C → ∀ v : ZMod n,
    ZeroTransfer n C v 0 ∧ ZeroTransfer n C 0 v → Odd (O.readout () n v))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro n _ _ C _ _ v _
  exact ⟨0, rfl⟩

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change (0 : ZMod 2).val ≠ (1 : ZMod 2).val
    decide +kernel

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ v => v.val) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Dynamics") "OrientedCirculantZeroTransfer") "result") "Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer/Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ v => v.val) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, definition := some { owner := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer, name := `D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer.claim, path := #["arg"] }, coordinates := #[0], readouts := #[{ path := #["arg", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.OrientedCirculantZeroTransfer
