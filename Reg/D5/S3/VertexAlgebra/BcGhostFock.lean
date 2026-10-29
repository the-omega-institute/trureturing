import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.BcGhostFock

/-! A source-family audit candidate for the all-integer mixed ghost relation. -/

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.BcGhostFock

open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.VertexAlgebra.BcGhostFock
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ n m => b m * c n + c n * b m) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m n : ℤ, R.readout () n m =
    if m+n = 0 then (1 : Module.End ℂ Fock) else 0

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0 0
  change (0 : Module.End ℂ Fock) = if (0 : ℤ)+0 = 0 then 1 else 0 at hz
  simpa using hz

def family : Registration arena (type_of% @ghost_mixed_car) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghost_mixed_car, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨0, 0, 1, ?_⟩
    change b 0 * c 0 + c 0 * b 0 ≠ b 1 * c 0 + c 0 * b 1
    rw [ghost_mixed_car, ghost_mixed_car]
    norm_num

def mixed_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ghost_mixed_car) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostFock.mixedUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n m => b m * c n + c n * b m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFock
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.BcGhostFock
