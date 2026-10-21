import LeanInformationAuditInterface.Contract.Registration
import D5.S1.DifferentialAlgebra.ExponentialTranscendence
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.DifferentialAlgebra.ExponentialTranscendence

open _root_.D5.S1.DifferentialAlgebra.ExponentialTranscendence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Polynomial (Polynomial ℚ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => exponentialEval p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Function.Injective (R.readout () ())

private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  change Function.Injective (fun _ : Polynomial (Polynomial ℚ) => (0 : PowerSeries ℚ)) at h
  have hh : (0 : Polynomial (Polynomial ℚ)) = 1 := h rfl
  exact zero_ne_one hh

def injection_family : Registration arena (type_of% exponentialEval_injective) where
  actual := actual
  bridge := by
    constructor <;> exact fun h => h
  variation := ⟨exponentialEval_injective, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : Polynomial (Polynomial ℚ)), (1 : Polynomial (Polynomial ℚ)), ?_⟩
    change exponentialEval 0 ≠ exponentialEval 1
    simp

def injection_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exponentialEval_injective (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.DifferentialAlgebra.ExponentialTranscendence.exponentialEval_injective
    "__information_unit"
  realizationName :=
    `Reg.D5.S1.DifferentialAlgebra.ExponentialTranscendence.injection_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨injection_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.DifferentialAlgebra.ExponentialTranscendence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def transcendental_family : Registration arena (type_of% exp_transcendental) where
  actual := actual
  bridge := by
    constructor
    · intro h
      exact transcendental_iff_injective.mp h
    · intro h
      exact transcendental_iff_injective.mpr h
  variation := ⟨transcendental_iff_injective.mp exp_transcendental, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : Polynomial (Polynomial ℚ)), (1 : Polynomial (Polynomial ℚ)), ?_⟩
    change exponentialEval 0 ≠ exponentialEval 1
    simp

def transcendental_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exp_transcendental (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.DifferentialAlgebra.ExponentialTranscendence.exp_transcendental
    "__information_unit"
  realizationName :=
    `Reg.D5.S1.DifferentialAlgebra.ExponentialTranscendence.transcendental_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨transcendental_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.DifferentialAlgebra.ExponentialTranscendence
