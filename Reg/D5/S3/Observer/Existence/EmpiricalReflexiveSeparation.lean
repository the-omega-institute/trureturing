import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of normalized rank-one density projections. -/

namespace Reg.D5.S3.Observer.Existence.EmpiricalReflexiveSeparation

open _root_.D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.Quantum.Tomography.RankOneContextCommutator
  (IsNormalizedRankOneProjection)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the rank-one density matrix of an arbitrary qubit vector. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => rankOneDensity v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain normalization and all four rank-one projection laws. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (v : Fin 2 → ℂ) (_hv : star v ⬝ᵥ v = 1),
    IsNormalizedRankOneProjection (R.readout () () v)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hv : star (![1, 0] : Fin 2 → ℂ) ⬝ᵥ ![1, 0] = 1 := by
    norm_num [dotProduct, Fin.sum_univ_two]
  have ht := (h ![1, 0] hv).2.2.1
  change Matrix.trace (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 at ht
  simp at ht

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, (fun _ => 1), ?_⟩
  intro he
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) he
  norm_num [actual, realize, rankOneDensity, Matrix.vecMulVec_apply] at hc

def source_registration : Registration arena (type_of% @rankOneDensity_isNormalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rankOneDensity_isNormalized, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rankOneDensity_isNormalized) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.unit
  realizationName :=
    `Reg.D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => rankOneDensity v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
