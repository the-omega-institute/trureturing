import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityProfileRegion
import Reg.Support.DependentFamily

/-! The requested profile enters the attainable coupling event equalities. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityProfileRegion

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParityProfileRegion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 3 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

def zeroTarget : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Fin 3 → ℝ,
    (∃ w : Profile → Profile → ℝ, Feasible w ∧ ∀ i, commonMass w i = R.readout () () a i) ↔
      (∀ i, a i ≤ a (i+1) + a (i+2)) ∧ a 0 + a 1 + a 2 ≤ 1

private theorem zero_target_fails : ¬ arena.Law zeroTarget := by
  intro law
  let a (i : Fin 3) : ℝ := if i = 0 then 1 else 0
  obtain ⟨w, hw, zero⟩ := (attainable_iff (fun _ => 0)).mpr (by simp)
  have triangle := ((law a).mp ⟨w, hw, zero⟩).1 (0 : Fin 3)
  norm_num [a] at triangle

def family : Registration arena (type_of% (@attainable_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨attainable_iff, zeroTarget, zero_target_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroTarget, ?_, rfl, zero_target_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    intro eq
    exact zero_ne_one (congrFun eq (0 : Fin 3))

def parityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@attainable_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityProfileRegion.commonMassTarget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityProfileRegion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityProfileRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityProfileRegion
