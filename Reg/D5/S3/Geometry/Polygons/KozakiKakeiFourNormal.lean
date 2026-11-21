import D5.S3.Geometry.Polygons.KozakiKakeiFourNormal
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Equality with the four-column matrix is an observation on the full matrix carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Geometry.Polygons.KozakiKakeiFourNormal

open _root_.D5.S3.Geometry.KozakiKakei
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit

noncomputable section
open Classical

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Chart K 2) (fun _ => Bool)

private def actual : Realization signature :=
  realize signature (fun _ _ Z => decide (Z = fourNormal)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ Z : Chart K 2, Normalized (by decide : 2 ≤ 2) Z ↔ R.readout () () Z = true

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have impossible := (h fourNormal).mp ((normalized_four_iff fourNormal).mpr rfl)
  cases impossible

def evidence : Registration arena (type_of% @normalized_four_iff) where
  actual := actual
  bridge := by
    simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using @normalized_four_iff,
    rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := by
    intro _
    refine ⟨(), fourNormal, 0, ?_⟩
    have bad : (0 : Chart K 2) ≠ fourNormal := by
      intro hz
      have entry := congrFun (congrFun hz 0) 1
      change (0 : K) = 1 at entry
      exact zero_ne_one entry
    simpa [actual, realize, bad]

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@normalized_four_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.KozakiKakei.normalized_four_iff.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Polygons.KozakiKakeiFourNormal.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z => decide (Z = fourNormal)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Polygons.KozakiKakeiFourNormal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Polygons.KozakiKakeiFourNormal
