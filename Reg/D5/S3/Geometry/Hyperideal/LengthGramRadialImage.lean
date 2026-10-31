import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.LengthGramRadialImage
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.LengthGramBody

namespace Reg.D5.S3.Geometry.Hyperideal.LengthGramRadialImage
open _root_.D5.S3.Geometry.Hyperideal.LengthGramRadialImage

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 6 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set V × (Fin 6 → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ l => (halfspaceSlice l, l)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (∅, fun _ => 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (l : Fin 6 → ℝ), (∀ k, 0 < l k) →
    radial l '' cutBody l = (r.readout () () l).1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let l : Fin 6 → ℝ := fun _ => 1
  have hl : ∀ k, 0 < l k := by intro k; norm_num [l]
  obtain ⟨_, _, _, _, _, _, _, himage, _, _⟩ := shared_radial_body l hl
  obtain ⟨y, hy⟩ := himage
  rw [h l hl] at hy
  exact hy

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (fun _ => (1 : ℝ)), (fun _ => (2 : ℝ)), ?_⟩
  intro heq
  have hsecond := congrArg Prod.snd heq
  have hentry := congrFun hsecond 0
  norm_num [actual, realize] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := by rfl
  variation := ⟨radial_image_halfspace_slice, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.LengthGramRadialImage.radial_image_halfspace_slice)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ l => (halfspaceSlice l, l)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `D5.S3.Geometry.Hyperideal.LengthGramRadialImage.radial_image_halfspace_slice.image_unit,
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.LengthGramRadialImage.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ l => (halfspaceSlice l, l)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperideal.LengthGramRadialImage,
    definition := none,
    coordinates := #[],
    readouts := #[]
  },
  continuation := .unknown,
  familyRecord := none,
  options := #[]
}

end Reg.D5.S3.Geometry.Hyperideal.LengthGramRadialImage
