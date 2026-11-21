import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization

namespace Reg.D5.S3.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization

open LeanInformationAudit
open _root_.D5.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false

structure FiniteGroupState where
  carrier : Type
  group : Group carrier
  finite : Finite carrier

abbrev signature : Signature where
  Params := ℚ
  State _ := FiniteGroupState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ G => @ndeg G.carrier G.group G.finite) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ x : ℚ, 0 < x → x ≤ 1 →
    ∃ (G : Type) (group : Group G) (finite : Finite G),
      R.readout () x ⟨G, group, finite⟩ = x

theorem source_bridge : claim ↔ arena.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, hzero⟩ := h 1 (by norm_num) (by norm_num)
  change (0 : ℚ) = 1 at hzero
  exact zero_ne_one hzero

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨G, groupG, finiteG, hG⟩ := result 1 (by norm_num) (by norm_num)
  obtain ⟨H, groupH, finiteH, hH⟩ := result (1 / 2) (by norm_num) (by norm_num)
  refine ⟨1, ⟨G, groupG, finiteG⟩, ⟨H, groupH, finiteH⟩, ?_⟩
  change @ndeg G groupG finiteG ≠ @ndeg H groupH finiteH
  rw [hG, hH]
  norm_num

noncomputable def familyRegistration : Registration arena claim where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (Realization signature) Type Unit where
  unitName := `D5.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization.result.__information_unit
  realizationName :=
    `Reg.D5.S3.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature
    (fun _ _ G => @ndeg G.carrier G.group G.finite) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization
    definition := some {
      owner := `D5.S3.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization
      name := `D5.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization.claim }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 3 }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization
