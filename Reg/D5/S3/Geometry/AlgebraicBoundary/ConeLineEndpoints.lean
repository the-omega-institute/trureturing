import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints

/-! Scalar parameter observations on actual cone-directed lines. -/

noncomputable section
open Set
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints

namespace Reg.D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints
universe u

structure Parameters where
  E : Type u
  group : NormedAddCommGroup E
  space : @NormedSpace ℝ E _ group.toSeminormedAddCommGroup
  e : E
  x : E

attribute [instance] Parameters.group Parameters.space

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ConvexCone ℝ E) (_hclosed : IsClosed (C : Set E)) (_hs : C.Salient)
    {e x : E} (_he : e ∈ interior (C : Set E)) (_hx : ∀ s : ℝ, x ≠ s • e),
    ∃ a b : ℝ, a < b ∧
      {t : ℝ | -(t • e - x) ∈ C} = Iic a ∧
      {t : ℝ | R.readout () () t • e - x ∈ C} = Ici b ∧
      -(a • e - x) ∈ frontier (C : Set E) ∧
      b • e - x ∈ frontier (C : Set E)

private theorem bridge : (type_of% (@off_axis_closed_rays.{u})) ↔
    arena.{u}.Law actual := Iff.rfl

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} (ℝ × ℝ), inferInstance, inferInstance, ⟨1, 1⟩, ⟨1, 0⟩⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let C : ConvexCone ℝ (ULift.{u} (ℝ × ℝ)) := {
    carrier := {z | 0 ≤ z.down.1 ∧ 0 ≤ z.down.2}
    smul_mem' := by
      intro c hc z hz
      exact ⟨mul_nonneg hc.le hz.1, mul_nonneg hc.le hz.2⟩
    add_mem' := by
      intro z hz w hw
      exact ⟨add_nonneg hz.1 hw.1, add_nonneg hz.2 hw.2⟩ }
  have hc : IsClosed (C : Set (ULift.{u} (ℝ × ℝ))) :=
    (isClosed_le continuous_const (continuous_fst.comp continuous_uliftDown)).inter
      (isClosed_le continuous_const (continuous_snd.comp continuous_uliftDown))
  have hsal : C.Salient := by
    intro z hz hz0 hn
    apply hz0
    apply ULift.down_injective
    apply Prod.ext
    · exact le_antisymm (neg_nonneg.mp hn.1) hz.1
    · exact le_antisymm (neg_nonneg.mp hn.2) hz.2
  have he : testParameters.e ∈ interior (C : Set testParameters.E) := by
    let U : Set (ULift.{u} (ℝ × ℝ)) := {x | 0 < x.down.1 ∧ 0 < x.down.2}
    have ho : IsOpen U :=
      (isOpen_lt continuous_const (continuous_fst.comp continuous_uliftDown)).inter
        (isOpen_lt continuous_const (continuous_snd.comp continuous_uliftDown))
    apply (interior_mono (show U ⊆ (C : Set testParameters.E) from ?_))
      (show testParameters.e ∈ interior U from
        ho.interior_eq.symm ▸ (by norm_num [U, testParameters]))
    intro z hz
    change (0 : ℝ) ≤ z.down.1 ∧ (0 : ℝ) ≤ z.down.2
    exact ⟨hz.1.le, hz.2.le⟩
  have hx : ∀ s : ℝ, testParameters.x ≠ s • testParameters.e := by
    intro s hs
    have h1 := congrArg (fun z : ULift.{u} (ℝ × ℝ) => z.down.1) hs
    have h2 := congrArg (fun z : ULift.{u} (ℝ × ℝ) => z.down.2) hs
    change (1 : ℝ) = s * 1 at h1
    change (0 : ℝ) = s * 1 at h2
    linarith
  obtain ⟨a, b, _, _, hpos, _, _⟩ := @h testParameters.E testParameters.group
    testParameters.space C hc hsal testParameters.e testParameters.x he hx
  have hm : b ∈ Ici b := by
    change b ≤ b
    exact le_rfl
  rw [← hpos] at hm
  change (0 : ℝ) ≤ 0 * 1 - 1 ∧ (0 : ℝ) ≤ 0 * 1 - 0 at hm
  norm_num at hm

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, zero_ne_one⟩

def family : Registration arena.{u} (type_of% (@off_axis_closed_rays.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@off_axis_closed_rays.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@off_axis_closed_rays.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints.__information_unit
  realizationName := `Reg.D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg", "arg", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Geometry.AlgebraicBoundary.ConeLineEndpoints
