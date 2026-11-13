import D5.S3.Quantum.Foundation.OriginalNormalRestriction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The readout is actual restriction on every member of the full original
normal span.  This is partial source-audit evidence, not a completed four-slot
registration.  No model witness, intervention or dependence field is postulated. -/

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Foundation.OriginalNormalRestriction

open Set
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.ExclusionBallFaces
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.OriginalNormalRestriction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  p : pure cone unit
  chart : ExclusionChart cone unit p

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev normals (P : Inputs.{v}) : Set (P.V →L[ℝ] ℝ) :=
  {f | (∀ x ∈ P.cone, 0 ≤ f x) ∧ f P.p = 0}
abbrev normalSpan (P : Inputs.{v}) := Submodule.span ℝ (normals P)
abbrev chartSpace (P : Inputs.{v}) := EuclideanSpace ℝ (Fin P.chart.dim)

def restriction (P : Inputs.{v}) : normalSpan P →ₗ[ℝ] (chartSpace P →ᵃ[ℝ] ℝ) where
  toFun f := f.val.toLinearMap.toAffineMap.comp P.chart.param
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := normalSpan P
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := chartSpace P →ᵃ[ℝ] ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P f => restriction P f) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    (∀ q : pure P.cone P.unit, ∃ b : ExclusionChart P.cone P.unit q, b.dim = 3) →
    (∀ q r : pure P.cone P.unit,
      exclusion P.cone P.unit q = exclusion P.cone P.unit r → q = r) →
    P.chart.dim = 3 →
    let N := normals P
    let L := normalSpan P
    let R := O.readout () P
    Function.Surjective R ∧ 4 ≤ Module.finrank ℝ L ∧
    {f | f ∈ N ∧ ∀ z ∈ Metric.closedBall (0 : chartSpace P) 1,
      f (P.chart.param z) = 1} =
      {f | ∃ e : P.V →ₗ[ℝ] ℝ, common P.cone P.unit P.p e ∧
        f = (P.unit - e).toContinuousLinearMap} ∧
    (∃ f : L, f ∈ interior (L.subtype ⁻¹' N) ∧
      f.val ∈ intrinsicInterior ℝ N ∧ R f = AffineMap.const ℝ _ 1) ∧
    (∀ ep : P.V →ₗ[ℝ] ℝ, (∀ e, common P.cone P.unit P.p e ↔ e = ep) →
      ∃ (g : L) (e : L ≃ₗ[ℝ] (chartSpace P →ᵃ[ℝ] ℝ)),
        g.val = (P.unit - ep).toContinuousLinearMap ∧
        g ∈ interior (L.subtype ⁻¹' N) ∧ g.val ∈ intrinsicInterior ℝ N ∧
        (e : L → (chartSpace P →ᵃ[ℝ] ℝ)) = R ∧
        Function.Bijective R ∧ Module.finrank ℝ L = 4)

abbrev sourceScope : Prop := type_of% (@original_normal_restriction.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg hEB3 hInj ha
    have hh := @h P.V P.add P.space P.finite P.cone P.unit
      hc hs hg hEB3 hInj P.p P.chart ha
    rcases hh with ⟨ho, hd, hf, hri, hu⟩
    refine ⟨ho, hd, hf, hri, ?_⟩
    intro ep hep
    obtain ⟨g, e, he, hi, hr, hmap, hb, hd⟩ := hu ep hep
    exact ⟨g, e, he, hi, hr, congrArg DFunLike.coe hmap, hb, hd⟩
  · intro h V add space finite C unit hc hs hg hEB3 hInj p a ha
    have hh := h (@Inputs.mk V add space finite C unit p a) hc hs hg hEB3 hInj ha
    rcases hh with ⟨ho, hd, hf, hri, hu⟩
    refine ⟨ho, hd, hf, hri, ?_⟩
    intro ep hep
    obtain ⟨g, e, he, hi, hr, hmap, hb, hd⟩ := hu ep hep
    exact ⟨g, e, he, hi, hr, LinearMap.ext (congrFun hmap), hb, hd⟩

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@original_normal_restriction.{v})

/-- All original assumptions of one actual model; no such model is constructed here. -/
structure ModelWitness where
  inputs : Inputs.{v}
  closed : IsClosed (inputs.cone : Set inputs.V)
  strict : ∀ x ∈ inputs.cone, x ≠ 0 → 0 < inputs.unit x
  generating : Submodule.span ℝ (inputs.cone : Set inputs.V) = ⊤
  balls : ∀ q : pure inputs.cone inputs.unit,
    ∃ b : ExclusionChart inputs.cone inputs.unit q, b.dim = 3
  inj : ∀ q r : pure inputs.cone inputs.unit,
    exclusion inputs.cone inputs.unit q = exclusion inputs.cone inputs.unit r → q = r
  dim : inputs.chart.dim = 3

def erased : Realization signature.{v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem erased_negative (w : ModelWitness.{v}) : ¬ arena.{v}.Law erased.{v} := by
  intro h
  have ho := (h w.inputs w.closed w.strict w.generating w.balls w.inj w.dim).1
  obtain ⟨f, hf⟩ := ho (AffineMap.const ℝ (chartSpace w.inputs) 1)
  have hh := congrArg (fun q : chartSpace w.inputs →ᵃ[ℝ] ℝ => q 0) hf
  norm_num [erased, realize] at hh

private theorem dependence (w : ModelWitness.{v}) :
    ObservationalDependence signature.{v} actual.{v} := by
  intro i
  cases i
  have ho := (actual_positive w.inputs w.closed w.strict w.generating
    w.balls w.inj w.dim).1
  obtain ⟨f, hf⟩ := ho (AffineMap.const ℝ (chartSpace w.inputs) 1)
  refine ⟨w.inputs, 0, f, ?_⟩
  change restriction w.inputs 0 ≠ restriction w.inputs f
  change restriction w.inputs f = AffineMap.const ℝ (chartSpace w.inputs) 1 at hf
  rw [map_zero, hf]
  intro he
  have hh := congrArg (fun q : chartSpace w.inputs →ᵃ[ℝ] ℝ => q 0) he
  norm_num at hh

/-- A conditional mathematical four-slot family. A closed model witness and
the exact native source-occurrence binding remain separate admission obligations. -/
def family (w : ModelWitness.{v}) : Registration arena.{v} sourceScope.{v} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, erased, erased_negative w⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_negative w⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence w

def audit (w : ModelWitness.{v}) : LeanInformationAudit.Contract.Registration
    (@original_normal_restriction.{v}) (Realization signature.{v}) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.OriginalNormalRestriction.original_normal_restriction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.OriginalNormalRestriction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{v} ⟨family w⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ P f => restriction P f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms source_bridge
#print axioms actual_positive
#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Foundation.OriginalNormalRestriction
