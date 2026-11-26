import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

/-! Source-bound audit of the compactness theorem for integral operators with a continuous
kernel on compact spaces. -/

namespace Reg.D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact

open _root_.D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v w

/-! ## The real numbers as an `RCLike` field in an arbitrary universe -/

/-- The real numbers lifted to universe `w`; its `RCLike` structure is the shared one of
`Reg.Support.RealScalarLift`. -/
abbrev LiftReal := ULift.{w} ℝ

/-! ## Finite models -/

/-- The one-point space in universe `v`, with its measurable structure. -/
abbrev Pt := ULift.{v} Unit

/-- Every subset of the one-point space is measurable. -/
instance ptOpensMeasurable : OpensMeasurableSpace Pt.{v} :=
  ⟨MeasurableSpace.generateFrom_le fun _ _ => Subsingleton.measurableSet⟩

/-! ## `exists_isCompactOperator_kernel`: the integrand reads the function at a point -/
namespace Kernel

set_option linter.checkUnivs false in
/-- Evaluation at a point `y` of `Y` of a function on `Y` with values in `𝕜`. -/
abbrev signature : Signature where
  Params := Σ Y : Type v, Σ 𝕜 : Type w, Σ _ : MeasurableSpace Y, Σ _ : RCLike 𝕜, Y
  State p := p.1 → p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v, w} :=
  realize signature (fun _ p g => g p.2.2.2.2) (fun e => nomatch e)

def rejected : Realization signature.{v, w} :=
  realize signature (fun _ p _ => letI := p.2.2.2.1; 1) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- Retain the complete space, measure, exponent, kernel and conclusion telescope of
`exists_isCompactOperator_kernel`. -/
abbrev arena : Arena where
  signature := signature.{v, w}
  Law r := ∀ {X : Type u} {Y : Type v} {𝕜 : Type w} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [mY : MeasurableSpace Y] [OpensMeasurableSpace Y]
    [i𝕜 : RCLike 𝕜] (μ : Measure Y) [IsFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)]
    (K : C(X × Y, 𝕜)),
    ∃ T : Lp 𝕜 p μ →L[𝕜] C(X, 𝕜), IsCompactOperator T ∧
      ∀ (f : Lp 𝕜 p μ) (x : X),
        T f x = ∫ y, K (x, y) * r.readout () ⟨Y, 𝕜, mY, i𝕜, y⟩ f ∂μ

/-- If the integrand ignored the function, the operator would send `0` to the nonzero
integral of the constant kernel `1` against the unit point mass. -/
theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  obtain ⟨T, -, hT⟩ := h (X := Pt.{u}) (𝕜 := LiftReal.{w}) (p := 1)
    (Measure.dirac (⟨()⟩ : Pt.{v})) 1
  have h0 := hT 0 ⟨()⟩
  rw [ContinuousLinearMap.map_zero, ContinuousMap.zero_apply] at h0
  simp [rejected, realize] at h0

/-- Evaluation at the point separates the functions `0` and `1`. -/
theorem dependence : ObservationalDependence signature.{v, w} actual := by
  intro i
  cases i
  refine ⟨⟨Pt.{v}, LiftReal.{w}, inferInstance, inferInstance, ⟨()⟩⟩, 0, 1, ?_⟩
  change (0 : Pt.{v} → LiftReal.{w}) ⟨()⟩ ≠ (1 : Pt.{v} → LiftReal.{w}) ⟨()⟩
  simp

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_isCompactOperator_kernel.{u, v, w}

def source_registration :
    Registration arena.{u, v, w} sourceStatement.{u, v, w} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_isCompactOperator_kernel.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Kernel

def exists_isCompactOperator_kernel_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_isCompactOperator_kernel.{u, v, w}) (Realization Kernel.signature.{v, w})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact.exists_isCompactOperator_kernel_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact.Kernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Kernel.arena.{u, v, w}⟩
  objectArena := .source ⟨Kernel.arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Kernel.arena.{u, v, w} ⟨Kernel.source_registration.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Kernel.signature.{v, w} (fun _ p g => g p.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact
    definition := none
    coordinates := #[1, 2, 18]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg",
        "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact
