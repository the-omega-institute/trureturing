import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

/-! Source-bound audit of the restriction isomorphism for isometries fixing a subspace
pointwise. The readout is the isometry `U` read as a map of `E`, which the restricted isometry
`e U` must reproduce on every vector of `Kᗮ`. -/

namespace Reg.D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer

open _root_.D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Submodule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-! ## The real line as a model in arbitrary universes -/

/-- The real numbers lifted to universe `u`, with the shared `RCLike` structure. -/
abbrev LiftReal := ULift.{u} ℝ

/-- The real line lifted to universe `v`, an inner product space over `LiftReal`. -/
abbrev Line := ULift.{v} ℝ

/-- The vector `1` of the line, as an element of the orthogonal complement of `⊥`. -/
def oneVec : ↥(⊥ : Submodule LiftReal.{u} Line.{v})ᗮ :=
  ⟨⟨1⟩, by rw [Submodule.bot_orthogonal_eq_top]; trivial⟩

namespace Restrict

set_option linter.checkUnivs false in
/-- A linear isometry of `E` read as a map `E → E`. -/
abbrev signature : Signature where
  Params := Σ 𝕜 : Type u, Σ E : Type v, Σ _ : RCLike 𝕜, Σ _ : NormedAddCommGroup E,
    InnerProductSpace 𝕜 E
  State p := letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2; p.2.1 ≃ₗᵢ[p.1] p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1 → p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p V => letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2; ⇑V)
    (fun e => nomatch e)

/-- The reading that returns the zero map. -/
def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p _ => letI := p.2.2.2.1; (0 : p.2.1 → p.2.1)) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- Retain the complete statement of `exists_mulEquiv_orthogonal`; only the isometry `U`, read
as the map of `E` that the restricted isometry must reproduce on `Kᗮ`, is read out. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {𝕜 : Type u} {E : Type v} [i1 : RCLike 𝕜] [i2 : NormedAddCommGroup E]
    [i3 : InnerProductSpace 𝕜 E] (K : Submodule 𝕜 E) [K.HasOrthogonalProjection],
    ∃ e : pointwiseStabilizer K ≃* (Kᗮ ≃ₗᵢ[𝕜] Kᗮ),
      (∀ (U : pointwiseStabilizer K) (y : Kᗮ),
        ((e U y : Kᗮ) : E) = r.readout () ⟨𝕜, E, i1, i2, i3⟩ (U : E ≃ₗᵢ[𝕜] E) y) ∧
      (FiniteDimensional 𝕜 E → ∀ U : pointwiseStabilizer K,
        LinearMap.det ((U : E ≃ₗᵢ[𝕜] E).toLinearEquiv : E →ₗ[𝕜] E) =
          LinearMap.det ((e U).toLinearEquiv : Kᗮ →ₗ[𝕜] Kᗮ))

/-- On the line with `K = ⊥`, the identity of the stabilizer restricts to the identity, which
does not send the vector `1` to `0`. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨e, he, -⟩ := h (𝕜 := LiftReal.{u}) (E := Line.{v}) ⊥
  have h1 := he 1 oneVec
  rw [map_one] at h1
  have h2 := congrArg ULift.down h1
  simp [rejected, realize, oneVec] at h2

/-- On the line, the identity and the negation differ at the vector `1`. -/
theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  cases i
  refine ⟨⟨LiftReal.{u}, Line.{v}, inferInstance, inferInstance, inferInstance⟩,
    1, LinearIsometryEquiv.neg LiftReal.{u}, ?_⟩
  intro h
  have h1 := congrFun h (⟨1⟩ : Line.{v})
  change (⟨1⟩ : Line.{v}) = -(⟨1⟩ : Line.{v}) at h1
  have h2 := congrArg ULift.down h1
  norm_num at h2

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @exists_mulEquiv_orthogonal.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_mulEquiv_orthogonal.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Restrict

def exists_mulEquiv_orthogonal_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_mulEquiv_orthogonal.{u, v}) (Realization Restrict.signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer.exists_mulEquiv_orthogonal_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer.Restrict.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Restrict.arena.{u, v}⟩
  objectArena := .source ⟨Restrict.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Restrict.arena.{u, v} ⟨Restrict.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Restrict.signature.{u, v}
    (fun _ p V => letI := p.2.2.1; letI := p.2.2.2.1; letI := p.2.2.2.2; ⇑V) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn",
        "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Algebra.Unitary.PointwiseStabilizer
