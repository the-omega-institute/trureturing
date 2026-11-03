import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.UniformVarianceTraceBound
import Reg.Support.DependentFamily

/-! Ordinary trace-norm observation over every finite complex matrix dimension. -/
namespace Reg.D5.S3.Quantum.Matrix.UniformVarianceTraceBound
open _root_.D5.S3.Quantum.Matrix.UniformVarianceTraceBound
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators MatrixOrder
noncomputable section
universe u v w

abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => traceNorm X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def referenceLift {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (n : ℕ) (L : E →ₗ[ℂ] F) :
    PiLp 2 (fun _ : Fin n => E) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => F) where
  toFun x := WithLp.toLp 2 (fun r => L (x r))
  map_add' x y := by ext r; exact L.map_add (x r) (y r)
  map_smul' c x := by ext r; exact L.map_smul c (x r)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} {F : Type v}
    [en : NormedAddCommGroup E] [ei : InnerProductSpace ℂ E]
    [ef : FiniteDimensional ℂ E]
    [fn : NormedAddCommGroup F] [fi : InnerProductSpace ℂ F]
    [ff : FiniteDimensional ℂ F] {J : Type w} [Fintype J]
    (V : E →ₗᵢ[ℂ] F) (h : J → F →ₗ[ℂ] F)
    (_hh : ∀ j, (h j).IsSymmetric) (δ : ℝ) (_hδ : 0 ≤ δ)
    (_hv : ∀ x : E, ‖x‖ = 1 →
      ∑ j, ‖h j (V x) - (inner ℂ (V x) (h j (V x))).re • V x‖^2 ≤ δ)
    (e : E) (_he : (∃ x : E, ‖x‖ = 1) → ‖e‖ = 1),
    let c : J → ℝ := fun j => (inner ℂ (V e) (h j (V e))).re
    let L : J → E →ₗ[ℂ] F := fun j => (h j).comp V.toLinearMap - (c j : ℂ) • V.toLinearMap
    ∀ n : ℕ,
      let vb := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => E))
      let wb := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => F))
      let M := fun j => LinearMap.toMatrix vb.toBasis wb.toBasis (referenceLift n (L j))
      ∀ X : Matrix (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E))))
        (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))) ℂ, R.readout () (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => F)))
        (∑ j, M j * X * (M j)ᴴ) ≤ (5*δ)*traceNorm X

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Empty)
  let F := EuclideanSpace ℂ (ULift.{v} Empty)
  let V : E →ₗᵢ[ℂ] F :=
    { toLinearMap := 0
      norm_map' := fun x => by simp [Subsingleton.elim x 0] }
  have he : (∃ x : E, ‖x‖ = 1) → ‖(0 : E)‖ = 1 := by
    rintro ⟨x,hx⟩
    simp [Subsingleton.elim x 0] at hx
  have hh := @h E F inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (ULift.{w} Empty) inferInstance
    V (fun j => nomatch j.down) (fun j => nomatch j.down) 0 (by norm_num)
    (by intro x hx; simp) 0 he 0 0
  change (1 : ℝ) ≤ (5*0)*_ at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change traceNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) ≠ traceNorm (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have h0 := traceNorm_of_posSemidef (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef)
  have h1 := traceNorm_of_posSemidef (Matrix.PosSemidef.one :
    (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef)
  have h0' := congrArg Complex.re h0
  have h1' := congrArg Complex.re h1
  norm_num at h0' h1'
  rw [h0',h1']
  norm_num

private theorem sensitivity : Sensitivity arena.{u,v,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def source_registration : Registration arena.{u,v,w}
    (type_of% @hermitian_centered_kraus_trace_bound.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hermitian_centered_kraus_trace_bound, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration
      (@hermitian_centered_kraus_trace_bound.{u,v,w}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.UniformVarianceTraceBound.hermitian_centered_kraus_trace_bound.__information_unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => traceNorm X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.UniformVarianceTraceBound
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.Matrix.UniformVarianceTraceBound
