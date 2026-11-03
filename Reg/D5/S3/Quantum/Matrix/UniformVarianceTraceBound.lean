import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.UniformVarianceTraceBound
import Reg.Support.DependentFamily

/-! Ordinary trace-norm observation over every finite complex matrix dimension. -/
namespace Reg.D5.S3.Quantum.Matrix.UniformVarianceTraceBound
open _root_.D5.S3.Quantum.Matrix.UniformVarianceTraceBound
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder
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
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
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

abbrev defectArena : Arena where
  signature := signature
  Law R := ∀ {E : Type u}
    [en : NormedAddCommGroup E] [ei : InnerProductSpace ℂ E]
    [ef : FiniteDimensional ℂ E] {J : Type w} [Fintype J]
    (h : J → E →ₗ[ℂ] E) (_hh : ∀ j, (h j).IsSymmetric)
    (_hs : ∑ j, (h j).comp (h j) = LinearMap.id)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (_hv : ∀ x : E, ‖x‖ = 1 →
      ∑ j, ‖h j x - (inner ℂ x (h j x)).re • x‖^2 ≤ δ)
    (e : E) (_he : (∃ x : E, ‖x‖ = 1) → ‖e‖ = 1),
    let c : J → ℝ := fun j => (inner ℂ e (h j e)).re
    ∀ n : ℕ,
      let vb := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => E))
      let H := fun j => LinearMap.toMatrix vb.toBasis vb.toBasis (referenceLift n (h j))
      let M := fun j => H j - (c j : ℂ) • 1
      let Q := ∑ j, (M j)ᴴ * M j
      ∀ X : Matrix (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E))))
        (Fin (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))) ℂ,
        (X - ∑ j, H j * X * (H j)ᴴ =
          (1/2 : ℂ) • (Q*X+X*Q) - ∑ j, M j * X * (M j)ᴴ) ∧
        R.readout () (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => E)))
          (X - ∑ j, H j * X * (H j)ᴴ) ≤ (10*δ)*traceNorm X

private theorem defect_rejected_law : ¬ defectArena.{u,w}.Law rejected := by
  intro h
  let E := EuclideanSpace ℂ (ULift.{u} Empty)
  have he : (∃ x : E, ‖x‖ = 1) → ‖(0 : E)‖ = 1 := by
    rintro ⟨x,hx⟩
    simp [Subsingleton.elim x 0] at hx
  have hh := @h E inferInstance inferInstance inferInstance
    (ULift.{w} Empty) inferInstance
    (fun j => nomatch j.down) (fun j => nomatch j.down)
    (Subsingleton.elim _ _) 0 (by norm_num) (by intro x hx; simp) 0 he 0 0
  have hn := hh.2
  change (1 : ℝ) ≤ (10*0)*_ at hn
  norm_num at hn

private theorem defect_sensitivity : Sensitivity defectArena.{u,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, defect_rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def defect_source_registration : Registration defectArena.{u,w}
    (type_of% @hermitian_unital_kraus_defect_trace_bound.{u,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hermitian_unital_kraus_defect_trace_bound, rejected, defect_rejected_law⟩
  sensitivity := defect_sensitivity
  dependence := dependence

def defect_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hermitian_unital_kraus_defect_trace_bound.{u,w}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.UniformVarianceTraceBound.hermitian_unital_kraus_defect_trace_bound.__information_unit
  realizationName := ``defect_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨defectArena.{u,w}⟩
  objectArena := .source ⟨defectArena.{u,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source defectArena.{u,w} ⟨defect_source_registration⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms defect_source_registration
#print axioms defect_registration

#print axioms source_registration
#print axioms registration

open _root_.D5.S3.Quantum.Matrix.UniformVarianceCentering
open scoped Matrix.Norms.L2Operator

abbrev globalArena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    {E : I → Type v} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)]
    {J : Type w} [Fintype J]
    (h : J → PiLp 2 E →ₗ[ℂ] PiLp 2 E) (_hh : ∀ j, (h j).IsSymmetric)
    (_hs : ∑ j, (h j).comp (h j) = LinearMap.id)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (_hv : ∀ i (x : E i), ‖x‖ = 1 →
      ∑ j, ‖h j (blockInclusion i x) -
        (inner ℂ (blockInclusion i x) (h j (blockInclusion i x))).re •
          blockInclusion i x‖^2 ≤ δ)
    (e : ∀ i, E i) (_he : ∀ i, (∃ x : E i, ‖x‖ = 1) → ‖e i‖ = 1),
    ∀ n : ℕ,
      let v := stdOrthonormalBasis ℂ (PiLp 2 (fun _ : Fin n => PiLp 2 E))
      let P := fun i => LinearMap.toMatrix v.toBasis v.toBasis
        (directSumReference n (blockProjection (E := E) i))
      let H := fun j => LinearMap.toMatrix v.toBasis v.toBasis (directSumReference n (h j))
      let M := fun j => LinearMap.toMatrix v.toBasis v.toBasis
        (directSumReference n (h j - centralMean h e j))
      let Q := centerPinching P (∑ j, M j * M j)
      let A := fun t : J × I × I => P t.2.2 * H t.1 * P t.2.1
      let B := fun t : J × I × I => P t.2.2 * M t.1 * P t.2.1
      Q ≤ (5*δ : ℝ) • 1 ∧
      (∑ t, (A t)ᴴ * A t = 1) ∧
      (∑ t, (B t)ᴴ * B t = Q) ∧
      (∀ Y, (centerPinching P Y).trace = Y.trace) ∧
      (∀ Y i, P i * centerPinching P Y = centerPinching P Y * P i) ∧
      (∀ X, (∀ i, P i * X = X * P i) →
        let K := centerPinching P (∑ j, M j * X * M j)
        let Phi := centerPinching P (∑ j, H j * X * H j)
        (K = ∑ t, B t * X * (B t)ᴴ) ∧
        (Phi = ∑ t, A t * X * (A t)ᴴ) ∧
        (X - Phi = (1/2 : ℂ) • (Q*X+X*Q) - K) ∧
        (R.readout () (Module.finrank ℂ (PiLp 2 (fun _ : Fin n => PiLp 2 E)))
          (X-Phi) ≤ min 2 (10*δ) * traceNorm X) ∧
        (Phi.trace = X.trace) ∧ (0 ≤ X → 0 ≤ Phi) ∧ (0 ≤ X → 0 ≤ K) ∧
        (∀ Y, (K*Y).trace = (X*(∑ t, (B t)ᴴ * Y * B t)).trace))

private theorem global_rejected_law : ¬ globalArena.{u,v,w}.Law rejected := by
  intro h
  let I := ULift.{u} Empty
  let E := fun _ : I => EuclideanSpace ℂ (ULift.{v} Empty)
  let H := PiLp 2 E
  have hz := @h I inferInstance inferInstance E
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (ULift.{w} Empty) inferInstance (fun j => nomatch j.down)
    (fun j => nomatch j.down) (Subsingleton.elim _ _) 0 (by norm_num)
    (by intro i; exact nomatch i.down) (fun i => nomatch i.down)
    (by intro i; exact nomatch i.down) 0
  have hb := (hz.2.2.2.2.2 0 (by intro i; exact nomatch i.down)).2.2.2.1
  change (1:ℝ) ≤ min 2 (10*0) * _ at hb
  norm_num at hb

private theorem global_sensitivity : Sensitivity globalArena.{u,v,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, global_rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def global_source_registration : Registration globalArena.{u,v,w}
    (type_of% @hermitian_unital_direct_sum_defect_trace_bound.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hermitian_unital_direct_sum_defect_trace_bound, rejected, global_rejected_law⟩
  sensitivity := global_sensitivity
  dependence := dependence

def global_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hermitian_unital_direct_sum_defect_trace_bound.{u,v,w})
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.UniformVarianceTraceBound.hermitian_unital_direct_sum_defect_trace_bound.__information_unit
  realizationName := ``global_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨globalArena.{u,v,w}⟩
  objectArena := .source ⟨globalArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source globalArena.{u,v,w} ⟨global_source_registration⟩
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Matrix.UniformVarianceTraceBound
