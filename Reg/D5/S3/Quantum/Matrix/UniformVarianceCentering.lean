import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.UniformVarianceCentering
import Reg.Support.DependentFamily

/-! The centered Gram norm over arbitrary finite complex Hilbert carriers. -/

namespace Reg.D5.S3.Quantum.Matrix.UniformVarianceCentering
open _root_.D5.S3.Quantum.Matrix.UniformVarianceCentering
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section
universe u v w

structure Carrier where
  space : Type v
  normed : NormedAddCommGroup space
  inner : InnerProductSpace ℂ space
  finite : FiniteDimensional ℂ space

attribute [instance] Carrier.normed Carrier.inner Carrier.finite

abbrev signature : Signature where
  Params := Carrier.{v}
  State p := p.space →ₗ[ℂ] p.space
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Observe the genuine operator norm, without restricting the carrier dimension. -/
def actual : Realization signature :=
  realize signature (fun _ _ Q => ‖Q.toContinuousLinearMap‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def referenceLift {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (n : ℕ) (L : G →ₗ[ℂ] H) :
    PiLp 2 (fun _ : Fin n => G) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H) where
  toFun x := WithLp.toLp 2 (fun r => L (x r))
  map_add' x y := by ext r; exact L.map_add (x r) (y r)
  map_smul' c x := by ext r; exact L.map_smul c (x r)

abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {H : Type u} {G : Type v}
    [hn : NormedAddCommGroup H] [hi : InnerProductSpace ℂ H]
    [hf : FiniteDimensional ℂ H]
    [gn : NormedAddCommGroup G] [gi : InnerProductSpace ℂ G]
    [gf : FiniteDimensional ℂ G] {J : Type w} [Fintype J]
    (V : G →ₗᵢ[ℂ] H) (h : J → H →ₗ[ℂ] H)
    (_hh : ∀ j, (h j).IsSymmetric) (δ : ℝ) (_hδ : 0 ≤ δ)
    (_hv : ∀ x : G, ‖x‖ = 1 →
      ∑ j, ‖h j (V x) - (inner ℂ (V x) (h j (V x))).re • V x‖^2 ≤ δ)
    (e : G) (_he : (∃ x : G, ‖x‖ = 1) → ‖e‖ = 1),
    let c : J → ℝ := fun j => (inner ℂ (V e) (h j (V e))).re
    let L : J → G →ₗ[ℂ] H := fun j => (h j).comp V.toLinearMap - (c j : ℂ) • V.toLinearMap
    let Q : G →ₗ[ℂ] G := ∑ j, (L j).adjoint.comp (L j)
    (∀ x : G, ‖x‖ = 1 →
      (∑ j, ((inner ℂ (V x) (h j (V x))).re - c j)^2 ≤ 4*δ) ∧
      (∑ j, ‖L j x‖^2 ≤ 5*δ)) ∧
    (∀ x : G, (inner ℂ x (Q x)).re = ∑ j, ‖L j x‖^2 ∧
      (inner ℂ x (Q x)).re ≤ (5*δ)*‖x‖^2) ∧
    R.readout () ⟨G,gn,gi,gf⟩ Q ≤ 5*δ ∧
    (∀ A : H →L[ℂ] H,
      ‖(∑ j, (L j).adjoint.comp (A.toLinearMap.comp (L j))).toContinuousLinearMap‖
        ≤ (5*δ)*‖A‖) ∧
    (∀ n : ℕ,
      let R : J → PiLp 2 (fun _ : Fin n => G) →ₗ[ℂ]
        PiLp 2 (fun _ : Fin n => H) := fun j => referenceLift n (L j)
      ∀ A : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H),
        ‖(∑ j, (R j).adjoint.comp (A.toLinearMap.comp (R j))).toContinuousLinearMap‖
          ≤ (5*δ)*‖A‖)

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let G := EuclideanSpace ℂ (ULift.{v} Empty)
  let H := EuclideanSpace ℂ (ULift.{u} Empty)
  let V : G →ₗᵢ[ℂ] H :=
    { toLinearMap := 0
      norm_map' := fun x => by simp [Subsingleton.elim x 0] }
  have he : (∃ x : G, ‖x‖ = 1) → ‖(0 : G)‖ = 1 := by
    rintro ⟨x,hx⟩
    simp [Subsingleton.elim x 0] at hx
  have hh := @h H G inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (ULift.{w} Empty) inferInstance
    V (fun j => nomatch j.down) (fun j => nomatch j.down) 0 (by norm_num)
    (by intro x hx; simp) 0 he
  have hbad := hh.2.2.1
  change (1 : ℝ) ≤ 5*0 at hbad
  norm_num at hbad

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  let G := EuclideanSpace ℂ (ULift.{v} (Fin 1))
  let p : Carrier.{v} := ⟨G,inferInstance,inferInstance,inferInstance⟩
  refine ⟨p, 0, LinearMap.id, ?_⟩
  change ‖(0 : G →L[ℂ] G)‖ ≠ ‖(ContinuousLinearMap.id ℂ G)‖
  simp

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
    (type_of% @hermitian_block_centering_and_gram_bound.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hermitian_block_centering_and_gram_bound, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hermitian_block_centering_and_gram_bound.{u,v,w}) (Realization signature.{v}) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.UniformVarianceCentering.hermitian_block_centering_and_gram_bound.__information_unit
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
  readout := some (realize signature.{v} (fun _ _ Q => ‖Q.toContinuousLinearMap‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.UniformVarianceCentering
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration


abbrev directSumArena : Arena where
  signature := signature.{max u v}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    {E : I → Type v} [en : ∀ i, NormedAddCommGroup (E i)]
    [ei : ∀ i, InnerProductSpace ℂ (E i)] [ef : ∀ i, FiniteDimensional ℂ (E i)]
    {J : Type w} [Fintype J]
    (h : J → PiLp 2 E →ₗ[ℂ] PiLp 2 E) (_hh : ∀ j, (h j).IsSymmetric)
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (_hv : ∀ i (x : E i), ‖x‖ = 1 →
      ∑ j, ‖h j (blockInclusion i x) -
        (inner ℂ (blockInclusion i x) (h j (blockInclusion i x))).re •
          blockInclusion i x‖^2 ≤ δ)
    (e : ∀ i, E i) (_he : ∀ i, (∃ x : E i, ‖x‖ = 1) → ‖e i‖ = 1),
    let ell := fun j => h j - centralMean h e j
    ∀ n : ℕ,
      let P := fun i => directSumReference n (blockProjection (E := E) i)
      let L := fun j => directSumReference n (ell j)
      let B := fun t : J × I × I => (P t.2.2).comp ((L t.1).comp (P t.2.1))
      (∀ x, ∑ t, ‖B t x‖^2 ≤ (5*δ)*‖x‖^2) ∧
      (∀ A : PiLp 2 (fun _ : Fin n => PiLp 2 E) →L[ℂ]
          PiLp 2 (fun _ : Fin n => PiLp 2 E),
        R.readout () ⟨PiLp 2 (fun _ : Fin n => PiLp 2 E),inferInstance,inferInstance,inferInstance⟩
          (∑ t, (B t).adjoint.comp (A.toLinearMap.comp (B t)))
          ≤ (5*δ)*‖A‖)

private theorem directSum_rejected_law : ¬ directSumArena.{u,v,w}.Law rejected := by
  intro h
  let I := ULift.{u} Empty
  let E := fun _ : I => EuclideanSpace ℂ (ULift.{v} Empty)
  have hz := @h I inferInstance inferInstance E
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (ULift.{w} Empty) inferInstance (fun j => nomatch j.down)
    (fun j => nomatch j.down) 0 (by norm_num)
    (by intro i; exact nomatch i.down) (fun i => nomatch i.down)
    (by intro i; exact nomatch i.down) 0
  have hb := hz.2 0
  change (1:ℝ) ≤ (5*0)*_ at hb
  norm_num at hb

private theorem directSum_sensitivity : Sensitivity directSumArena.{u,v,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, directSum_rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def directSum_source_registration : Registration directSumArena.{u,v,w}
    (type_of% @hermitian_direct_sum_centering.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hermitian_direct_sum_centering, rejected, directSum_rejected_law⟩
  sensitivity := directSum_sensitivity
  dependence := dependence

def directSum_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hermitian_direct_sum_centering.{u,v,w}) (Realization signature.{max u v}) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.UniformVarianceCentering.hermitian_direct_sum_centering.__information_unit
  realizationName := ``directSum_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨directSumArena.{u,v,w}⟩
  objectArena := .source ⟨directSumArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source directSumArena.{u,v,w} ⟨directSum_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{max u v}
    (fun _ _ Q => ‖Q.toContinuousLinearMap‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.UniformVarianceCentering
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev adjointArena : Arena where
  signature := signature.{v}
  Law R := ∀ {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [gn : NormedAddCommGroup G] [gi : InnerProductSpace ℂ G] [gf : FiniteDimensional ℂ G]
    {J : Type w} [Fintype J] (L : J → G →ₗ[ℂ] H) (b : ℝ) (_hb : 0 ≤ b)
    (_hv : ∀ x : G, ‖x‖ = 1 → ∑ j, ‖L j x‖^2 ≤ b) (A : H →L[ℂ] H),
    R.readout () ⟨G,gn,gi,gf⟩ (∑ j, (L j).adjoint.comp (A.toLinearMap.comp (L j)))
      ≤ b*‖A‖

private theorem adjoint_rejected_law : ¬ adjointArena.{u,v,w}.Law rejected := by
  intro h
  let G := EuclideanSpace ℂ (ULift.{v} Empty)
  let H := EuclideanSpace ℂ (ULift.{u} Empty)
  have hz := @h H G inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (ULift.{w} Empty) inferInstance
    (fun j => nomatch j.down) 0 (by norm_num) (by intro x hx; simp) 0
  change (1:ℝ) ≤ (0:ℝ)*_ at hz
  norm_num at hz

private theorem adjoint_sensitivity : Sensitivity adjointArena.{u,v,w} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, adjoint_rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def adjoint_source_registration : Registration adjointArena.{u,v,w}
    (type_of% @kraus_adjoint_norm_le.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kraus_adjoint_norm_le, rejected, adjoint_rejected_law⟩
  sensitivity := adjoint_sensitivity
  dependence := dependence

def adjoint_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kraus_adjoint_norm_le.{u,v,w}) (Realization signature.{v}) Unit Unit := {
  unitName := `D5.S3.Quantum.Matrix.UniformVarianceCentering.kraus_adjoint_norm_le.__information_unit
  realizationName := ``adjoint_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨adjointArena.{u,v,w}⟩
  objectArena := .source ⟨adjointArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source adjointArena.{u,v,w} ⟨adjoint_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v}
    (fun _ _ Q => ‖Q.toContinuousLinearMap‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.UniformVarianceCentering
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Matrix.UniformVarianceCentering
