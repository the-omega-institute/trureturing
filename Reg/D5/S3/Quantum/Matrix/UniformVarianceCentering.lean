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
    LeanInformationAudit.Contract.Registration
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
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.UniformVarianceCentering
