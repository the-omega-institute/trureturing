import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ContinuousObservables.ProjectedUnitaryLifting

/-! Source-domain registrations for projected-unitary operator laws. -/

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Encoding
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar
open Polynomial

noncomputable section
universe u
namespace Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting

structure Parameters where
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [finite : FiniteDimensional ℂ H]
  encoding : ProjUnitaryEncoding H

attribute [instance] Parameters.normed Parameters.inner Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := List ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H →ₗ[ℂ] p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ p phases => altSeq p.encoding phases)
  (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => 0) (fun a => nomatch a)

def liftingLaw (r : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (E : ProjUnitaryEncoding H) (Ψ : List ℝ) (R : ℂ[X]),
    (∀ x ∈ Set.Icc (0 : ℝ) 1, seqR Ψ x 0 0 =
      if Even Ψ.length then R.eval ((x : ℂ) ^ 2) else (x : ℂ) * R.eval ((x : ℂ) ^ 2)) →
    (Even Ψ.length → E.P * r.readout () ⟨H, E⟩ Ψ * E.P =
      E.P * aeval (LinearMap.adjoint E.encoded * E.encoded) R * E.P) ∧
    (Odd Ψ.length → E.P' * r.readout () ⟨H, E⟩ Ψ * E.P =
      E.encoded * aeval (LinearMap.adjoint E.encoded * E.encoded) R)

abbrev liftingArena : Arena where
  signature := signature.{u}
  Law := liftingLaw

def singularLaw (r : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {E : ProjUnitaryEncoding H} {ψ : H} {σ : ℝ},
    IsSingularPair E ψ σ → ∀ Φ : List ℝ,
    r.readout () ⟨H, E⟩ Φ ψ =
      seqR Φ σ 0 0 • (if Even Φ.length then ψ else lvOf E ψ σ) +
      seqR Φ σ 1 0 • (if Even Φ.length then rvpOf E ψ σ else lvtOf E ψ σ)

abbrev singularArena : Arena where
  signature := signature.{u}
  Law := singularLaw

def oneEncoding : ProjUnitaryEncoding ℂ :=
  ofRaw 1 1 1 (by simp) (by simp) (IsStarProjection.one _) (IsStarProjection.one _)
def negativeEncoding : ProjUnitaryEncoding ℂ :=
  ofRaw (-1) 1 1 (by simp only [star_neg, star_one, neg_mul_neg, one_mul]) (by simp only [star_neg, star_one, neg_mul_neg, one_mul]) (IsStarProjection.one _) (IsStarProjection.one _)

theorem actualDependence : ObservationalDependence signature.{u} actual := by
  intro i
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let E : ProjUnitaryEncoding K :=
    ofRaw (-1) 1 1 (by simp only [star_neg, star_one, neg_mul_neg, one_mul]) (by simp only [star_neg, star_one, neg_mul_neg, one_mul]) (IsStarProjection.one _) (IsStarProjection.one _)
  refine ⟨⟨K, E⟩, [], [0], ?_⟩
  intro h
  have hv := LinearMap.congr_fun h (EuclideanSpace.single ⟨()⟩ 1)
  have hcoord := congrArg (fun v : K => v ⟨()⟩) hv
  simpa [actual, realize, E, ofRaw, altSeq, phaseOp] using hcoord

theorem liftingActual : liftingArena.{u}.Law actual := by
  intro H _ _ _ E Ψ R hs
  exact polynomial_lifting E Ψ R hs

theorem liftingRejected : ¬ liftingArena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let E : ProjUnitaryEncoding K :=
    ofRaw 1 1 1 (by simp) (by simp) (IsStarProjection.one _) (IsStarProjection.one _)
  have hs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      seqR [] x 0 0 = if Even ([] : List ℝ).length then (1 : ℂ[X]).eval ((x : ℂ) ^ 2)
        else (x : ℂ) * (1 : ℂ[X]).eval ((x : ℂ) ^ 2) := by simp [seqR]
  have he := (h E [] 1 hs).1 (by simp)
  have hv := LinearMap.congr_fun he (EuclideanSpace.single ⟨()⟩ 1)
  have hcoord := congrArg (fun v : K => v ⟨()⟩) hv
  simpa [rejected, realize, E, ofRaw] using hcoord

theorem singularActual : singularArena.{u}.Law actual := by
  intro H _ _ _ E ψ σ h Φ
  exact altSeq_apply_singular h Φ

theorem singularRejected : ¬ singularArena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let E : ProjUnitaryEncoding K :=
    ofRaw 1 1 1 (by simp) (by simp) (IsStarProjection.one _) (IsStarProjection.one _)
  let v : K := EuclideanSpace.single ⟨()⟩ 1
  have hp : IsSingularPair E v 1 := by
    constructor <;> simp [E, ofRaw, ProjUnitaryEncoding.encoded]
  have hv := h hp []
  have hcoord := congrArg (fun v : K => v ⟨()⟩) hv
  simpa [rejected, realize, seqR, v] using hcoord

def liftingFamily : Registration liftingArena (type_of% (@polynomial_lifting.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨liftingActual, rejected, liftingRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, liftingRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a; exact nomatch a
  dependence := actualDependence

def singularFamily : Registration singularArena (type_of% (@altSeq_apply_singular.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨singularActual, rejected, singularRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, singularRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a; exact nomatch a
  dependence := actualDependence

end Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting
