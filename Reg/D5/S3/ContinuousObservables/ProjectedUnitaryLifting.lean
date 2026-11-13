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

abbrev signature : Signature where
  Params := List ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature (fun _ phases x => seqR phases x) (fun a => nomatch a)
def rejected := realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def liftingLaw (r : Realization signature) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (E : ProjUnitaryEncoding H) (Ψ : List ℝ) (R : ℂ[X]),
    (∀ x ∈ Set.Icc (0 : ℝ) 1, r.readout () Ψ x 0 0 =
      if Even Ψ.length then R.eval ((x : ℂ) ^ 2) else (x : ℂ) * R.eval ((x : ℂ) ^ 2)) →
    (Even Ψ.length → E.P * altSeq E Ψ * E.P =
      E.P * aeval (LinearMap.adjoint E.encoded * E.encoded) R * E.P) ∧
    (Odd Ψ.length → E.P' * altSeq E Ψ * E.P =
      E.encoded * aeval (LinearMap.adjoint E.encoded * E.encoded) R)

abbrev liftingArena.{u} : Arena where
  signature := signature
  Law := liftingLaw.{u}

abbrev singularSignature : Signature where
  Params := List ℝ
  State _ := ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def singularActualReadout := realize singularSignature
  (fun _ phases x => seqR phases x) (fun a => nomatch a)
def singularBad (i : Fin 2) := realize singularSignature
  (fun j phases x => if j = i then 0 else seqR phases x) (fun a => nomatch a)

def singularLaw (r : Realization singularSignature) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {E : ProjUnitaryEncoding H} {ψ : H} {σ : ℝ},
    IsSingularPair E ψ σ → ∀ Φ : List ℝ,
    altSeq E Φ ψ =
      r.readout 0 Φ σ 0 0 • (if Even Φ.length then ψ else lvOf E ψ σ) +
      r.readout 1 Φ σ 1 0 • (if Even Φ.length then rvpOf E ψ σ else lvtOf E ψ σ)

abbrev singularArena.{u} : Arena where
  signature := singularSignature
  Law := singularLaw.{u}

theorem actualDependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[0], 0, 1, ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simpa [actual, realize, seqR, phaseZ, Rref] using hc

theorem liftingActual : liftingArena.{u}.Law actual := by
  intro H _ _ _ E Ψ R hs
  exact polynomial_lifting E Ψ R hs

theorem liftingRejected : ¬ liftingArena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let E : ProjUnitaryEncoding K :=
    ofRaw (1 : K →ₗ[ℂ] K) 1 1 (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one]) (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one]) (IsStarProjection.one _) (IsStarProjection.one _)
  have hs : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      rejected.readout () [] x 0 0 = if Even ([] : List ℝ).length then
        (0 : ℂ[X]).eval ((x : ℂ) ^ 2) else (x : ℂ) * (0 : ℂ[X]).eval ((x : ℂ) ^ 2) := by
    change ∀ x ∈ Set.Icc (0 : ℝ) 1, (0 : ℂ) = _
    simp
  have he := (h E [] 0 hs).1 (by simp)
  have hv := LinearMap.congr_fun he (EuclideanSpace.single ⟨()⟩ 1)
  have hcoord := congrArg (fun v : K => v ⟨()⟩) hv
  simpa [E, ofRaw, altSeq] using hcoord

theorem singularActual : singularArena.{u}.Law singularActualReadout := by
  intro H _ _ _ E ψ σ h Φ
  exact altSeq_apply_singular h Φ

theorem singularRejected (i : Fin 2) : ¬ singularArena.{u}.Law (singularBad i) := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  let v : K := EuclideanSpace.single ⟨()⟩ 1
  fin_cases i
  · let E := ofRaw (1 : K →ₗ[ℂ] K) 1 1
      (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one])
      (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one])
      (IsStarProjection.one _) (IsStarProjection.one _)
    have hp : IsSingularPair E v 1 := by
      constructor <;> simp [E, ofRaw, ProjUnitaryEncoding.encoded]
    have hv := h hp []
    have hc := congrArg (fun w : K => w ⟨()⟩) hv
    simpa [singularBad, realize, seqR, altSeq, v] using hc
  · let E := ofRaw (1 : K →ₗ[ℂ] K) 1 0
      (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one])
      (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one])
      (IsStarProjection.one _) (IsStarProjection.zero _)
    have hp : IsSingularPair E v 0 := by
      constructor <;> simp [E, ofRaw, ProjUnitaryEncoding.encoded]
    have hv := h hp [0]
    have hc := congrArg (fun w : K => w ⟨()⟩) hv
    simpa [singularBad, realize, seqR, altSeq, phaseZ, Rref, phaseOp, E, ofRaw, v] using hc

theorem singularDependence : ObservationalDependence singularSignature singularActualReadout := by
  intro i
  refine ⟨[0], 0, 1, ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simpa [singularActualReadout, realize, seqR, phaseZ, Rref] using hc

def liftingFamily : Registration liftingArena.{u} (type_of% (@polynomial_lifting.{u})) where
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

def singularFamily : Registration singularArena.{u} (type_of% (@altSeq_apply_singular.{u})) where
  actual := singularActualReadout
  bridge := Iff.rfl
  variation := ⟨singularActual, singularBad 0, singularRejected 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨singularBad i, ?_, rfl, singularRejected i⟩
      intro j hj
      funext phases x
      simp [singularActualReadout, singularBad, realize, hj]
    · intro a; exact nomatch a
  dependence := singularDependence

def liftingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@polynomial_lifting.{u}) (type_of% (realize signature (fun _ phases x => seqR phases x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.liftingUnit
  realizationName := `Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.liftingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨liftingArena.{u}⟩
  objectArena := .source ⟨liftingArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftingArena.{u} ⟨liftingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ phases x => seqR phases x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ContinuousObservables.ProjectedUnitaryLifting
    definition := none
    coordinates := #[5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "fn", "arg", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def singularRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@altSeq_apply_singular.{u}) (type_of% (realize singularSignature (fun _ phases x => seqR phases x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.singularUnit
  realizationName := `Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting.singularFamily
  realizationSource := none
  generated := false
  arena := .source ⟨singularArena.{u}⟩
  objectArena := .source ⟨singularArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source singularArena.{u} ⟨singularFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize singularSignature (fun _ phases x => seqR phases x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ContinuousObservables.ProjectedUnitaryLifting
    definition := none
    coordinates := #[8]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ContinuousObservables.ProjectedUnitaryLifting
