import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.Quantum.Divergence.PositiveKrausCompression
import D5.S3.Quantum.Divergence.UniversalPositiveScalarizer

/-! The weighted center and the simultaneous residual-Gram bounds. -/

noncomputable section
universe u
open Set Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer

namespace CommonState

structure Parameters where
  b : Type u
  R : Type u
  fb : Fintype b
  db : DecidableEq b
  fr : Fintype R
  dr : DecidableEq R
  sigma : @DensityState b fb db

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Matrix (p.R × p.b) (p.R × p.b) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.R p.R ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p Y => by
    letI := p.fb
    letI := p.db
    letI := p.fr
    letI := p.dr
    exact stateCenter p.sigma Y) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p Y => by
    letI := p.fb
    letI := p.db
    letI := p.fr
    letI := p.dr
    exact stateCenter p.sigma Y + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law Q := ∀ {a b : Type u} [fa : Fintype a] [da : DecidableEq a] [na : Nonempty a]
    [fb : Fintype b] [db : DecidableEq b] [nb : Nonempty b]
    (channel : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k)
    (hUniversal : UniversalPositiveTraceTest channel k),
    ∃ sigma : DensityState b,
      ∀ {R : Type u} [fr : Fintype R] [dr : DecidableEq R]
        (Y : Matrix (R × b) (R × b) ℂ),
        let X := Q.readout () ⟨b,R,fb,db,fr,dr,sigma⟩ Y;
        let Δ := PhiR channel Y - Matrix.kronecker X (1 : Matrix a a ℂ);
        X = _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
          (Matrix.kronecker (1 : Matrix R R ℂ)
            (CStarMatrix.ofMatrix.symm sigma.1 : Matrix b b ℂ) * Y) ∧
        (((k : ℂ) • (PhiR channel (Y * Yᴴ) - PhiR channel Y * (PhiR channel Y)ᴴ)) -
          Δ * Δᴴ).PosSemidef ∧
        (((k : ℂ) • (PhiR channel (Yᴴ * Y) - (PhiR channel Y)ᴴ * PhiR channel Y)) -
          Δᴴ * Δ).PosSemidef

theorem source_equivalence :
    (type_of% @common_positive_state_scalarizer.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨sigma,hs⟩ := h singletonChannel 0 (by norm_num) singleton_test
  have he := (hs (R := ULift.{u} Unit) 0).1
  have hd := congrArg (fun M : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    M ⟨()⟩ ⟨()⟩) he
  simp [rejected, realize, stateCenter,
    _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.trace, Matrix.mul_apply] at hd
  change (1 : ℂ) = 0 at hd
  exact one_ne_zero hd

private def singletonState : DensityState (ULift.{u} Unit) := by
  refine ⟨CStarMatrix.ofMatrix (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv Matrix.PosSemidef.one.nonneg
  · change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
    simp [Matrix.trace]

private def singletonParameters : Parameters.{u} :=
  ⟨ULift.{u} Unit, ULift.{u} Unit, inferInstance, inferInstance,
    inferInstance, inferInstance, singletonState⟩

set_option maxHeartbeats 2000000 in
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨singletonParameters, (0 : Matrix
    (ULift.{u} Unit × ULift.{u} Unit) (ULift.{u} Unit × ULift.{u} Unit) ℂ),
    (1 : Matrix (ULift.{u} Unit × ULift.{u} Unit)
      (ULift.{u} Unit × ULift.{u} Unit) ℂ), ?_⟩
  intro he
  dsimp only [actual, realize, singletonParameters] at he
  have hd := congrArg (fun M : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ =>
    M ⟨()⟩ ⟨()⟩) he
  change (stateCenter singletonState (0 : Matrix
      (ULift.{u} Unit × ULift.{u} Unit) (ULift.{u} Unit × ULift.{u} Unit) ℂ)) ⟨()⟩ ⟨()⟩ =
    (stateCenter singletonState (1 : Matrix
      (ULift.{u} Unit × ULift.{u} Unit) (ULift.{u} Unit × ULift.{u} Unit) ℂ)) ⟨()⟩ ⟨()⟩ at hd
  simp [stateCenter, singletonState, CStarMatrix.ofMatrix,
    Matrix.trace, Matrix.mul_apply, Matrix.one_apply] at hd
  change (0 : ℂ) = (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) default default at hd
  simpa using hd

def family : Registration arena.{u} (type_of% @common_positive_state_scalarizer.{u}) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@common_positive_state_scalarizer.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_positive_state_scalarizer.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UniversalPositiveScalarizer.common_positive_state_scalarizer.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer.CommonState.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p Y => by
    letI := p.fb
    letI := p.db
    letI := p.fr
    letI := p.dr
    exact stateCenter p.sigma Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
    definition := none
    coordinates := #[1,12,13]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "value"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_equivalence
#print axioms family
#print axioms audit

end CommonState

end Reg.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
