import D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit ContinuousLinearMap MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
universe u v
namespace Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
structure Parameters where
  V : Type u
  W : Type v
  [normedV : NormedAddCommGroup V]
  [innerV : InnerProductSpace ℝ V]
  [finiteV : FiniteDimensional ℝ V]
  [normedW : NormedAddCommGroup W]
  [innerW : InnerProductSpace ℝ W]
  [completeW : CompleteSpace W]
  B : V →L[ℝ] V
  C : V →L[ℝ] W
  beta : ℝ
  eta : ℝ
attribute [instance] Parameters.normedV Parameters.innerV Parameters.finiteV
  Parameters.normedW Parameters.innerW Parameters.completeW
abbrev signature : Signature where
  Params := Parameters.{u,v}
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : ∀ (_ : Empty) p, signature.{u,v}.State p := fun e => nomatch e

def actual : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ x => |x|) emptyAnchor

def rejected : Realization signature.{u,v} := realize signature.{u,v} (fun _ _ _ => 1) emptyAnchor

def theoremLaw (family : Realization signature.{u,v}) : Prop := ∀
    {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] V) (C : V →L[ℝ] W)
    (β η : ℝ) (_hβ : 0 < β) (_hη : 0 < η),
    let H := C.adjoint.comp C
    let G : ℝ → V →L[ℝ] V := fun T =>
      ∫ t in (0 : ℝ)..T, (C.comp (NormedSpace.exp (t • B))).adjoint.comp
        (C.comp (NormedSpace.exp (t • B)))
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ T : ℝ, 0 < T → T ≤ δ →
      family.readout () { V := V, W := W, B := B, C := C, beta := β, eta := η } ((1 / 2 : ℝ) * Real.log ((ContinuousLinearMap.id ℝ V +
          (β * η)⁻¹ • G T).det) -
        T / (2 * β * η) * LinearMap.trace ℝ V H.toLinearMap) ≤ K * T ^ 2

def arena : Arena where
  signature := signature.{u,v}
  Law := theoremLaw.{u,v}

theorem actual_law : arena.{u,v}.Law actual.{u,v} := by
  intro V W _ _ _ _ _ _ B C beta eta hbeta heta
  exact _root_.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information B C beta eta hbeta heta

theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  let V := EuclideanSpace ℝ (ULift.{u} (Fin 0))
  let W := EuclideanSpace ℝ (ULift.{v} (Fin 0))
  have hh := h (V:=V) (W:=W) 0 0 1 1 zero_lt_one zero_lt_one
  dsimp only [theoremLaw,rejected,realize] at hh
  obtain ⟨K,delta,hK,hdelta,hbound⟩ := hh
  let T := min (delta/2) (min 1 (2*(K+1))⁻¹)
  have hp:0<2*(K+1) := by linarith
  have hT:0<T := lt_min (half_pos hdelta) (lt_min zero_lt_one (inv_pos.mpr hp))
  have hTd:T≤delta := (min_le_left _ _).trans (by linarith)
  have hT1:T≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hTi:T≤(2*(K+1))⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hb := hbound T hT hTd
  have hKi:K*(2*(K+1))⁻¹<1 := (mul_inv_lt_iff₀ hp).2 (by linarith)
  have hKT:K*T<1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hTi hK) hKi
  nlinarith [mul_nonneg hK (mul_nonneg hT.le (sub_nonneg.mpr hT1))]

theorem dependence_proof : ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro role
  let V := EuclideanSpace ℝ (ULift.{u} (Fin 0))
  let W := EuclideanSpace ℝ (ULift.{v} (Fin 0))
  refine ⟨{V:=V,W:=W,B:=0,C:=0,beta:=1,eta:=1},0,1,?_⟩
  norm_num [actual,realize]

def registration : Registration arena.{u,v} (arena.{u,v}.Law actual.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro other hne
      exact (hne (by cases role; cases other; rfl)).elim
    · intro e; exact nomatch e
  dependence := dependence_proof

register_information_theorem _root_.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation.physical_fixed_noise_information in arena
  readout via (realize signature.{u,v} (fun _ _ x => |x|) emptyAnchor)
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
    coordinates := #[0,1,8,9,10,11]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "fn", "arg" ]
      stateOperand := some #["arg"] }] })
  escape continues (open)
end Reg.D5.S3.Observer.Linear.PhysicalFixedNoiseInformation
