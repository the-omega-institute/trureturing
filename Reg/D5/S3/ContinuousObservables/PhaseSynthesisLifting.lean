import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ContinuousObservables.PhaseSynthesisLifting

/-! Source-domain registration for the full native same-witness consumer. -/
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting
open D5.S3.ContinuousObservables.ProjectedUnitaryLifting.Scalar
open D5.S3.ContinuousObservables.PhaseSynthesisLifting
open D5.S3.ContinuousObservables.PhaseSynthesis
open D5.S3.ContinuousObservables.IntervalSOSCompletion
open D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly
open D5.S3.ContinuousObservables.CentralWinding
open Polynomial Complex
noncomputable section
universe u
namespace Reg.D5.S3.ContinuousObservables.PhaseSynthesisLifting

abbrev signature : Signature where
  Params := ℝ
  State _ := List ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CyclicObservable 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature (fun _ φ Φ => phaseProduct φ Φ) (fun a => nomatch a)
def rejected := realize signature (fun _ _ _ => 0) (fun a => nomatch a)

def nativeLaw (r : Realization signature) : Prop :=
  ∀
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    (rawU Pi PiTilde : H →ₗ[ℂ] H)
    (hU : star rawU * rawU = 1) (hU' : rawU * star rawU = 1)
    (hPi : IsStarProjection Pi) (hPiTilde : IsStarProjection PiTilde)
    (d : ℕ) (hd : 0 < d) (p : ℝ[X]) (hp : p.natDegree ≤ d)
    (hpar : HasParity (p.map (algebraMap ℝ ℂ)) d)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1),
    ∃ (B C : ℝ[X]) (Ufield : D5.S3.ContinuousObservables.CentralWinding.CyclicObservable 2)
      (φ₀ : ℝ) (Φ : List ℝ) (hne : Φ ≠ []),
      1 - p ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧
      B.natDegree ≤ d ∧ C.natDegree ≤ d - 1 ∧ (d = 0 → C = 0) ∧
      HasParity (B.map (algebraMap ℝ ℂ)) d ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (d - 1) ∧
      Ufield = phaseCompletion p B C ∧ star Ufield * Ufield = 1 ∧
      Ufield * star Ufield = 1 ∧ (∀ t, (Ufield t).det = 1) ∧
      (∀ t, (Ufield t 0 0).re = p.eval
        (D5.S3.ContinuousObservables.CentralWinding.windingPhase t).re) ∧
      Φ.length = d ∧
      qspPolyW φ₀ Φ = (p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ),
        C.map (algebraMap ℝ ℂ)) ∧ r.readout () φ₀ Φ = Ufield ∧
      let Ψ := cor8Phases φ₀ Φ hne
      let P := p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ)
      let E := ofRaw rawU Pi PiTilde hU hU' hPi hPiTilde
      let A := PiTilde * rawU * Pi
      Ψ.length = d ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, seqR Ψ x 0 0 = P.eval (x : ℂ)) ∧
      (Even d → Pi * altSeq E Ψ * Pi =
        Pi * aeval (LinearMap.adjoint A * A) (evenRoot P) * Pi) ∧
      (Odd d → PiTilde * altSeq E Ψ * Pi =
        A * aeval (LinearMap.adjoint A * A) (oddRoot P))

abbrev arena.{u} : Arena where
  signature := signature
  Law := nativeLaw.{u}

theorem actualLaw : arena.{u}.Law actual := by
  intro H _ _ _ rawU Pi PiT hU hU' hPi hPiT d hd p hp hpar hb
  exact native_phase_lifting rawU Pi PiT hU hU' hPi hPiT d hd p hp hpar hb

theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨B, C, Ufield, φ, Φ, hne, hsos, hB, hC, hC0, hBp, hCp,
    hfield, hleft, hright, hdet, hre, hlen, hpair, hproduct, hrest⟩ :=
    h (1 : K →ₗ[ℂ] K) 0 0
      (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one])
      (by simp [LinearMap.star_eq_adjoint, LinearMap.adjoint_one])
      (IsStarProjection.zero _) (IsStarProjection.zero _) 1 (by decide) 0 (by simp)
      (by simpa using hasParity_zero 1) (by simp)
  have hz : Ufield = 0 := by simpa [rejected, realize] using hproduct.symm
  have hc := congrArg (fun M : CyclicObservable 2 => M 0 0 0) hleft
  simp [hz] at hc

theorem actualDependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, [], [Real.pi], ?_⟩
  intro h
  have hs : phaseCompletion X 0 1 (0 : AddCircle (1 : ℝ)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [phaseCompletion, windingPhase] <;> rfl
  have hc := congrArg (fun M : CyclicObservable 2 => M 0 0 0) h
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp [actual, realize, phaseProduct, hs, phaseDiagonal, Matrix.mul_apply, hu, matrix2,
    Complex.exp_pi_mul_I, mul_comm] at hc

def family : Registration arena.{u} (type_of% (@native_phase_lifting.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a; exact nomatch a
  dependence := actualDependence

def nativeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_phase_lifting.{u})
    (type_of% (realize signature (fun _ φ Φ => phaseProduct φ Φ) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.ContinuousObservables.PhaseSynthesisLifting.nativeUnit
  realizationName := `Reg.D5.S3.ContinuousObservables.PhaseSynthesisLifting.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ φ Φ => phaseProduct φ Φ) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ContinuousObservables.PhaseSynthesisLifting
    definition := none
    coordinates := #[20]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ContinuousObservables.PhaseSynthesisLifting
