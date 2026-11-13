import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ContinuousObservables.PhaseSynthesis
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ContinuousObservables.PhaseSynthesis
open _root_.D5.S3.ContinuousObservables.IntervalSOSCompletion
open _root_.D5.S3.ContinuousObservables.IntervalSOSCompletion.Poly
open _root_.D5.S3.ContinuousObservables.CentralWinding
open Polynomial Complex

noncomputable section
namespace Reg.D5.S3.ContinuousObservables.PhaseSynthesis

abbrev signature : Signature where
  Params := ℝ
  State _ := List ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ[X] × ℂ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ φ₀ Φ => qspPolyW φ₀ Φ) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (0, 0)) (fun e => nomatch e)

private theorem parity_one : HasParity (1 : ℂ[X]) 0 := by
  constructor
  · intro _ n hn
    have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
    simp [hn0]
  · intro h
    simp at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, [], [0], ?_⟩
  intro h
  have hh := congrArg Prod.snd h
  simpa [actual, realize, qspPolyW, stepW] using hh

abbrev pairArena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (P Q : ℂ[X]) (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ k - 1)
    (hQ0 : k = 0 → Q = 0) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1),
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧ R.readout () φ₀ Φ = (P, Q)

private theorem pairRejectedLaw : ¬ pairArena.Law rejected := by
  intro h
  obtain ⟨φ₀, Φ, hlen, heq⟩ := h 0 1 0 (by simp) (by simp)
    (fun _ => rfl) parity_one (hasParity_zero _) (by simp [conjP])
  have hh := congrArg Prod.fst heq
  simpa [rejected, realize] using hh

def pairFamily : Registration pairArena (type_of% (@exists_phases)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_phases, rejected, pairRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · exact pairRejectedLaw
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def pairRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_phases) (Realization signature) (type_of% (@qspPolyW)) Unit := {
  unitName := `D5.S3.ContinuousObservables.PhaseSynthesis.exists_phases.information_unit
  realizationName := `Reg.D5.S3.ContinuousObservables.PhaseSynthesis.pairFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena⟩
  objectArena := .source ⟨pairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairArena ⟨pairFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ φ₀ Φ => qspPolyW φ₀ Φ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@qspPolyW)
  sourceSelection := some {
    owner := `D5.S3.ContinuousObservables.PhaseSynthesis
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev nativeArena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k)
    (hpar : HasParity (p.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p.eval x ^ 2 ≤ 1),
    ∃ (B C : ℝ[X]) (U : CyclicObservable 2) (φ₀ : ℝ) (Φ : List ℝ),
      1 - p ^ 2 = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧
      B.natDegree ≤ k ∧ C.natDegree ≤ k - 1 ∧ (k = 0 → C = 0) ∧
      HasParity (B.map (algebraMap ℝ ℂ)) k ∧
      HasParity (C.map (algebraMap ℝ ℂ)) (k - 1) ∧
      U = phaseCompletion p B C ∧ star U * U = 1 ∧ U * star U = 1 ∧
      (∀ t, (U t).det = 1) ∧ (∀ t, (U t 0 0).re = p.eval (windingPhase t).re) ∧
      Φ.length = k ∧
      R.readout () φ₀ Φ =
        (p.map (algebraMap ℝ ℂ) + Polynomial.C I * B.map (algebraMap ℝ ℂ),
          C.map (algebraMap ℝ ℂ)) ∧ phaseProduct φ₀ Φ = U

private theorem nativeRejectedLaw : ¬ nativeArena.Law rejected := by
  intro h
  obtain ⟨B, C, U, φ₀, Φ, hsos, hB, hC, hC0, hBp, hCp, hU,
    hl, hr, hd, hre, hlen, hpair, hprod⟩ := h 0 1 (by simp)
      (by simpa using parity_one) (by intro x hx; simp)
  have hh := congrArg (fun pq : ℂ[X] × ℂ[X] => (pq.1.coeff 0).re) hpair
  simpa [rejected, realize] using hh

def nativeFamily : Registration nativeArena (type_of% (@exists_phase_factorization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_phase_factorization, rejected, nativeRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · exact nativeRejectedLaw
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def nativeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_phase_factorization) (Realization signature) (type_of% (@qspPolyW)) Unit := {
  unitName := `D5.S3.ContinuousObservables.PhaseSynthesis.exists_phase_factorization.information_unit
  realizationName := `Reg.D5.S3.ContinuousObservables.PhaseSynthesis.nativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨nativeArena⟩
  objectArena := .source ⟨nativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nativeArena ⟨nativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ φ₀ Φ => qspPolyW φ₀ Φ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@qspPolyW)
  sourceSelection := some {
    owner := `D5.S3.ContinuousObservables.PhaseSynthesis
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.ContinuousObservables.PhaseSynthesis
