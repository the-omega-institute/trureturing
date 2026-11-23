import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets

/-! The residue mass depends on the weights used to evaluate the band. -/

namespace Reg.D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets
open _root_.D5.S3.Fourier.Concentration.CyclicCollisionCertificate
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open FiniteSpectralPerturbation (actual frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

private def erasedWeights : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (w : J → ℝ) (p : ℕ) (P : Finset ℕ) (Q B H D : ℕ)
    (_ : 2 ≤ Q) (_ : ∀ q ∈ P, q.Prime ∧ Q ≤ q) (_ : ∀ j, 0 ≤ w j)
    (_ : ∀ m ∈ piAntidiag univ p, ∀ n ∈ piAntidiag univ p,
      (latticeFrequency a m - latticeFrequency a n).natAbs ≤ D)
    (_ : (∏ y ∈ Icc (-(H : ℤ)) H, ((D : ℤ) - y).natAbs) < Q ^ (B + 1)),
    let A := piAntidiag (univ : Finset J) p
    let L := ∑ m ∈ A, ∑ n ∈ A,
      if (latticeFrequency a m - latticeFrequency a n).natAbs ≤ H
      then monomialWeight w m * monomialWeight w n else 0
    let C := fun q => cyclicCollisionMass q a (V.readout () ⟨J, w⟩) p
      ((Icc (-(H : ℤ)) H).image (fun y : ℤ => (y : ZMod q)))
    0 ≤ ∑ q ∈ P, (C q - L) ∧
      ∑ q ∈ P, (C q - L) ≤ ((min B P.card : ℕ) : ℝ) * ((∑ j, w j) ^ (2 * p) - L)

private abbrev Point := ULift.{u} Unit

private theorem erasedWeights_law : ¬ weightArena.{u}.Law erasedWeights := by
  intro law
  classical
  have h := law (J := Point.{u}) 0 1 1 {2} 2 0 0 0 (by decide)
    (by simp [Nat.prime_two]) (fun _ => zero_le_one) (by simp [latticeFrequency]) (by simp)
  have hdegree : piAntidiag (univ : Finset Point.{u}) 1 =
      ({(1 : Point.{u} → ℕ)} : Finset (Point.{u} → ℕ)) := by
    ext m
    simp only [mem_piAntidiag, mem_singleton, univ_unique,
      sum_singleton]
    constructor
    · intro hm
      funext j
      rw [Subsingleton.elim j default]
      exact hm.1
    · intro hm
      rw [hm]
      exact ⟨rfl, fun i _ => Subsingleton.elim i default⟩
  have hweight : monomialWeight (1 : Point.{u} → ℝ) 1 = 1 := by
    simp [monomialWeight, univ_unique]
  have hzero : monomialWeight (fun _ : Point.{u} => (0 : ℝ)) 1 = 0 := by
    simp [monomialWeight, univ_unique]
  have hlower := h.1
  simp only [sum_singleton] at hlower
  change 0 ≤ cyclicCollisionMass 2 0 (fun _ : Point.{u} => 0) 1 _ - _ at hlower
  unfold cyclicCollisionMass at hlower
  simp only [hdegree, sum_singleton, hweight, hzero] at hlower
  norm_num [latticeFrequency] at hlower

def weightEvidence :
    Registration weightArena.{u} (type_of% @sum_cyclic_excess_le.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_cyclic_excess_le.{u}, erasedWeights, erasedWeights_law⟩
  sensitivity := sensitivity weightArena.Law actual erasedWeights erasedWeights_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def weightRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_cyclic_excess_le.{u}) (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets.weightUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets.weightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena.{u}⟩
  objectArena := .source ⟨weightArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena.{u} ⟨weightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "value", "body",
        "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightRegistration

end

end Reg.D5.S3.Fourier.Concentration.PrimeCyclicCollisionBudgets
