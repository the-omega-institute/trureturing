import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass

/-! Dependence of the fixed-difference mass on the shifted factorial coefficient. -/

namespace Reg.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (diagonal monomialWeight)
open _root_.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℕ → ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => shiftedCoefficient x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
      (w : J → ℝ) (a b : J → ℕ) (p d : ℕ) (_ : d ≤ p)
      (_ : ∑ j, a j = d) (_ : ∑ j, b j = d) (_ : ∀ j, a j = 0 ∨ b j = 0),
    let coefficient := V.readout () ()
    (fixedDifferenceMass w a b p =
      (p.factorial : ℝ) ^ 2 * (∏ j, w j ^ (a j + b j)) *
        ∑ l ∈ piAntidiag univ (p - d), ∏ j, coefficient (w j ^ 2) (l j) (a j + b j)) ∧
    ((∀ j, 0 ≤ w j) → fixedDifferenceMass w a b p ≤
      (Nat.choose p d : ℝ) ^ 2 * diagonal w (p - d) *
        (monomialWeight w a * monomialWeight w b))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  have h := (law (J := ULift.{u} (Fin 1)) (fun _ => 1) 0 0 0 0
    (le_refl 0) (by simp) (by simp) (fun _ => Or.inl rfl)).1
  norm_num [rejected, realize, fixedDifferenceMass, Finset.sum_filter, monomialWeight, Nat.multinomial] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change shiftedCoefficient 0 ≠ shiftedCoefficient 1
  intro h
  have hvalue := congrFun (congrFun h 1) 0
  norm_num [shiftedCoefficient] at hvalue

def evidence : Registration arena.{u} (type_of% @fixed_difference_mass.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_difference_mass.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_difference_mass.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => shiftedCoefficient x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace FactorialExpansion

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (n.factorial : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J] (w : J → ℝ)
      (p : ℕ) (m : J → ℕ), (∑ j, m j = p) →
    monomialWeight w m = V.readout () () p *
      ∏ j, w j ^ m j / ((m j).factorial : ℝ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  have h := law (J := ULift.{u} (Fin 0)) (fun _ => 0) 0 (fun _ => 0) (by simp)
  norm_num [rejected, realize, monomialWeight, Nat.multinomial] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 2, ?_⟩
  change (Nat.factorial 0 : ℝ) ≠ (Nat.factorial 2 : ℝ)
  norm_num [Nat.factorial]

def evidence : Registration arena.{u} (type_of% @weight_factorials.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_factorials.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weight_factorials.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass.FactorialExpansion.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass.FactorialExpansion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n.factorial : ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FactorialExpansion

end

end Reg.D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass
