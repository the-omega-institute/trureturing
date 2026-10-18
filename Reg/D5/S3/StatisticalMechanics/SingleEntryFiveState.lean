import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntryFiveState
import Reg.Support.SingleDependentReadout

/-! # The same forward trajectory supplies the association observation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiveState
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open Matrix

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Rates, ℝ → Fin 5 → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actualReadout : ∀ role p, (signature).State p → (signature).Output role p :=
  fun _ p x => association p.2 x

def actualAnchor : ∀ (_ : (signature).Anchor) p, (signature).State p :=
  fun e => nomatch e

def actual : Realization signature :=
  realize signature actualReadout actualAnchor

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both the probability-law existence clause and the full arbitrary-solution
clause remain. Only its actual time-dependent association is observed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Rates,
    ((∃ p : ℝ → Fin 5 → ℝ, ForwardSolution k p ∧
      (∀ t, 0 ≤ t → (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      ∀ t, 0 < t →
        pyramidLaw p t ∈ D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openSimplex ∧
        D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.visible (pyramidLaw p t) ∈
          D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openPyramid) ∧
      (∀ i, 0 < equilibriumLaw k i) ∧ (∑ i, equilibriumLaw k i) = 1 ∧
      generator k *ᵥ equilibriumLaw k = 0 ∧
      association (fun _ => equilibriumLaw k) 0 = 0 ∧
      0 < fiberWidth (fun _ => equilibriumLaw k) 0 ∧
      activeMass (fun _ => equilibriumLaw k) 0 =
        k.theta / (k.theta + k.eta *
          (k.b / (k.a + k.b) * (k.d / (k.c + k.d))))) ∧
    (∀ (p : ℝ → Fin 5 → ℝ), ForwardSolution k p → ∀ t, 0 < t →
      0 < activeMass p t ∧ 0 < fiberWidth p t ∧ 0 < R.readout () ⟨k, p⟩ t ∧
        p t 2 * p t 3 < p t 1 * p t 4 ∧
        0 < k.theta * p t 0 - k.eta * p t 1 ∧
        (∃ lam c : Fin 5 → ℝ,
          (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
          (∃ j, 0 < lam j * c j) ∧
          ∀ u, 0 ≤ u → p u 0 = ∑ j, c j * Real.exp (-lam j * u)) ∧
        ∀ f : Fin 5 → ℝ,
          taskError p f t = taskContrast f * association p t / activeMass p t ∧
          (taskContrast f ≠ 0 → 0 < taskContrast f * taskError p f t))

private def unitRates : Rates where
  a := 1
  b := 1
  c := 1
  d := 1
  eta := 1
  theta := 1
  a_pos := by norm_num
  b_pos := by norm_num
  c_pos := by norm_num
  d_pos := by norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private theorem rejected_law : ¬ arena.Law rejected := by
  obtain ⟨p, hp, _⟩ := (five_state_strict_association unitRates).1.1
  intro h
  have hh := ((h unitRates).2 p hp 1 (by norm_num)).2.2.1
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  obtain ⟨p, hp, _⟩ := (five_state_strict_association unitRates).1.1
  have hpos := ((five_state_strict_association unitRates).2 p hp 1 (by norm_num)).2.2.1
  have hzero : association p 0 = 0 := by
    simp [association, activeMass, firstOccupancy, secondOccupancy, hp.1]
  intro role
  refine ⟨⟨unitRates, p⟩, 0, 1, ?_⟩
  change association p 0 ≠ association p 1
  rw [hzero]
  exact ne_of_lt hpos

def family : Registration arena (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨five_state_strict_association, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiveState
  definition := none
  coordinates := #[0, 1]
  readouts := #[{
    path := #["body", "arg", "body", "body", "body", "body",
      "arg", "arg", "fn", "arg", "arg"]
    stateBinder := 3
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@five_state_strict_association) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- This is the full original occurrence, including its independent existence
clause. Its state is a real time selecting a law, not a single sample. -/
def analysisSource : Analysis.Source (@five_state_strict_association) :=
  Analysis.Source.ofRegistration _ family .exact selection

/-- Association is a law statistic on an infinite time-indexed family. No
finite microstate table or native continuation correspondence is supplied. -/
def analysis : AuricFib.Contract.Application (@five_state_strict_association) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Real time-indexed five-mode law: no finite presentation or native reader/continuation bridge" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

end Reg.D5.S3.StatisticalMechanics.SingleEntryFiveState
