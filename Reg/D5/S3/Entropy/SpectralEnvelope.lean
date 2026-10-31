import LeanInformationAuditInterface.Contract.Registration
import Batteries.Tactic.OpenPrivate
import D5.S3.Entropy.SpectralEnvelope
import Reg.D5.S3.Entropy.CountableSpectralMoments

noncomputable section
open _root_.D5.S3.Entropy.CountableSpectralMoments
open _root_.D5.S3.Entropy.SpectralEnvelopeParameters
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Entropy.CountableSpectralMoments
open LeanInformationAudit
open private threshold_bounds from D5.S3.Entropy.FiniteSpectralEnvelope
open private three_summable three_mass three_purity three_nonneg from
  Reg.D5.S3.Entropy.CountableSpectralMoments

namespace Reg.D5.S3.Entropy.SpectralEnvelope

def budgetLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 →
    1 / 3 ≤ purity p → purity p ≤ 3 / 8 → envelope (purity p) ≤ R.readout () () p

theorem budgetActual : budgetLaw actual := by
  intro p hp hn hm hl hu
  exact _root_.D5.S3.Entropy.SpectralEnvelope.countable_budget_envelope hp hn hm hl hu

theorem budgetRejected : ¬ budgetLaw zeroReadout := by
  intro h
  have hz := h (three_summable (1 / 3))
    (three_nonneg (by norm_num) (by norm_num)) (three_mass _)
    (by rw [three_purity]; norm_num) (by rw [three_purity]; norm_num)
  norm_num [zeroReadout, realize, three_purity, envelope] at hz

def budgetFamily : Registration ⟨momentSignature, budgetLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 →
      1 / 3 ≤ purity p → purity p ≤ 3 / 8 → envelope (purity p) ≤ third p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨budgetActual, zeroReadout, budgetRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity budgetLaw actual zeroReadout budgetRejected
  dependence := actualDependence

def budgetRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.SpectralEnvelope.countable_budget_envelope)
    (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.SpectralEnvelope.budgetUnit
  realizationName := `Reg.D5.S3.Entropy.SpectralEnvelope.budgetFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, budgetLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, budgetLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, budgetLaw⟩ ⟨budgetFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.SpectralEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def uniformLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 →
    purity p ≤ 3 / 8 → 25 / 864 ≤ R.readout () () p

theorem uniformActual : uniformLaw actual := by
  intro p hp hn hm hq
  exact _root_.D5.S3.Entropy.SpectralEnvelope.third_lower_of_purity_le_three_eighths hp hn hm hq

theorem uniformRejected : ¬ uniformLaw zeroReadout := by
  intro h
  have hz := h (three_summable (1 / 3))
    (three_nonneg (by norm_num) (by norm_num)) (three_mass _)
    (by rw [three_purity]; norm_num)
  norm_num [zeroReadout, realize] at hz

def uniformFamily : Registration ⟨momentSignature, uniformLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 →
      purity p ≤ 3 / 8 → 25 / 864 ≤ third p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniformActual, zeroReadout, uniformRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity uniformLaw actual zeroReadout uniformRejected
  dependence := actualDependence

def uniformRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.SpectralEnvelope.third_lower_of_purity_le_three_eighths)
    (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.SpectralEnvelope.uniformUnit
  realizationName := `Reg.D5.S3.Entropy.SpectralEnvelope.uniformFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, uniformLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, uniformLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, uniformLaw⟩ ⟨uniformFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.SpectralEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def thresholdLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 →
    purity p ≤ threshold → 1 / 32 ≤ R.readout () () p

theorem thresholdActual : thresholdLaw actual := by
  intro p hp hn hm hq
  exact _root_.D5.S3.Entropy.SpectralEnvelope.third_lower_of_purity_le_threshold hp hn hm hq

theorem thresholdRejected : ¬ thresholdLaw zeroReadout := by
  intro h
  have hz := h (three_summable (1 / 3))
    (three_nonneg (by norm_num) (by norm_num)) (three_mass _)
    (by rw [three_purity]; norm_num; exact threshold_bounds.1)
  norm_num [zeroReadout, realize] at hz

def thresholdFamily : Registration ⟨momentSignature, thresholdLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 →
      purity p ≤ threshold → 1 / 32 ≤ third p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨thresholdActual, zeroReadout, thresholdRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity thresholdLaw actual zeroReadout thresholdRejected
  dependence := actualDependence

def thresholdRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.SpectralEnvelope.third_lower_of_purity_le_threshold)
    (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.SpectralEnvelope.thresholdUnit
  realizationName := `Reg.D5.S3.Entropy.SpectralEnvelope.thresholdFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, thresholdLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, thresholdLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, thresholdLaw⟩ ⟨thresholdFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.SpectralEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Entropy.SpectralEnvelope
