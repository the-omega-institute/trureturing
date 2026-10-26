import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.CountableSpectralMoments
import D5.S3.Entropy.SpectralEnvelopeParameters
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

noncomputable section
open scoped BigOperators
open D5.S3.Entropy.CountableSpectralMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private three_third three_summable three_mass three_purity from
  D5.S3.Entropy.SpectralEnvelopeParameters

namespace Reg.D5.S3.Entropy.CountableSpectralMoments

abbrev momentSignature : Signature where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize momentSignature (fun _ _ p => third p) (fun a => nomatch a)
def rejected := realize momentSignature (fun _ _ _ => 1) (fun a => nomatch a)

def newtonLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p ≤ 1 →
    6 * R.readout () () p = mass p ^ 3 - 3 * mass p * purity p + 2 * cubicMoment p

abbrev newtonArena : Arena where
  signature := momentSignature
  Law := newtonLaw

theorem actualLaw : newtonArena.Law actual := by
  intro p hp hn hm
  exact D5.S3.Entropy.CountableSpectralMoments.countable_newton hp hn hm

theorem rejectedLaw : ¬ newtonArena.Law rejected := by
  intro h
  have hz := h (p := fun _ => 0) (by simp) (by simp) (by simp [mass])
  norm_num [rejected, realize, mass, purity, cubicMoment] at hz

theorem actualDependence : ObservationalDependence momentSignature actual := by
  intro i
  refine ⟨(), (fun _ => 0),
    D5.S3.Entropy.SpectralEnvelopeParameters.threeSpectrum (1 / 3), ?_⟩
  change third (fun _ => 0) ≠ third
    (D5.S3.Entropy.SpectralEnvelopeParameters.threeSpectrum (1 / 3))
  rw [three_third]
  norm_num [third, tripleLayer]

def newtonFamily : Registration newtonArena
    (∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p ≤ 1 →
      6 * third p = mass p ^ 3 - 3 * mass p * purity p + 2 * cubicMoment p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := actualDependence

-- The telescope has p, summability, nonnegativity and the mass bound.
-- The selected operand is precisely `third p` in the left side of the equality.
-- Source-path/binding acceptance is pending the current compiled report.
def newtonRegistration : Contract.Registration
    (@D5.S3.Entropy.CountableSpectralMoments.countable_newton)
    (type_of% (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Entropy.CountableSpectralMoments.newtonUnit
  realizationName := `Reg.D5.S3.Entropy.CountableSpectralMoments.newtonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨newtonArena⟩
  objectArena := .source ⟨newtonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source newtonArena ⟨newtonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.CountableSpectralMoments
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms newtonFamily
#print axioms newtonRegistration

private theorem three_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ∀ i, 0 ≤ D5.S3.Entropy.SpectralEnvelopeParameters.threeSpectrum x i := by
  intro i
  unfold D5.S3.Entropy.SpectralEnvelopeParameters.threeSpectrum
  split_ifs <;> linarith

def absoluteLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) →
    Summable (fun t => ‖tripleTerm p t‖) ∧ (∑' t, tripleTerm p t) = R.readout () () p

theorem absoluteActual : absoluteLaw actual := by
  intro p hp hn
  exact D5.S3.Entropy.CountableSpectralMoments.absolute_triple_sum hp hn

theorem absoluteRejected : ¬ absoluteLaw rejected := by
  intro h
  have hz := (h (p := fun _ => 0) (by simp) (by simp)).2
  norm_num [rejected, realize, tripleTerm] at hz

def absoluteFamily : Registration ⟨momentSignature, absoluteLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) →
      Summable (fun t => ‖tripleTerm p t‖) ∧ (∑' t, tripleTerm p t) = third p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨absoluteActual, rejected, absoluteRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity absoluteLaw actual rejected absoluteRejected
  dependence := actualDependence

def absoluteRegistration : Contract.Registration
    (@D5.S3.Entropy.CountableSpectralMoments.absolute_triple_sum) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.CountableSpectralMoments.absoluteUnit
  realizationName := `Reg.D5.S3.Entropy.CountableSpectralMoments.absoluteFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, absoluteLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, absoluteLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, absoluteLaw⟩ ⟨absoluteFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some
    { owner := `D5.S3.Entropy.CountableSpectralMoments, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def negative := realize momentSignature (fun _ _ _ => -1) (fun a => nomatch a)
def nonnegativeLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, (∀ i, 0 ≤ p i) → 0 ≤ R.readout () () p

theorem nonnegativeActual : nonnegativeLaw actual := by
  intro p hn
  exact D5.S3.Entropy.CountableSpectralMoments.third_nonneg hn

theorem nonnegativeRejected : ¬ nonnegativeLaw negative := by
  intro h
  have hz := h (p := fun _ => 0) (by simp)
  norm_num [negative, realize] at hz

def nonnegativeFamily : Registration ⟨momentSignature, nonnegativeLaw⟩
    (∀ {p : ℕ → ℝ}, (∀ i, 0 ≤ p i) → 0 ≤ third p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nonnegativeActual, negative, nonnegativeRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity nonnegativeLaw actual negative nonnegativeRejected
  dependence := actualDependence

def nonnegativeRegistration : Contract.Registration
    (@D5.S3.Entropy.CountableSpectralMoments.third_nonneg) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.CountableSpectralMoments.nonnegativeUnit
  realizationName := `Reg.D5.S3.Entropy.CountableSpectralMoments.nonnegativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, nonnegativeLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, nonnegativeLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, nonnegativeLaw⟩ ⟨nonnegativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some
    { owner := `D5.S3.Entropy.CountableSpectralMoments, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def zeroReadout := realize momentSignature (fun _ _ _ => 0) (fun a => nomatch a)
def lowPurityLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 → purity p ≤ 1 / 3 →
    (1 - 3 * purity p + 2 * purity p ^ 2) / 6 ≤ R.readout () () p ∧
    1 / 27 ≤ (1 - 3 * purity p + 2 * purity p ^ 2) / 6

theorem lowPurityActual : lowPurityLaw actual := by
  intro p hp hn hm hq
  exact D5.S3.Entropy.CountableSpectralMoments.third_lower_of_purity_le_third hp hn hm hq

theorem lowPurityRejected : ¬ lowPurityLaw zeroReadout := by
  intro h
  have hz := (h (three_summable (1 / 3)) (three_nonneg (by norm_num) (by norm_num))
    (three_mass _) (by rw [three_purity]; norm_num)).1
  norm_num [zeroReadout, realize, three_purity] at hz

def lowPurityFamily : Registration ⟨momentSignature, lowPurityLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ i, 0 ≤ p i) → mass p = 1 → purity p ≤ 1 / 3 →
      (1 - 3 * purity p + 2 * purity p ^ 2) / 6 ≤ third p ∧
      1 / 27 ≤ (1 - 3 * purity p + 2 * purity p ^ 2) / 6) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lowPurityActual, zeroReadout, lowPurityRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity lowPurityLaw actual zeroReadout lowPurityRejected
  dependence := actualDependence

def lowPurityRegistration : Contract.Registration
    (@D5.S3.Entropy.CountableSpectralMoments.third_lower_of_purity_le_third) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.CountableSpectralMoments.lowPurityUnit
  realizationName := `Reg.D5.S3.Entropy.CountableSpectralMoments.lowPurityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, lowPurityLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, lowPurityLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, lowPurityLaw⟩ ⟨lowPurityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some
    { owner := `D5.S3.Entropy.CountableSpectralMoments, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def distinguishedLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ j, 0 ≤ p j) → mass p = 1 → ∀ i : ℕ,
    R.readout () () p - 1 / 32 =
      (2 * p i - 1) * (4 * p i - 1) ^ 2 / 32 +
      (p i / 2) * (3 / 8 - purity p) + third (erase p i)

theorem distinguishedActual : distinguishedLaw actual := by
  intro p hp hn hm i
  exact D5.S3.Entropy.CountableSpectralMoments.distinguished_identity hp hn hm i

theorem distinguishedRejected : ¬ distinguishedLaw rejected := by
  intro h
  have hr := h (three_summable (1 / 3)) (three_nonneg (by norm_num) (by norm_num)) (three_mass _) 0
  have ha := distinguishedActual (three_summable (1 / 3))
    (three_nonneg (by norm_num) (by norm_num)) (three_mass _) 0
  change 1 - 1 / 32 = _ at hr
  change third _ - 1 / 32 = _ at ha
  rw [three_third] at ha
  norm_num at ha
  linarith

def distinguishedFamily : Registration ⟨momentSignature, distinguishedLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ j, 0 ≤ p j) → mass p = 1 → ∀ i : ℕ,
      third p - 1 / 32 =
        (2 * p i - 1) * (4 * p i - 1) ^ 2 / 32 +
        (p i / 2) * (3 / 8 - purity p) + third (erase p i)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨distinguishedActual, rejected, distinguishedRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity distinguishedLaw actual rejected distinguishedRejected
  dependence := actualDependence

def distinguishedRegistration : Contract.Registration
    (@D5.S3.Entropy.CountableSpectralMoments.distinguished_identity) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.CountableSpectralMoments.distinguishedUnit
  realizationName := `Reg.D5.S3.Entropy.CountableSpectralMoments.distinguishedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, distinguishedLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, distinguishedLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, distinguishedLaw⟩ ⟨distinguishedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some
    { owner := `D5.S3.Entropy.CountableSpectralMoments, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def halfLaw (R : Realization momentSignature) : Prop :=
  ∀ {p : ℕ → ℝ}, Summable p → (∀ j, 0 ≤ p j) → mass p = 1 → purity p ≤ 3 / 8 →
    ∀ i : ℕ, 1 / 2 ≤ p i → 1 / 32 ≤ R.readout () () p

theorem halfActual : halfLaw actual := by
  intro p hp hn hm hq i hi
  exact D5.S3.Entropy.CountableSpectralMoments.third_lower_of_distinguished_ge_half hp hn hm hq i hi

theorem halfRejected : ¬ halfLaw zeroReadout := by
  intro h
  have hz := h (three_summable (1 / 4)) (three_nonneg (by norm_num) (by norm_num))
    (three_mass _) (by rw [three_purity]; norm_num) 2
    (by norm_num [D5.S3.Entropy.SpectralEnvelopeParameters.threeSpectrum])
  norm_num [zeroReadout, realize] at hz

def halfFamily : Registration ⟨momentSignature, halfLaw⟩
    (∀ {p : ℕ → ℝ}, Summable p → (∀ j, 0 ≤ p j) → mass p = 1 → purity p ≤ 3 / 8 →
      ∀ i : ℕ, 1 / 2 ≤ p i → 1 / 32 ≤ third p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨halfActual, zeroReadout, halfRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity halfLaw actual zeroReadout halfRejected
  dependence := actualDependence

def halfRegistration : Contract.Registration
    (@D5.S3.Entropy.CountableSpectralMoments.third_lower_of_distinguished_ge_half) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.CountableSpectralMoments.halfUnit
  realizationName := `Reg.D5.S3.Entropy.CountableSpectralMoments.halfFamily
  realizationSource := none
  generated := false
  arena := .source ⟨⟨momentSignature, halfLaw⟩⟩
  objectArena := .source ⟨⟨momentSignature, halfLaw⟩⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ⟨momentSignature, halfLaw⟩ ⟨halfFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ p => third p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some
    { owner := `D5.S3.Entropy.CountableSpectralMoments, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Entropy.CountableSpectralMoments
