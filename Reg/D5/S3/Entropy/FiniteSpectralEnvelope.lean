import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.FiniteSpectralEnvelope
import Reg.Support.DependentFamily

noncomputable section
open scoped BigOperators
open _root_.D5.S3.Entropy.FiniteSpectralEnvelope
open _root_.D5.S3.Entropy.SpectralEnvelopeParameters
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private endpoint_constants from D5.S3.Entropy.SpectralEnvelopeParameters

universe u
namespace Reg.D5.S3.Entropy.FiniteSpectralEnvelope

abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize scalarSignature.{u} (fun _ _ q => envelope q) (fun a => nomatch a)
def rejected := realize scalarSignature.{u} (fun _ _ _ => 1) (fun a => nomatch a)

def envelopeLaw (R : Realization scalarSignature.{u}) : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (p : ι → ℝ),
    (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
    ∀ {q : ℝ}, 1 / 3 ≤ q → q ≤ 3 / 8 → finitePurity p ≤ q →
      R.readout ⟨()⟩ () q ≤ finiteThird p

abbrev envelopeArena : Arena where
  signature := scalarSignature.{u}
  Law := envelopeLaw

theorem actualLaw : envelopeArena.{u}.Law actual := by
  intro ι _ _ p hn hm q hq0 hq1 hpq
  exact _root_.D5.S3.Entropy.FiniteSpectralEnvelope.finite_budget_envelope p hn hm hq0 hq1 hpq

theorem rejectedLaw : ¬ envelopeArena.{u}.Law rejected := by
  intro h
  have hz := h (ι := ULift.{u} (Fin 3)) (fun _ => (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (q := 1 / 3) le_rfl (by norm_num)
    (by norm_num [finitePurity])
  norm_num [rejected, realize, finiteThird, finitePurity] at hz

theorem actualDependence : ObservationalDependence scalarSignature.{u} actual := by
  intro i
  refine ⟨(), 1 / 3, 3 / 8, ?_⟩
  change envelope (1 / 3) ≠ envelope (3 / 8)
  rw [endpoint_constants.1]
  norm_num [envelope]

def envelopeFamily : Registration envelopeArena (envelopeArena.Law actual) where
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

-- Readout occurrence reconstruction will be checked against the current
-- elaborated telescope. It is not reported as accepted from this source.
def envelopeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.FiniteSpectralEnvelope.finite_budget_envelope.{u})
    (type_of% (realize scalarSignature.{u} (fun _ _ q => envelope q) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Entropy.FiniteSpectralEnvelope.envelopeUnit
  realizationName := `Reg.D5.S3.Entropy.FiniteSpectralEnvelope.envelopeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨envelopeArena⟩
  objectArena := .source ⟨envelopeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source envelopeArena ⟨envelopeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature.{u} (fun _ _ q => envelope q) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.FiniteSpectralEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 6
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms envelopeFamily
#print axioms envelopeRegistration

end Reg.D5.S3.Entropy.FiniteSpectralEnvelope
