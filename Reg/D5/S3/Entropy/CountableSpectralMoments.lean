import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.CountableSpectralMoments
import D5.S3.Entropy.SpectralEnvelopeParameters
import Reg.Support.DependentFamily

noncomputable section
open scoped BigOperators
open D5.S3.Entropy.CountableSpectralMoments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private three_third from D5.S3.Entropy.SpectralEnvelopeParameters

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

end Reg.D5.S3.Entropy.CountableSpectralMoments
