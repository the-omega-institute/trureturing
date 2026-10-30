import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Solenoid.DyadicTimeSeparation

/-! The readout is the actual rational homomorphism evaluated along the quarter sequence.
The law preserves every conjunct of the concrete dyadic-solenoid statement. -/

noncomputable section
namespace Reg.D5.S1.Solenoid.DyadicTimeSeparation

open _root_.D5.S1.Solenoid
open _root_.D5.S1.Solenoid.DyadicSolenoid
open _root_.D5.S3.ConceptDynamics.InformationEscape

abbrev TimeState := (ℚ →+ DyadicSolenoid) × ℕ

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => TimeState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => DyadicSolenoid
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ z => z.1 ((1 / 4 : ℚ)^z.2))
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law r :=
    CompactSpace DyadicSolenoid ∧ ConnectedSpace DyadicSolenoid ∧
    Continuous realFlow ∧ DenseRange realFlow ∧
    (∀ m : ℕ, 0 < m → Function.Surjective (fun x : DyadicSolenoid => m • x)) ∧
    (∀ x : DyadicSolenoid, 2 • x = 0 → x = 0) ∧
    thirdPoint ≠ 0 ∧ 3 • thirdPoint = 0 ∧
    (∃ phi : ℚ →+ DyadicSolenoid, phi 1 = thirdPoint) ∧
    (∀ phi : ℚ →+ DyadicSolenoid, phi 1 = thirdPoint →
      (∀ n : ℕ, r.readout () () (phi, n) = thirdPoint) ∧ ¬ Continuous phi) ∧
    (¬ ∃ psi : ℝ →+ DyadicSolenoid, Continuous psi ∧ psi 1 = thirdPoint)

abbrev sourceScope := type_of% dyadic_time_separation

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : DyadicSolenoid)) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, _, _, _, _, _, hn, _, ⟨phi, hp⟩, hseq, _⟩
  have he := (hseq phi hp).1 0
  change (0 : DyadicSolenoid) = thirdPoint at he
  exact hn he.symm

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp dyadic_time_separation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro i
      exact Empty.elim i
  dependence := by
    intro i
    cases i
    obtain ⟨_, _, _, _, _, _, hn, _, ⟨phi, hp⟩, _, _⟩ := dyadic_time_separation
    refine ⟨(), (phi, 0), (0, 0), ?_⟩
    change phi ((1 / 4 : ℚ)^0) ≠ (0 : ℚ →+ DyadicSolenoid) ((1 / 4 : ℚ)^0)
    simpa only [pow_zero, hp, AddMonoidHom.zero_apply] using hn

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      dyadic_time_separation (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S1.Solenoid.DyadicSolenoid.dyadic_time_separation.__information_unit
  realizationName := `Reg.D5.S1.Solenoid.DyadicTimeSeparation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ z => z.1 ((1 / 4 : ℚ)^z.2)) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Solenoid.DyadicTimeSeparation
