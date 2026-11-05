import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Solenoid.DyadicRootFiberArithmetic

/-! The observation is the actual multiplication homomorphism at every degree.
The law retains the original telescope and all target fibers. -/

noncomputable section
namespace Reg.D5.S1.Solenoid.DyadicRootFiberArithmetic

open _root_.D5.S1.Solenoid
open _root_.D5.S1.Solenoid.DyadicSolenoid
open _root_.D5.S3.ConceptDynamics.InformationEscape

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => DyadicSolenoid →+ DyadicSolenoid
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ _ z => nsmulAddMonoidHom (2 ^ z.1 * z.2)) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ k q : ℕ, Odd q →
    Nonempty ((r.readout () () (k, q)).ker ≃+ ZMod q) ∧
    ∀ a : DyadicSolenoid,
      Finite {x : DyadicSolenoid // r.readout () () (k, q) x = a} ∧
      Nat.card {x : DyadicSolenoid // r.readout () () (k, q) x = a} = q

abbrev sourceScope := type_of% dyadic_root_fiber_arithmetic

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : DyadicSolenoid →+ DyadicSolenoid)) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := dyadic_time_separation.2.2.2.2.2.2.1
  have : IsEmpty {x : DyadicSolenoid // (0 : DyadicSolenoid →+ DyadicSolenoid) x = thirdPoint} :=
    ⟨fun x => hn (by simpa using x.2.symm)⟩
  have hc := ((h 0 1 (by decide)).2 thirdPoint).2
  change Nat.card {x : DyadicSolenoid // (0 : DyadicSolenoid →+ DyadicSolenoid) x = thirdPoint} = 1 at hc
  simpa using hc

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp dyadic_root_fiber_arithmetic, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i
      exact Empty.elim i
  dependence := by
    intro i
    cases i
    refine ⟨(), (0, 1), (0, 3), ?_⟩
    intro he
    have hv := congrArg (fun f : DyadicSolenoid →+ DyadicSolenoid => f thirdPoint) he
    have hn := dyadic_time_separation.2.2.2.2.2.2.1
    have ht := dyadic_time_separation.2.2.2.2.2.2.2.1
    apply hn
    simpa [actual, DependentFamily.realize, ht] using hv

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      dyadic_root_fiber_arithmetic (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S1.Solenoid.DyadicSolenoid.dyadic_root_fiber_arithmetic.__information_unit
  realizationName := `Reg.D5.S1.Solenoid.DyadicRootFiberArithmetic.familyRegistration
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
    (fun _ _ z => nsmulAddMonoidHom (2 ^ z.1 * z.2)) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Solenoid.DyadicRootFiberArithmetic
