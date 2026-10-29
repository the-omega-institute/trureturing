import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Solenoid.DyadicPathComponent

/-! The whole original two-point law observes the actual real-flow operand.
The typed family evidence does not supply raw source-domain selection. -/

noncomputable section
namespace Reg.D5.S1.Solenoid.DyadicPathComponent

open _root_.D5.S1.Solenoid
open _root_.D5.S1.Solenoid.DyadicSolenoid
open _root_.D5.S3.ConceptDynamics.InformationEscape

private theorem half_nonzero : realFlow (1 / 2 : ℝ) ≠ 0 := by
  intro h
  have hc : (((1 / 2 : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    simpa [realFlow] using congrArg (fun x : DyadicSolenoid => x.1 0) h
  have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico
    (show (1 / 2 : ℝ) ∈ Set.Ico 0 1 by constructor <;> norm_num)).mp hc
  norm_num at hz

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => DyadicSolenoid
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ t => realFlow t) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law r := ∀ x y : DyadicSolenoid,
    Joined x y ↔ ∃! t : ℝ, y = r.readout () () t + x

abbrev sourceScope := type_of% (@dyadic_path_orbit_classification)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : DyadicSolenoid)) (fun a => Empty.elim a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hj : Joined (0 : DyadicSolenoid) (realFlow (1 / 2 : ℝ)) := by
    refine ⟨Path.mk
      ⟨fun u => realFlow ((u : ℝ) * (1 / 2 : ℝ)),
        dyadic_time_separation.2.2.1.comp (continuous_subtype_val.mul continuous_const)⟩
      (by simp) (by simp)⟩
  obtain ⟨t, ht, _⟩ := (h 0 (realFlow (1 / 2 : ℝ))).mp hj
  exact half_nonzero (by simpa [rejected, DependentFamily.realize] using ht)

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@dyadic_path_orbit_classification), rejected, rejected_law⟩
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
    refine ⟨(), (1 / 2 : ℝ), (0 : ℝ), ?_⟩
    change realFlow (1 / 2 : ℝ) ≠ realFlow 0
    simpa only [map_zero] using half_nonzero

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@dyadic_path_orbit_classification) (DependentFamily.Realization signature) Unit Unit where
  unitName := `D5.S1.Solenoid.DyadicSolenoid.dyadic_path_orbit_classification.__information_unit
  realizationName := `Reg.D5.S1.Solenoid.DyadicPathComponent.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature (fun _ _ t => realFlow t)
    (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Solenoid.DyadicPathComponent
