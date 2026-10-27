import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Solenoid.SingularHomology
import Reg.Support.DependentFamily

/-! # Source-bound audits for source lifting and positive singular homology -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S1.Solenoid.SingularHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open _root_.D5.S1.Dynamics
open _root_.D5.S1.Solenoid.SingularHomology
open _root_.D5.S1.Solenoid.RealFlowInjectivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ModuleCat.{0} ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev homologyObject (n : ℕ) : ModuleCat.{0} ℤ :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of UniversalSolenoid))

abbrev actual : Realization signature :=
  realize signature (fun _ _ X => IsZero X) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (n : ℕ), n ≠ 0 → obs.readout () n (homologyObject n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by decide)

def evidence : Registration arena
    (∀ (n : ℕ) (_ : n ≠ 0), IsZero (homologyObject n)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨singular_homology_positive_is_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, ModuleCat.of ℤ PUnit, ModuleCat.of ℤ ℤ, ?_⟩
    change IsZero (ModuleCat.of ℤ PUnit) ≠ IsZero (ModuleCat.of ℤ ℤ)
    intro h
    have hz : IsZero (ModuleCat.of ℤ ℤ) := h ▸ ModuleCat.isZero_of_subsingleton _
    letI : Subsingleton ℤ := (ModuleCat.isZero_iff_subsingleton).mp hz
    exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

def homology_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S1.Solenoid.SingularHomology.singular_homology_positive_is_zero)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Solenoid.SingularHomology.homology_unit
  realizationName := `Reg.D5.S1.Solenoid.SingularHomology.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => IsZero X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Solenoid.SingularHomology
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe u

abbrev liftSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := UniversalSolenoid
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev liftActual : Realization liftSignature :=
  realize liftSignature (fun _ _ t => UniversalSolenoid.realFlow t) (fun e => nomatch e)

abbrev liftRejected : Realization liftSignature :=
  realize liftSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev liftArena : Arena where
  signature := liftSignature
  Law obs := ∀ {A : Type u} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] (f : C(A, UniversalSolenoid)) (a₀ : A),
    ∃! r : C(A, ℝ), r a₀ = 0 ∧ ∀ a, f a = obs.readout () () (r a) + f a₀

private theorem lift_rejected_law : ¬ liftArena.{u}.Law liftRejected := by
  intro h
  letI : ContractibleSpace (ULift.{u} ℝ) :=
    (Homeomorph.ulift : ULift.{u} ℝ ≃ₜ ℝ).contractibleSpace_iff.mpr inferInstance
  letI : LocallyPathConnectedSpace (ULift.{u} ℝ) :=
    (Homeomorph.ulift : ULift.{u} ℝ ≃ₜ ℝ).symm.locallyPathConnectedSpace
  let f : C(ULift.{u} ℝ, UniversalSolenoid) :=
    ⟨fun a => UniversalSolenoid.realFlow a.down,
      UniversalSolenoid.continuous_realFlow.comp continuous_uliftDown⟩
  obtain ⟨r, hr, _⟩ := h f ⟨0⟩
  have he := hr.2 ⟨1⟩
  change UniversalSolenoid.realFlow 1 = 0 + UniversalSolenoid.realFlow 0 at he
  have bad := realFlow_injective (by simpa using he)
  norm_num at bad

def liftEvidence : Registration liftArena.{u} (liftArena.Law liftActual) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨exists_unique_normalized_lift, liftRejected, lift_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftRejected, ?_, rfl, lift_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    exact fun h => zero_ne_one (realFlow_injective h)

def lift_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S1.Solenoid.SingularHomology.exists_unique_normalized_lift.{u})
    (Realization liftSignature) Unit Unit where
  unitName := `Reg.D5.S1.Solenoid.SingularHomology.lift_unit
  realizationName := `Reg.D5.S1.Solenoid.SingularHomology.liftEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena.{u}⟩
  objectArena := .source ⟨liftArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena.{u} ⟨liftEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature (fun _ _ t => UniversalSolenoid.realFlow t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Solenoid.SingularHomology
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Solenoid.SingularHomology
