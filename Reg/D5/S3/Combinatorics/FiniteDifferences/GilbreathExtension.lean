import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => List ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Set ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ s => validExtensions s) (fun e => nomatch e)

def geometry (X : Set ℤ) : Prop :=
  X.Finite ∧ oneParity X ∧ (maximalStepTwoRuns X).Finite

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ n : ℕ, 5 ≤ n →
    (∀ s : List ℤ, admissible n s →
      geometry (R.readout () () s) ∧ stepTwoRunCount (R.readout () () s) ≤ 2^(n-4)) ∧
    (∃ s : List ℤ, admissible n s ∧ geometry (R.readout () () s) ∧
      stepTwoRunCount (R.readout () () s) = 2^(n-4))

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (∅ : Set ℤ)) (fun e => nomatch e)

theorem empty_run_count : stepTwoRunCount ∅ = 0 := by
  have he : maximalStepTwoRuns ∅ = ∅ := by
    ext ab
    simp only [maximalStepTwoRuns, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hle,hpar,hseg,_,_⟩
    exact hseg ab.1 (le_refl _) hle (by simp)
  simp [stepTwoRunCount,he]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s,_,_,hc⟩ := (h 5 (by omega)).2
  change stepTwoRunCount ∅ = 2^(5-4) at hc
  rw [empty_run_count] at hc
  norm_num at hc

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),[],[0],?_⟩
    intro he
    change validExtensions [] = validExtensions [0] at he
    have hz : (0:ℤ) ∈ validExtensions [] := by
      intro r hr hrl
      simp only [List.nil_append,List.length_singleton] at hrl
      omega
    rw [he] at hz
    have hh := hz 1 (by omega) (by simp)
    norm_num [row,difference] at hh

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension.familyRegistration
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
    (fun _ _ s => validExtensions s) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (List ℤ)
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension
    definition := some {
      owner := `D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension
      name := `D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension.componentMaximum
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Combinatorics.FiniteDifferences.GilbreathExtension
