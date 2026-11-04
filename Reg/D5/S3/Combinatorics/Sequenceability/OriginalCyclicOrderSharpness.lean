import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Index Coordinate q p a b full triple)
open _root_.D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering (MinimalZeroSupport)
open _root_.D5.S3.Combinatorics.Sequenceability.BooleanRowChargeConnectivity (supportIntersectionGraph)
open scoped Classical BigOperators

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ _ m => addOrderOf (label m (q m))) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (_hm : 2 ≤ m),
    Finite (WitnessGroup m) ∧
    IsAddCyclic (WitnessGroup m) ∧
    Function.Injective (label m) ∧
    (∀ x : Coordinate m, label m x ≠ 0) ∧
    q m ∈ full m ∧
    R.readout () () m = m ∧
    (∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
        ∃ j : Index m, C = triple m j) ∧
    (∀ B : Finset (Coordinate m),
      B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B) ∧
    (supports m).card = m - 1 ∧
    (∀ B ∈ supports m, q m ∈ B) ∧
    (∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m))) ∧
    (((Finset.univ : Finset (supports m)).filter (fun B => q m ∈ B.val)).image
      (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card = m - 1

abbrev sourceScope := type_of% (@sharpness)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem actual_positive : arena.Law actual := sharpness

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 2 (by decide)).2.2.2.2.2.1
  change (0 : ℕ) = 2 at he
  omega

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  have htwo := (sharpness 2 (by decide)).2.2.2.2.2.1
  have hthree := (sharpness 3 (by decide)).2.2.2.2.2.1
  change addOrderOf (label 2 (q 2)) ≠ addOrderOf (label 3 (q 3))
  rw [htwo, hthree]
  decide

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@sharpness) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness.sharpness.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness.familyRegistration
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
    (fun _ _ m => addOrderOf (label m (q m))) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalCyclicOrderSharpness
