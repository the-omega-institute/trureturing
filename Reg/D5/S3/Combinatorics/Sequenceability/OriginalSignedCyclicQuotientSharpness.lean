import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Coordinate q triple)
open scoped Classical BigOperators

abbrev signature : DependentFamily.Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ k s => modulus s * (4 * modulus s - 6 + 2 * k)) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (k s : ℕ) (hs : 1 ≤ s),
    Finite (WitnessGroup s k) ∧
    Nat.card (WitnessGroup s k) = R.readout () k s ∧
    addOrderOf (label s k (q (modulus s))) = modulus s ∧
    ((modulus s).Coprime (quotientModulus s k) → IsAddCyclic (WitnessGroup s k)) ∧
    (∀ C : Finset (Coordinate (modulus s)),
      (C.Nonempty ∧ (∑ x ∈ C, label s k x) = 0) ↔
        ∃ i : PairIndex s, C = triple (modulus s) i)

abbrev sourceScope := type_of% (@sharpness)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem actual_positive : arena.Law actual := sharpness

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 0 1 (by decide)).2.1
  change Nat.card (WitnessGroup 1 0) = 0 at he
  have hcard := (sharpness 0 1 (by decide)).2.1
  rw [hcard] at he
  norm_num [modulus] at he

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 1, 2, ?_⟩
  change modulus 1 * (4 * modulus 1 - 6) ≠ modulus 2 * (4 * modulus 2 - 6)
  norm_num [modulus]

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
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness.sharpness.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence
    ⟨(show Nonempty (DependentFamily.Realization signature) from ⟨actual⟩)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ k s => modulus s * (4 * modulus s - 6 + 2 * k)) (fun e => nomatch e))
  variation := .evidence ⟨familyRegistration.variation⟩ trivial
  sensitivity := .evidence ⟨familyRegistration.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness
    definition := none
    coordinates := #[0]
    readouts := #[{
      -- Full k,s,hs telescope; second conjunction; cardinal equality right side.
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalSignedCyclicQuotientSharpness
