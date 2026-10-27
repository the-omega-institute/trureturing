import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness
open _root_.D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
  (Coordinate q triple)
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
    (fun _ _ s => modulus s * 2 ^ (dimension s + 1)) (fun e => nomatch e)

abbrev arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (s : ℕ) (hs : 1 ≤ s),
    Finite (WitnessGroup s) ∧
    Nat.card (WitnessGroup s) = R.readout () () s ∧
    Nat.card (WitnessGroup s) < 4 * modulus s * (modulus s - 1) ∧
    addOrderOf (label s hs (q (modulus s))) = modulus s ∧
    ¬ Function.Injective (label s hs) ∧
    (∀ C : Finset (Coordinate (modulus s)),
      (C.Nonempty ∧ (∑ x ∈ C, label s hs x) = 0) ↔
        ∃ i : PairIndex s, C = triple (modulus s) i)

abbrev sourceScope := type_of% (@sharpness)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem actual_positive : arena.Law actual := sharpness

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 (by decide)).2.1
  change Nat.card (WitnessGroup 1) = 0 at he
  have hcard := (sharpness 1 (by decide)).2.1
  rw [hcard] at he
  change (12 : ℕ) = 0 at he
  omega

private theorem dependence : DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change (12 : ℕ) ≠ 40
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
  unitName := `D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness.sharpness.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness.familyRegistration
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
    (fun _ _ s => modulus s * 2 ^ (dimension s + 1)) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Syntax candidate: s,hs bodies; first And.right; next And.left; Eq.rhs.
      -- This source-only path still requires the actual inspector to match it.
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness
