import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HereditaryFlip.Majority

/-! # Source-bound small-face and completion observations -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Majority

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

def flagSignature : Signature where
  Params := Type u
  State V := Set (Finset V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def flagActual : Realization flagSignature :=
  realize flagSignature (fun _ _ K => Flag K) (fun e => nomatch e)

def flagRejected : Realization flagSignature :=
  realize flagSignature (fun _ _ _ => False) (fun e => nomatch e)

def flagArena : Arena where
  signature := flagSignature
  Law R := ∀ (V : Type u) (inst : DecidableEq V) (K : Set (Finset V)),
    IsLowerSet K → (@MajorityClosed V inst K ↔ R.readout () V K)

private theorem flagRejected_law : ¬ flagArena.Law flagRejected := by
  intro h
  have ht := h (ULift.{u} Unit) inferInstance Set.univ (fun _ _ _ _ => trivial)
  exact ht.mp (by intro A hA B hB C hC; trivial)

private theorem triangle_not_flag :
    ¬ Flag {S : Finset (ULift.{u} (Fin 3)) | S.card ≤ 2} := by
  intro h
  have ht := h {⟨0⟩, ⟨1⟩, ⟨2⟩} (fun _ _ hc => hc)
  have hc : ({⟨0⟩, ⟨1⟩, ⟨2⟩} : Finset (ULift.{u} (Fin 3))).card = 3 := by decide
  change _ ≤ 2 at ht
  omega

def flagFamily : Registration flagArena (type_of% (@majority_closed_iff_flag.{u})) where
  actual := flagActual
  bridge := Iff.rfl
  variation := ⟨@majority_closed_iff_flag.{u}, flagRejected, flagRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨flagRejected, ?_, rfl, flagRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} (Fin 3), Set.univ, {S | S.card ≤ 2}, ?_⟩
    intro h
    have ht : Flag (Set.univ : Set (Finset (ULift.{u} (Fin 3)))) := by
      intro S hS; trivial
    exact triangle_not_flag (Eq.mp h ht)

def closureSignature : Signature where
  Params := Type u
  State V := Set (Finset V)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Set (Finset V)
  Anchor := Empty
  finiteAnchor := inferInstance

def closureActual : Realization closureSignature :=
  realize closureSignature (fun _ _ K => pairClosure K) (fun e => nomatch e)

def closureRejected : Realization closureSignature :=
  realize closureSignature (fun _ _ _ => ∅) (fun e => nomatch e)

def closureArena : Arena where
  signature := closureSignature
  Law R := ∀ (V : Type u) (inst : DecidableEq V) (K : Set (Finset V)),
    IsLowerSet K → IsLeast {L : Set (Finset V) | K ⊆ L ∧ @MajorityClosed V inst L}
      (R.readout () V K)

private theorem closureRejected_law : ¬ closureArena.Law closureRejected := by
  intro h
  have ht := h (ULift.{u} Unit) inferInstance Set.univ (fun _ _ _ _ => trivial)
  exact ht.1.1 (show (∅ : Finset (ULift.{u} Unit)) ∈ Set.univ from trivial)

def closureFamily : Registration closureArena (type_of% (@pair_closure_is_least.{u})) where
  actual := closureActual
  bridge := Iff.rfl
  variation := ⟨@pair_closure_is_least.{u}, closureRejected, closureRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨closureRejected, ?_, rfl, closureRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, Set.univ, ∅, ?_⟩
    intro h
    have ht : (∅ : Finset (ULift.{u} Unit)) ∈ pairClosure Set.univ := by
      intro T hT hcard; trivial
    have he : (∅ : Finset (ULift.{u} Unit)) ∈ pairClosure ∅ := Eq.mp
      (congrArg (fun F : Set (Finset (ULift.{u} Unit)) => ∅ ∈ F) h) ht
    exact he ∅ Finset.Subset.rfl (by simp)

noncomputable def flagRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@majority_closed_iff_flag.{u}) (Realization flagSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Majority.majority_closed_iff_flag.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Majority.flagFamily
  realizationSource := none
  generated := false
  arena := .source ⟨flagArena⟩
  objectArena := .source ⟨flagArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source flagArena ⟨flagFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize flagSignature
    (fun _ _ K => Flag K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def closureRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@pair_closure_is_least.{u}) (Realization closureSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Majority.pair_closure_is_least.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Majority.closureFamily
  realizationSource := none
  generated := false
  arena := .source ⟨closureArena⟩
  objectArena := .source ⟨closureArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closureArena ⟨closureFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize closureSignature
    (fun _ _ K => pairClosure K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Majority
