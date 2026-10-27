import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration

/-! Typed whole-family evidence retains the original periodic-word predicate.
Raw selection through the cardinality subtype
remains an explicit unresolved slot. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev wordScope := type_of% (@periodic_word_card_eq_trace)

abbrev wordSignature : Signature where
  Params := ℕ
  State N := Fin N → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature
    (fun _ _ labels => AndrasfaiLanguage.PeriodicAvoidance (List.ofFn labels))
    (fun e => nomatch e)

abbrev wordArena : Arena where
  signature := wordSignature
  Law r := ∀ N : ℕ, 0 < N → N % 3 ≠ 0 →
    (Nat.card {labels : Fin N → Bool // r.readout () N labels} : ℚ) =
      Matrix.trace (AndrasfaiTransfer.transfer ^ N)

theorem word_source_bridge : wordScope ↔ wordArena.Law wordActual := by
  dsimp only [wordScope, wordArena, wordActual, realize]
  simp only [← Nat.card_eq_fintype_card]

theorem word_actual_positive : wordArena.Law wordActual :=
  word_source_bridge.mp periodic_word_card_eq_trace

def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => False) (fun e => nomatch e)

theorem word_rejected_law : ¬ wordArena.Law wordRejected := by
  intro h
  have he := h 1 (by decide) (by decide)
  have hc : Nat.card {labels : Fin 1 → Bool // False} = 0 := by simp
  change (Nat.card {labels : Fin 1 → Bool // False} : ℚ) = _ at he
  rw [hc] at he
  have ht : Matrix.trace (AndrasfaiTransfer.transfer ^ 1) = (1 : ℚ) := by decide +kernel
  rw [ht] at he
  norm_num at he

theorem word_dependence : ObservationalDependence wordSignature wordActual := by
  intro role
  cases role
  refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
  change AndrasfaiLanguage.PeriodicAvoidance (List.ofFn (fun _ : Fin 1 => false)) ≠
    AndrasfaiLanguage.PeriodicAvoidance (List.ofFn (fun _ : Fin 1 => true))
  have hg : AndrasfaiLanguage.PeriodicAvoidance [false] := by
    apply (AndrasfaiLanguage.exists_unique_closed_run [false] (by decide)).mpr
    refine ⟨0, ⟨by decide, by decide +kernel⟩, ?_⟩
    intro q hq
    exact AndrasfaiLanguage.closed_run_unique [false] (by decide) q 0
      hq.1 (by decide) hq.2 (by decide +kernel)
  have hb : ¬ AndrasfaiLanguage.PeriodicAvoidance [true] := by
    intro hp
    obtain ⟨q, hq, _⟩ :=
      (AndrasfaiLanguage.exists_unique_closed_run [true] (by decide)).mp hp
    fin_cases q <;> revert hq <;> decide +kernel
  simpa using (show AndrasfaiLanguage.PeriodicAvoidance [false] ≠
    AndrasfaiLanguage.PeriodicAvoidance [true] from fun he => hb (he ▸ hg))

def wordFamily : Registration wordArena wordScope where
  actual := wordActual
  bridge := word_source_bridge
  variation := ⟨word_actual_positive, wordRejected, word_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected, ?_, rfl, word_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := word_dependence

def word_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@periodic_word_card_eq_trace)
    (type_of% (realize wordSignature
      (fun _ _ labels => AndrasfaiLanguage.PeriodicAvoidance (List.ofFn labels))
      (fun e => nomatch e))) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration.periodic_word_card_eq_trace
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration.wordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨wordArena⟩
  objectArena := .source ⟨wordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wordArena ⟨wordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature
    (fun _ _ labels => AndrasfaiLanguage.PeriodicAvoidance (List.ofFn labels))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration
