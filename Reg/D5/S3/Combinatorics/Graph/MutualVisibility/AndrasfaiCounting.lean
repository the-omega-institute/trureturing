import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting

/-! The readout records actual original-DFA evaluation on every labelled word
and starting state, with a law equating the closed-fiber cardinality to the trace. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting

open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev countScope := type_of% (@closed_run_card_eq_trace)

abbrev countSignature : Signature where
  Params := ℕ
  State N := (Fin N → Bool) × Fin 4
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 5
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature :=
  realize countSignature
    (fun _ _ p => AndrasfaiLanguage.machine.evalFrom (liveState p.2) (List.ofFn p.1))
    (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law r := ∀ N : ℕ, 0 < N →
    (Fintype.card {p : (Fin N → Bool) × Fin 4 //
      r.readout () N p = liveState p.2} : ℚ) =
        Matrix.trace (AndrasfaiTransfer.transfer ^ N)

theorem count_source_bridge : countScope ↔ countArena.Law countActual := by
  dsimp only [countScope, countArena, countActual, realize]
  simp only [← Nat.card_eq_fintype_card]
  rfl

theorem count_actual_positive : countArena.Law countActual :=
  count_source_bridge.mp closed_run_card_eq_trace

def countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem count_rejected_law : ¬ countArena.Law countRejected := by
  intro h
  have he := h 1 (by decide)
  have hn : (Fintype.card {p : (Fin 1 → Bool) × Fin 4 //
      (0 : Fin 5) = liveState p.2} : ℚ) ≠
        Matrix.trace (AndrasfaiTransfer.transfer ^ 1) := by
    decide +kernel
  exact hn he

theorem count_dependence : ObservationalDependence countSignature countActual := by
  intro role
  refine ⟨1, (fun _ => false, 0), (fun _ => true, 0), ?_⟩
  cases role
  decide +kernel

def countFamily : Registration countArena countScope where
  actual := countActual
  bridge := count_source_bridge
  variation := ⟨count_actual_positive, countRejected, count_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, count_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := count_dependence

/-- The typed family proof is supplied; raw reconstruction through the cardinality
subtype still needs a supported source-selection certificate. -/
def count_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@closed_run_card_eq_trace)
    (type_of% (realize countSignature
      (fun _ _ p => AndrasfaiLanguage.machine.evalFrom (liveState p.2) (List.ofFn p.1))
      (fun e => nomatch e))) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting.closed_run_card_eq_trace
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature
    (fun _ _ p => AndrasfaiLanguage.machine.evalFrom (liveState p.2) (List.ofFn p.1))
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

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting
