import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Roommates.CyclicBridge

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates
open D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
open D5.S3.Combinatorics.Graph.Roommates.CyclicBridge
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicBridge

abbrev comparisonSignature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ x => decide (x.1 ≤ x.2)) (fun e => nomatch e)
def rejected : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ _ => false) (fun e => nomatch e)

/-- The full original telescope and its exact two arithmetic operands. -/
abbrev cutArena : Arena where
  signature := comparisonSignature
  Law R := ∀ n : ℕ, R.readout () ()
    (Fintype.card {p : SourceModel.Profile n // SourceModel.HasStableMatching p}, count (n + 5)) = true

/-- Typed reconstruction, whole-family variation, sensitivity and real observational dependence. -/
def cutFamily : Registration cutArena (type_of% source_count_le_open_count) := by
  have bridge : (type_of% source_count_le_open_count) ↔ cutArena.Law actual := by
    simp only [cutArena, actual, realize, decide_eq_true_eq]
  have hp : cutArena.Law actual := bridge.mp source_count_le_open_count
  have hn : ¬cutArena.Law rejected := by
    intro h
    have he : false = true := h 0
    cases he
  refine {
    actual := actual
    bridge := bridge
    variation := ⟨hp, rejected, hn⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  · intro i
    exact ⟨(), (0, 0), (1, 0), by norm_num [actual, realize]⟩

/-- Typed source-count comparison. Native source-selection binding is absent;
this declaration alone supplies no declared_validated status.
The public coordinate/rank helpers wrap_val, wrap_index, wrap_add, wrap_signed,
signed_bounds and rank_wrap have no completed native source bindings here;
the unfinished audit is tracked by trureturing issue 29645. -/
def cutAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@source_count_le_open_count) (Realization comparisonSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicBridge.cutUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicBridge.cutFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cutArena⟩
  objectArena := .source ⟨cutArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cutArena ⟨cutFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize comparisonSignature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cutFamily
#print axioms cutAudit
end Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicBridge
