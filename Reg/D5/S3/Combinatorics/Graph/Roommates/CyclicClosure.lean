import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Roommates.CyclicClosure

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
open D5.S3.Combinatorics.Graph.Roommates
open D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicClosure

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
abbrev closureCountArena : Arena where
  signature := comparisonSignature
  Law R := ∀ n : ℕ, R.readout () ()
    (count n, Fintype.card {p : SourceModel.Profile (n+1) // SourceModel.HasStableMatching p}) = true

/-- Typed reconstruction, whole-family variation, sensitivity and real observational dependence. -/
def closureCountFamily : Registration closureCountArena (type_of% count_le_successful_profile_count) := by
  have bridge : (type_of% count_le_successful_profile_count) ↔ closureCountArena.Law actual := by
    simp only [closureCountArena, actual, realize, decide_eq_true_eq]
  have hp : closureCountArena.Law actual := bridge.mp count_le_successful_profile_count
  have hn : ¬closureCountArena.Law rejected := by
    intro h
    have he : false = true := h 0
    cases he
  refine { actual := actual, bridge := bridge, variation := ⟨hp, rejected, hn⟩,
    sensitivity := ?_, dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  · intro i
    exact ⟨(), (0, 0), (1, 0), by norm_num [actual, realize]⟩

/-- Typed closure-count comparison. Native source-selection binding is absent;
this declaration alone supplies no declared_validated status. -/
def closureCountAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@count_le_successful_profile_count) (Realization comparisonSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicClosure.closureCountUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicClosure.closureCountFamily
  realizationSource := none
  generated := false
  arena := .source ⟨closureCountArena⟩
  objectArena := .source ⟨closureCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closureCountArena ⟨closureCountFamily⟩
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

#print axioms closureCountFamily
#print axioms closureCountAudit
end Reg.D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
