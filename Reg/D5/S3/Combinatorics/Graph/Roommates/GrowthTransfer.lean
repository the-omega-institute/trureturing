import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer

/-- The readout carries the actual real probability operand. -/
abbrev probabilitySignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- An application of the enrolled dependent-family realization template. -/
def actual : Realization probabilitySignature :=
  realize probabilitySignature (fun _ _ x => x) (fun e => nomatch e)

/-- The original three count premises and complete source conclusion. -/
abbrev transferArena : Arena where
  signature := probabilitySignature
  Law R :=
    (∀ m k : ℕ, 0 < m → 0 < k →
      OpenCertificates.count m * OpenCertificates.count k ≤ OpenCertificates.count (m + k + 6)) →
    (∀ m : ℕ, 0 < m → OpenCertificates.count m ≤
      Fintype.card {p : SourceModel.Profile (m + 1) // SourceModel.HasStableMatching p}) →
    OpenCertificates.count 3 < 24 ^ 3 →
    ∃ q c C : ℝ, 0 < q ∧ q < 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
        c * q ^ (n + 5) ≤ R.readout () () (SourceModel.solutionProbability n) ∧
        R.readout () () (SourceModel.solutionProbability n) ≤ C * q ^ (n + 5)

/-- Exact reconstruction of the source telescope; no count premise is omitted. -/
def sourceBridge : (type_of% _root_.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.same_q_probability_of_counts) ↔
    transferArena.Law actual := Iff.rfl

/-- The actual readout observes its real operand. -/
def dependence : ObservationalDependence probabilitySignature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

/-- A negative output cannot satisfy a positive lower probability bound. -/
def rejected : Realization probabilitySignature :=
  realize probabilitySignature (fun _ _ _ => -1) (fun e => nomatch e)

/-- The complete unconditional source conclusion with its actual probability operand. -/
abbrev resultArena : Arena where
  signature := probabilitySignature
  Law R := ∃ q c C : ℝ, 0 < q ∧ q < 1 ∧ 0 < c ∧ 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      c * q ^ (n + 5) ≤ R.readout () () (SourceModel.solutionProbability n) ∧
      R.readout () () (SourceModel.solutionProbability n) ≤ C * q ^ (n + 5)

/-- Exact source reconstruction, law variation, role sensitivity and operand dependence. -/
def resultFamily : Registration resultArena
    (type_of% _root_.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.result) := by
  have bridge : (type_of% _root_.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.result) ↔
      resultArena.Law actual := Iff.rfl
  have hp := bridge.mp _root_.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.result
  have hn : ¬resultArena.Law rejected := by
    rintro ⟨q, c, C, hq, _, hc, _, hb⟩
    have hl := (hb 2 (by omega)).1
    have hpos : 0 < c * q ^ (2 + 5) := mul_pos hc (pow_pos hq _)
    change c * q ^ (2 + 5) ≤ -1 at hl
    linarith
  refine {
    actual := actual
    bridge := bridge
    variation := ⟨hp, rejected, hn⟩
    sensitivity := ?_
    dependence := dependence }
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, hn⟩
    intro j hj
    exact (hj (Subsingleton.elim _ _)).elim
  · intro i
    exact nomatch i

/-- Typed enrolled-template evidence; raw source selection remains absent (issue 29645). -/
def resultAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.result)
    (Realization probabilitySignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.resultUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer.resultFamily
  realizationSource := none
  generated := false
  arena := .source ⟨resultArena⟩
  objectArena := .source ⟨resultArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resultArena ⟨resultFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize probabilitySignature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms resultFamily
#print axioms resultAudit

#print axioms sourceBridge
#print axioms dependence

end Reg.D5.S3.Combinatorics.Graph.Roommates.GrowthTransfer
