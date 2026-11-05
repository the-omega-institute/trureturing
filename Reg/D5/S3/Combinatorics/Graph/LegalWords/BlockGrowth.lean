import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Classical Topology
open Set Filter
open D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
open D5.S3.Combinatorics.Graph.LegalWordDegree
open D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => decide (x = 0)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

local notation "K" => (fun n : ℕ => kappa (legalWordGraph n))

/-- The scalar zero observation varies; every other original clause is retained. -/
abbrev growthArena : Arena where
  signature := signature
  Law R := R.readout () () (K 0) = true ∧
    (∀ n m, K (n+m) ≤ K n + K m ∧ K n + K m ≤ K (n+m+1)) ∧
    ∃ c : ℝ, Tendsto (fun n => K n / (n:ℝ)) atTop (𝓝 c) ∧
      c = sInf ((fun n : ℕ => K n / (n:ℝ)) '' Ici 1) ∧
      c = sSup (range (fun n : ℕ => K n / ((n:ℝ)+1))) ∧
      ∀ n : ℕ, c * n ≤ K n ∧ K n ≤ c * ((n:ℝ)+1)

def growthFamily : Registration growthArena (type_of% growth_constant) := by
  have bridge : (type_of% growth_constant) ↔ growthArena.Law actual := by
    simp only [growthArena, actual, realize, decide_eq_true_eq]
  have hp : growthArena.Law actual := bridge.mp growth_constant
  have hn : ¬growthArena.Law rejected := by
    intro h
    have he : false = true := h.1
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
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def growthAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@growth_constant) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth.growthUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth.growthFamily
  realizationSource := none
  generated := false
  arena := .source ⟨growthArena⟩
  objectArena := .source ⟨growthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source growthArena ⟨growthFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms growthFamily
#print axioms growthAudit

end Reg.D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth
