import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.BiasedMassFrontier
import Reg.Support.DependentFamily

open _root_.D5.S0.Computability.Coding.BiasedMassFrontier
open _root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open _root_.D5.S0.Computability.Coding.PrefixFreeCode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S0.Computability.Coding.BiasedMassFrontier

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := Finset (List Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p A => ∑ w ∈ A, wordMass (letterMass p.1 p.2) w) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

/-- All clauses remain in the law; only its total mass observation varies. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b t : ℝ) (_hb : 0 < b) (_hba : b ≤ a)
    (_ha : a < 1) (_hab : a + b = 1) (_ht : 0 < t) (_htone : t < 1),
    ∃ (N : ℕ) (A : Finset (List Bool)),
      (A : Set (List Bool)) = Crossing a b t ∧
      (∀ w ∈ A, w.length ≤ N) ∧
      IsPrefixFree (A : Set (List Bool)) ∧
      (∀ ω : ℕ → Bool, ∃! w, w ∈ A ∧ w = rayPrefix ω w.length) ∧
      R.readout () ⟨a, b⟩ A = 1 ∧
      (∀ w ∈ A, b * t < wordMass (letterMass a b) w ∧
        wordMass (letterMass a b) w ≤ t) ∧
      1 / t ≤ (A.card : ℝ) ∧ (A.card : ℝ) < 1 / (b * t)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨N, A, _, _, _, _, hm, _⟩ := h (1/2) (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change (0 : ℝ) = 1 at hm
  norm_num at hm

def sourceEvidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨biased_first_mass_frontier, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1/2, 1/2⟩, ∅, {[]}, ?_⟩
    simp [actual, realize, wordMass]

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0} biased_first_mass_frontier
    (Realization signature) Unit Unit where
  unitName := `D5.S0.Computability.Coding.BiasedMassFrontier.biased_first_mass_frontier.__information_unit
  realizationName := `Reg.D5.S0.Computability.Coding.BiasedMassFrontier.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p A => ∑ w ∈ A, wordMass (letterMass p.1 p.2) w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.Coding.BiasedMassFrontier
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceEvidence

end
end Reg.D5.S0.Computability.Coding.BiasedMassFrontier
