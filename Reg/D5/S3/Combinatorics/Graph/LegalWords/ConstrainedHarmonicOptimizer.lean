import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer

open scoped BigOperators Classical
open _root_.D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open _root_.D5.S3.Combinatorics.Graph.LegalWordDegree
open _root_.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private def oneLower : Legal 1 := ⟨fun _ => false, by decide⟩
private def oneUpper : Legal 1 := ⟨fun _ => true, by decide⟩

private def oneEquiv : Legal 1 ≃ Bool where
  toFun b := b.val 0
  invFun s := ⟨fun _ => s, by cases s <;> decide⟩
  left_inv b := by
    apply Subtype.ext
    funext i
    rw [Fin.eq_zero i]
  right_inv s := rfl

private theorem one_sum (p : Legal 1 → ℝ) : ∑ b, p b = p oneLower + p oneUpper := by
  have h := Equiv.sum_comp oneEquiv.symm p
  simpa [oneEquiv, oneLower, oneUpper, add_comm] using h.symm

private theorem one_erase : erase oneUpper 0 = oneLower := by
  apply Subtype.ext
  funext i
  simp [erase, oneLower, Fin.eq_zero i]

private theorem one_q : insertionLower (0 : Fin 1) = 1 := by
  have he : Finset.univ.filter (Near (0 : Fin 1)) = ∅ := by
    ext i
    rw [Fin.eq_zero i]
    simp [Near]
  unfold insertionLower positionDegree
  rw [he]
  norm_num

private theorem one_cases (b : Legal 1) : b = oneLower ∨ b = oneUpper := by
  cases h : b.val 0 with
  | false =>
    left; apply Subtype.ext; funext i
    simpa [oneLower, Fin.eq_zero i] using h
  | true =>
    right; apply Subtype.ext; funext i
    simpa [oneUpper, Fin.eq_zero i] using h

private theorem one_adj : (legalWordGraph 1).Adj oneLower oneUpper := by
  change (Finset.univ.filter (fun i => oneLower.val i ≠ oneUpper.val i)).card = 1
  simp [oneLower, oneUpper]

private theorem one_distinct : oneUpper ≠ oneLower := by
  intro h
  have hv := congrArg (fun b : Legal 1 => b.val 0) h
  norm_num [oneUpper, oneLower] at hv

private theorem one_edges : (legalWordGraph 1).edgeFinset = {s(oneLower, oneUpper)} := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  rcases one_cases a with rfl | rfl <;> rcases one_cases b with rfl | rfl <;>
    simp [SimpleGraph.mem_edgeFinset, one_adj, one_adj.symm,
      Sym2.eq_iff, one_distinct, one_distinct.symm]

private theorem one_objective (p : Legal 1 → ℝ) :
    objective 1 p = _root_.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer.harmonic (p oneLower) (p oneUpper) := by
  simp [objective, one_edges]

abbrev signature : Signature where
  Params := ℕ
  State n := Legal n → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n p => objective n p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n p => ∑ b : Legal n, if ∀ i, b.val i = true then p b else 0)
    (fun e => nomatch e)

private theorem rejected_one (p : Legal 1 → ℝ) : rejected.readout () 1 p = p oneUpper := by
  change (∑ b : Legal 1, if ∀ i, b.val i = true then p b else 0) = p oneUpper
  rw [one_sum]
  simp [oneLower, oneUpper]

abbrev maximumArena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 1 ≤ n) (ε : ℝ) (_hε : 0 < ε)
    (_hsmall : ε ≤ 1 / (Fintype.card (Legal n) : ℝ)),
    ∃ p : Legal n → ℝ, p ∈ epsilonSimplex n ε ∧
      IsMaxOn (R.readout () n) (epsilonSimplex n ε) p ∧ InsertionBounds n p

private def testVector : Legal 1 → ℝ := fun b => if b.val 0 = true then 3 / 4 else 1 / 4

private theorem test_feasible : testVector ∈ epsilonSimplex 1 (1 / 4) := by
  constructor
  · intro b; unfold testVector; split_ifs <;> norm_num
  · rw [one_sum]; norm_num [testVector, oneLower, oneUpper]

private theorem maximum_rejected : ¬maximumArena.Law rejected := by
  intro h
  have hc : Fintype.card (Legal 1) = 2 := by
    rw [Fintype.card_congr oneEquiv]; rfl
  obtain ⟨p, hp, hmax, hb⟩ := h 1 (by omega) (1 / 4) (by norm_num) (by norm_num [hc])
  let e : Marked 1 := ⟨oneUpper, ⟨0, rfl⟩⟩
  have he := hb e
  change insertionLower (0 : Fin 1) * p (erase oneUpper 0) ≤ p oneUpper ∧
    p oneUpper ≤ p (erase oneUpper 0) at he
  rw [one_q, one_erase, one_mul] at he
  have hsum := hp.2
  rw [one_sum] at hsum
  have hm := hmax test_feasible
  simp only [rejected_one] at hm
  norm_num [testVector, oneUpper] at hm
  change (3 / 4 : ℝ) ≤ p oneUpper at hm
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, (fun _ => 1 / 2), (fun b => if b.val 0 = true then 1 else 0), ?_⟩
  change objective 1 _ ≠ objective 1 _
  rw [one_objective, one_objective]
  norm_num [_root_.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer.harmonic, oneLower, oneUpper]

def maximumFamily : Registration maximumArena
    (type_of% (@exists_constrained_optimizer_with_insertion_bounds)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_constrained_optimizer_with_insertion_bounds, rejected, maximum_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, maximum_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Source binding selects the original objective function occurrence inside IsMaxOn. -/
def maximumAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@exists_constrained_optimizer_with_insertion_bounds) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer.maximumUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer.maximumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨maximumArena⟩
  objectArena := .source ⟨maximumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source maximumArena ⟨maximumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms maximumFamily
#print axioms maximumAudit

abbrev exchangeArena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_hn : 1 ≤ n) (ε : ℝ) (_hε : 0 < ε)
      (p : Legal n → ℝ) (_hp : p ∈ epsilonSimplex n ε) (_hbad : ¬InsertionBounds n p),
    ∃ donor receiver : Legal n,
      (legalWordGraph n).Adj donor receiver ∧ p receiver < p donor ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < p donor - ε ∧
        ∀ u : ℝ, 0 < u → u < δ →
          transfer p donor receiver u ∈ epsilonSimplex n ε ∧
          R.readout () n p < R.readout () n (transfer p donor receiver u)

private theorem exchange_rejected : ¬exchangeArena.Law rejected := by
  intro h
  have hb : ¬InsertionBounds 1 testVector := by
    intro hb
    let e : Marked 1 := ⟨oneUpper, ⟨0, rfl⟩⟩
    have hh := (hb e).2
    change testVector oneUpper ≤ testVector (erase oneUpper 0) at hh
    rw [one_erase] at hh
    norm_num [testVector, oneUpper, oneLower] at hh
  obtain ⟨donor, receiver, _, ho, δ, hδ, _, hall⟩ :=
    h 1 (by omega) (1 / 4) (by norm_num) testVector test_feasible hb
  have hdonor : donor = oneUpper := by
    rcases one_cases donor with h | h
    · rw [h] at ho
      have hp := test_feasible.1 receiver
      have hv : testVector oneLower = 1 / 4 := by norm_num [testVector, oneLower]
      rw [hv] at ho
      linarith
    · exact h
  have hreceiver : receiver = oneLower := by
    rcases one_cases receiver with h | h
    · exact h
    · rw [h] at ho
      have hp : testVector donor ≤ (3 / 4 : ℝ) := by
        unfold testVector; split_ifs <;> norm_num
      have hv : testVector oneUpper = 3 / 4 := by norm_num [testVector, oneUpper]
      rw [hv] at ho
      linarith
  subst donor
  subst receiver
  have hg := (hall (δ / 2) (half_pos hδ) (half_lt_self hδ)).2
  rw [rejected_one, rejected_one] at hg
  simp only [transfer, if_neg one_distinct, ite_true] at hg
  linarith

def exchangeFamily : Registration exchangeArena
    (type_of% (@improving_transfer_of_bad_insertion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨improving_transfer_of_bad_insertion, rejected, exchange_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, exchange_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Source binding selects the first original objective function occurrence in the comparison. -/
def exchangeAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@improving_transfer_of_bad_insertion) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer.exchangeUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer.exchangeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exchangeArena⟩
  objectArena := .source ⟨exchangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exchangeArena ⟨exchangeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "arg", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms exchangeFamily
#print axioms exchangeAudit

end
end Reg.D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
