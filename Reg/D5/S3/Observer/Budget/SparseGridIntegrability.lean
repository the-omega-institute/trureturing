import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Budget.SparseGridIntegrability
import Reg.Support.DependentFamily

noncomputable section
open MeasureTheory Filter Finset
open scoped ENNReal Topology BigOperators
namespace Reg.D5.S3.Observer.Budget.SparseGridIntegrability
open _root_.D5.S3.Observer.Budget.SparseGridIntegrability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

private def identityGrid : Grid := ⟨id, rfl, strictMono_id⟩
private def doubleGrid : Grid := ⟨fun n => 2 * n, by simp, fun a b h => by dsimp; omega⟩

private lemma identity_round (n : ℕ) : round identityGrid n = n := by
  have h := (sparse_grid_integrability.{0} identityGrid).2.2.1 n
  simpa [identityGrid] using h

private lemma identity_segment : segmentRatio identityGrid = 1 := by
  have hr (j : ℕ) : ((j : ℝ≥0∞) + 1) / ((j : ℝ≥0∞) + 1) = 1 :=
    ENNReal.div_self (by positivity) (by finiteness)
  simp [segmentRatio, identityGrid, Nat.cast_add, Nat.cast_one, hr]

abbrev signature : Signature where
  Params := Unit
  State _ := Grid
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => ratio S) (fun e => nomatch e)

private lemma actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), identityGrid, doubleGrid, ?_⟩
  change ratio identityGrid ≠ ratio doubleGrid
  rw [(sparse_grid_integrability.{0} identityGrid).1, identity_segment]
  have h : (2 : ℝ≥0∞) ≤ segmentRatio doubleGrid := by
    simpa [segmentRatio, doubleGrid] using
      (le_iSup (fun j : ℕ => (doubleGrid.depth (j+1) : ℝ≥0∞) /
        (doubleGrid.depth j+1 : ℕ)) 0)
  rw [← (sparse_grid_integrability.{0} doubleGrid).1] at h
  intro he
  rw [← he] at h
  norm_num at h

abbrev criterionArena : Arena where
  signature := signature
  Law R := ∀ S : Grid,
    R.readout () () S = segmentRatio S ∧
    (∀ n, n ≤ round S n ∧ ∀ j, n ≤ S.depth j → round S n ≤ S.depth j) ∧
    (∀ j, round S (S.depth j) = S.depth j) ∧
    (ratio S < ∞ ↔
      (fun n : ℕ => (round S n : ℝ)) =O[atTop] (fun n => (n : ℝ))) ∧
    (ratio S < ∞ ↔ AllLaw.{u} S)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private lemma zero_rejected : ¬ criterionArena.Law zeroReadout := by
  intro h
  have he := (h identityGrid).1
  change 0 = segmentRatio identityGrid at he
  rw [identity_segment] at he
  norm_num at he

def criterionProof : Registration criterionArena (∀ S : Grid,
    ratio S = segmentRatio S ∧
    (∀ n, n ≤ round S n ∧ ∀ j, n ≤ S.depth j → round S n ≤ S.depth j) ∧
    (∀ j, round S (S.depth j) = S.depth j) ∧
    (ratio S < ∞ ↔
      (fun n : ℕ => (round S n : ℝ)) =O[atTop] (fun n => (n : ℝ))) ∧
    (ratio S < ∞ ↔ AllLaw.{u} S)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sparse_grid_integrability, zeroReadout, zero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroReadout, ?_, rfl, zero_rejected⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := actual_dependence

abbrev witnessArena : Arena where
  signature := signature
  Law R := ∀ S : Grid, R.readout () () S = ∞ →
    ∃ t : ℕ → ℕ, StrictMono t ∧
      (∀ k, 2 ≤ t k) ∧
      (∀ k : ℕ, (k + 1 : ℝ) ^ 3 * (t k : ℝ) ≤ (round S (t k) : ℝ)) ∧
      IsProbabilityMeasure (atomicLaw t) ∧
      (∑' k, weight t k) ≤ 1 / 4 ∧
      atomicLaw t {1} = ENNReal.ofReal (1 - ∑' k, weight t k) ∧
      (∀ k, atomicLaw t {t k} = ENNReal.ofReal (weight t k)) ∧
      1 ≤ (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ≤
        ENNReal.ofReal (1 + (1 / 4 : ℝ) * ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) ∧
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) < ∞ ∧
      (∫⁻ n : ℕ, (round S n : ℝ≥0∞) ∂atomicLaw t) = ∞ ∧
      ∀ (A : Type u) [Fintype A] [DecidableEq A] [MeasurableSpace A]
        [MeasurableSingletonClass A] (zero one : A), one ≠ zero →
        (∀ n, codeTime zero one (depthPath zero one (n + 1)) = (n + 1 : ℕ)) ∧
        (∀ x, codeTime zero one x = ∞ ↔
          ∀ n, ¬((∀ i < n, x i = one) ∧ x n = zero)) ∧
        (∀ (x : ℕ → A) (n : ℕ), List.ofFn (fun i : Fin (n + 1) => x i) =
            List.replicate n one ++ [zero] ↔ (∀ i < n, x i = one) ∧ x n = zero) ∧
        (∀ n, (D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.level
          (firstZeroCode zero one) (n + 1)).card = 1) ∧
        (∀ (b : ℕ → ℕ), (∀ n, 1 ≤ n → 1 ≤ b n) →
          D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.Legal b
            (firstZeroCode zero one)) ∧
        IsProbabilityMeasure (prefixLaw zero one t) ∧
        Measure.map (codeTime zero one) (prefixLaw zero one t) =
          Measure.map (fun n : ℕ => (n : ℝ≥0∞)) (atomicLaw t) ∧
        (∫⁻ x, codeTime zero one x ∂prefixLaw zero one t) =
          (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
        (∫⁻ x, extendedRound S (codeTime zero one x) ∂prefixLaw zero one t) = ∞

def infiniteReadout : Realization signature :=
  realize signature (fun _ _ _ => ∞) (fun e => nomatch e)

private lemma infinite_rejected : ¬ witnessArena.Law infiniteReadout := by
  intro h
  obtain ⟨t, _, ht, hg, _⟩ := h identityGrid rfl
  have hbad := hg 1
  rw [identity_round] at hbad
  norm_num at hbad
  have hp : (0 : ℝ) < t 1 := by exact_mod_cast (show 0 < t 1 by have := ht 1; omega)
  nlinarith

def witnessProof : Registration witnessArena (∀ S : Grid, ratio S = ∞ →
    ∃ t : ℕ → ℕ, StrictMono t ∧
      (∀ k, 2 ≤ t k) ∧
      (∀ k : ℕ, (k + 1 : ℝ) ^ 3 * (t k : ℝ) ≤ (round S (t k) : ℝ)) ∧
      IsProbabilityMeasure (atomicLaw t) ∧
      (∑' k, weight t k) ≤ 1 / 4 ∧
      atomicLaw t {1} = ENNReal.ofReal (1 - ∑' k, weight t k) ∧
      (∀ k, atomicLaw t {t k} = ENNReal.ofReal (weight t k)) ∧
      1 ≤ (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ≤
        ENNReal.ofReal (1 + (1 / 4 : ℝ) * ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) ∧
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) < ∞ ∧
      (∫⁻ n : ℕ, (round S n : ℝ≥0∞) ∂atomicLaw t) = ∞ ∧
      ∀ (A : Type u) [Fintype A] [DecidableEq A] [MeasurableSpace A]
        [MeasurableSingletonClass A] (zero one : A), one ≠ zero →
        (∀ n, codeTime zero one (depthPath zero one (n + 1)) = (n + 1 : ℕ)) ∧
        (∀ x, codeTime zero one x = ∞ ↔
          ∀ n, ¬((∀ i < n, x i = one) ∧ x n = zero)) ∧
        (∀ (x : ℕ → A) (n : ℕ), List.ofFn (fun i : Fin (n + 1) => x i) =
            List.replicate n one ++ [zero] ↔ (∀ i < n, x i = one) ∧ x n = zero) ∧
        (∀ n, (D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.level
          (firstZeroCode zero one) (n + 1)).card = 1) ∧
        (∀ (b : ℕ → ℕ), (∀ n, 1 ≤ n → 1 ≤ b n) →
          D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.Legal b
            (firstZeroCode zero one)) ∧
        IsProbabilityMeasure (prefixLaw zero one t) ∧
        Measure.map (codeTime zero one) (prefixLaw zero one t) =
          Measure.map (fun n : ℕ => (n : ℝ≥0∞)) (atomicLaw t) ∧
        (∫⁻ x, codeTime zero one x ∂prefixLaw zero one t) =
          (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
        (∫⁻ x, extendedRound S (codeTime zero one x) ∂prefixLaw zero one t) = ∞) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_law_prefix_witness, infiniteReadout, infinite_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨infiniteReadout, ?_, rfl, infinite_rejected⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := actual_dependence

noncomputable def criterionRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.Budget.SparseGridIntegrability.sparse_grid_integrability)
    (type_of% (realize signature (fun _ _ S => ratio S) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Budget.SparseGridIntegrability.sparse_grid_integrability.__information_unit,
  realizationName := `Reg.D5.S3.Observer.Budget.SparseGridIntegrability.criterionProof,
  realizationSource := none,
  generated := false,
  arena := .source ⟨criterionArena⟩,
  objectArena := .source ⟨criterionArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source criterionArena ⟨criterionProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ S => ratio S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Budget.SparseGridIntegrability,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def witnessRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.Budget.SparseGridIntegrability.common_law_prefix_witness)
    (type_of% (realize signature (fun _ _ S => ratio S) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Budget.SparseGridIntegrability.common_law_prefix_witness.__information_unit,
  realizationName := `Reg.D5.S3.Observer.Budget.SparseGridIntegrability.witnessProof,
  realizationSource := none,
  generated := false,
  arena := .source ⟨witnessArena⟩,
  objectArena := .source ⟨witnessArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source witnessArena ⟨witnessProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ S => ratio S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Budget.SparseGridIntegrability,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "domain", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms criterionProof
#print axioms witnessProof
end Reg.D5.S3.Observer.Budget.SparseGridIntegrability
