import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity

/-! Source-bound audit of prime capacity in shrinking relative windows. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The observation selects only the threshold in `T ≤ x`. All cardinalities,
prime predicates, interval endpoints, and the positive threshold stay literal. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ x : ℝ,
    R.readout () () T ≤ x → ∀ N : ℕ, N ≤ ⌈C * Real.log x ^ 3⌉₊ →
    ∃ D U : Finset ℕ, D.card = N ∧ U.card = N ∧
      (∀ p ∈ D, p.Prime ∧ x * (1 - 1 / Real.log x ^ 3) < (p : ℝ) ∧
        (p : ℝ) ≤ x) ∧
      (∀ q ∈ U, q.Prime ∧ x < (q : ℝ) ∧
        (q : ℝ) ≤ x * (1 + 1 / Real.log x ^ 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := 2 / Real.log (2 : ℝ) ^ 3
  have hC : 0 < C := div_pos (by norm_num) (pow_pos hlog 3)
  obtain ⟨T, _, hT⟩ := h C hC
  have hN : 2 ≤ ⌈C * Real.log (2 : ℝ) ^ 3⌉₊ := by
    have heq : C * Real.log (2 : ℝ) ^ 3 = 2 := by
      dsimp [C]
      field_simp
    rw [heq]
    norm_num
  obtain ⟨D, U, hDcard, _, hD, _⟩ := hT 2 (by change (0 : ℝ) ≤ 2; norm_num) 2 hN
  have hsub : D ⊆ {2} := by
    intro p hp
    have hp0 := (hD p hp).1.two_le
    have hp1 : p ≤ 2 := by exact_mod_cast (hD p hp).2.2
    simpa only [Finset.mem_singleton] using (show p = 2 by omega)
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_singleton, hDcard] at hcard
  omega

def family : Registration arena (type_of% @shrinking_prime_windows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shrinking_prime_windows, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@shrinking_prime_windows) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.shrinking_prime_windows.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

/-- The threshold observation retains all literal predecessor comparisons and
both logarithms in the exact second-order conclusion. -/
abbrev logarithmicArena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ) (_hj : 2 ≤ j) (epsilon : ℝ) (_hepsilon : 0 < epsilon),
    ∃ T : ℝ, 1 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      R.readout () () T ≤ (largestPrime m : ℝ) →
      |Real.log (largestPrime m : ℝ) *
        ((layerPrime m j : ℝ) ^ j / ((j : ℝ) * (largestPrime m : ℝ)) - 1) +
          Real.log (j : ℝ)| < epsilon

private theorem rejected_logarithmic_law : ¬ logarithmicArena.Law rejected := by
  intro h
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨T, _, hT⟩ := h 2 (by norm_num) (Real.log 2 / 8) (by positivity)
  have hp : (2 : ℕ).primeFactors = {2} := (by norm_num : Nat.Prime 2).primeFactors
  have hf : (2 : ℕ).factorization 2 = 1 :=
    (by norm_num : Nat.Prime 2).factorization_self
  have hP : largestPrime 2 = 2 := by simp [largestPrime, hp]
  have hQ : layerPrime 2 2 = 1 := by norm_num [layerPrime, hp, hf]
  have hbad := hT 2 (by norm_num) (goldenLayerMarginal 2 1 / 2)
    FixedLayerRigidity.half_first_two_layer_pos FixedLayerRigidity.two_record_at_half_first_layer
    (by change (0 : ℝ) ≤ (largestPrime 2 : ℝ); rw [hP]; norm_num)
  rw [hP, hQ] at hbad
  norm_num only [Nat.cast_ofNat, Nat.cast_one, one_pow] at hbad
  have heq : Real.log (2 : ℝ) * -(3 / 4) + Real.log (2 : ℝ) = Real.log 2 / 4 := by ring
  rw [heq, abs_of_pos (by positivity : 0 < Real.log (2 : ℝ) / 4)] at hbad
  linarith

def logarithmicFamily : Registration logarithmicArena (type_of% @price_record_logarithmic_layer_rigidity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@price_record_logarithmic_layer_rigidity, rejected, rejected_logarithmic_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_logarithmic_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

def logarithmicAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@price_record_logarithmic_layer_rigidity) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.logarithmicFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logarithmicArena⟩
  objectArena := .source ⟨logarithmicArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logarithmicArena ⟨logarithmicFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms logarithmicFamily
#print axioms logarithmicAudit

end Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
