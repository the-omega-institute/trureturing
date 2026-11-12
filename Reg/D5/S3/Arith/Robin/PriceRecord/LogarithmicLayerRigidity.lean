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

namespace ThetaError

open Filter Asymptotics

def actual : Realization signature :=
  realize signature (fun _ _ t => Chebyshev.theta t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t => t + t / Real.log t ^ 8) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (fun t : ℝ => R.readout () () t - t) =o[atTop]
    (fun t : ℝ => t / Real.log t ^ 8)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.def (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hb
  let t := max T 2
  have ht : 1 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq : 0 < t / Real.log t ^ 8 :=
    div_pos (by linarith) (pow_pos (Real.log_pos ht) 8)
  have hbad := hT t (le_max_left _ _)
  change |(t + t / Real.log t ^ 8) - t| ≤ (1 / 2 : ℝ) * |t / Real.log t ^ 8| at hbad
  rw [add_sub_cancel_left, abs_of_pos hq] at hbad
  linarith

def family : Registration arena (type_of% @theta_error_eight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨theta_error_eight, rejected, rejected_law⟩
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
    refine ⟨(), 1, 2, ?_⟩
    change Chebyshev.theta 1 ≠ Chebyshev.theta 2
    rw [Chebyshev.theta_one]
    exact (Chebyshev.theta_pos (by norm_num : (2 : ℝ) ≤ 2)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@theta_error_eight) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.theta_error_eight.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.ThetaError.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Chebyshev.theta t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end ThetaError

end Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity

namespace Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.PublicExchangeLaws
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace record_ratio_limit
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => layerPrime p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type*} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (j : ℕ) (hj : 2 ≤ j)
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop),
    Tendsto (fun x => ((V.readout ()) (m x) j : ℝ) ^ j / (largestPrime (m x) : ℝ))
      l (𝓝 (j : ℝ))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.record_ratio_limit

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.record_ratio_limit)) ↔ arena.Law actual := Iff.rfl

end record_ratio_limit

namespace coarse_scale_limits
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
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type*} {l : Filter α} (P Q : α → ℝ)
    (j : ℕ) (hj : 2 ≤ j) (hQnonneg : ∀ x, 0 ≤ Q x)
    (hP : Tendsto P l atTop)
    (hfirst : Tendsto (fun x => Q x ^ j / P x) l (𝓝 (j : ℝ))),
    Tendsto Q l atTop ∧
      Tendsto (fun x => (V.readout () ()) (Q x) / (V.readout () ()) (P x)) l (𝓝 (j : ℝ)⁻¹) ∧
      Tendsto (fun x => Q x / P x) l (𝓝 0)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.coarse_scale_limits

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.coarse_scale_limits)) ↔ arena.Law actual := Iff.rfl

end coarse_scale_limits

end Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.PublicExchangeLaws
