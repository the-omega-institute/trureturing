import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass
import Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import Reg.Support.DependentFamily

/-! Exact source-bound audits of actual full-record third-layer estimates. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity (layerPrime)
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.EulerLayerRootCorrection (strict_inventory_third_layer_mass)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (half_first_two_layer_pos two_record_at_half_first_layer)
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass

abbrev finiteSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ _ m => m) (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ _ => 128) (fun e => nomatch e)

/-- Only the argument of the upper-bounded mass is observed. Every premise,
the nonnegativity conjunct and the right-hand bound retain the original m. -/
abbrev finiteArena : Arena where
  signature := finiteSignature
  Law R := ∀ {m : ℕ}, 2 ≤ m → ∀ {lambda : ℝ}, 0 ≤ lambda →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
    0 ≤ strict_inventory_third_layer_mass m ∧
      strict_inventory_third_layer_mass (R.readout () () m) ≤
        (layerPrime m 3 : ℝ) * Real.log (4 * (largestPrime m : ℝ) ^ 2)

private theorem finite_rejected_law : ¬ finiteArena.Law finiteRejected := by
  intro h
  have hbad := (h (m := 2) (by norm_num)
    (lambda := goldenLayerMarginal 2 1 / 2) half_first_two_layer_pos.le
    two_record_at_half_first_layer).2
  have hp2 : (2 : ℕ).primeFactors = {2} := (by norm_num : Nat.Prime 2).primeFactors
  have hf2 : (2 : ℕ).factorization 2 = 1 :=
    (by norm_num : Nat.Prime 2).factorization_self
  have hP2 : largestPrime 2 = 2 := by simp [largestPrime, hp2]
  have hL2 : layerPrime 2 3 = 1 := by norm_num [layerPrime, hp2, hf2]
  have hp128 : (128 : ℕ).primeFactors = {2} := by
    change ((2 : ℕ) ^ 7).primeFactors = {2}
    rw [Nat.primeFactors_pow 2 (by norm_num), hp2]
  have hf128 : (128 : ℕ).factorization 2 = 7 := by
    change ((2 : ℕ) ^ 7).factorization 2 = 7
    exact Nat.factorization_pow_self (by norm_num : Nat.Prime 2)
  have hmass : strict_inventory_third_layer_mass 128 = 5 * Real.log 2 := by
    norm_num [strict_inventory_third_layer_mass, hp128, Finset.filter_singleton, hf128]
  have hlog : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
    norm_num
  change strict_inventory_third_layer_mass 128 ≤
    (layerPrime 2 3 : ℝ) * Real.log (4 * (largestPrime 2 : ℝ) ^ 2) at hbad
  rw [hmass, hP2, hL2] at hbad
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul] at hbad
  rw [hlog] at hbad
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

def finiteFamily : Registration finiteArena (type_of% @price_record_third_layer_mass_bound) where
  actual := finiteActual
  bridge := Iff.rfl
  variation := ⟨@price_record_third_layer_mass_bound, finiteRejected, finite_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, finite_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 1; norm_num⟩

abbrev limitSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def limitActual : Realization limitSignature :=
  realize limitSignature (fun _ _ x => x) (fun e => nomatch e)

def limitRejected : Realization limitSignature :=
  realize limitSignature (fun _ _ _ => 0) (fun e => nomatch e)

/-- A common real scale readout observes the cutoff in the prime premise and
the requested precision in the conclusion. Both remain free in the full
original telescope; the positive precision and existential cutoff are literal. -/
abbrev limitArena : Arena where
  signature := limitSignature
  Law R := ∀ epsilon : ℝ, 0 < epsilon → ∃ T : ℝ, 0 < T ∧
    ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
    R.readout () () T ≤ (largestPrime m : ℝ) →
    strict_inventory_third_layer_mass m / Real.sqrt (largestPrime m : ℝ) <
      R.readout () () epsilon

private theorem limit_rejected_law : ¬ limitArena.Law limitRejected := by
  intro h
  obtain ⟨T, _, hrecords⟩ := h 1 (by norm_num)
  have hbad := hrecords 2 (by norm_num) (goldenLayerMarginal 2 1 / 2)
    half_first_two_layer_pos two_record_at_half_first_layer
    (by change (0 : ℝ) ≤ (largestPrime 2 : ℝ); positivity)
  have hp2 : (2 : ℕ).primeFactors = {2} := (by norm_num : Nat.Prime 2).primeFactors
  have hf2 : (2 : ℕ).factorization 2 = 1 :=
    (by norm_num : Nat.Prime 2).factorization_self
  change strict_inventory_third_layer_mass 2 / Real.sqrt (largestPrime 2 : ℝ) < 0 at hbad
  norm_num [strict_inventory_third_layer_mass, hp2, Finset.filter_singleton, hf2] at hbad

def limitFamily : Registration limitArena (type_of% @price_record_third_layer_mass_vanishing) where
  actual := limitActual
  bridge := Iff.rfl
  variation := ⟨@price_record_third_layer_mass_vanishing, limitRejected, limit_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨limitRejected, ?_, rfl, limit_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩

def finiteAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@price_record_third_layer_mass_bound) (Realization finiteSignature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass.price_record_third_layer_mass_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass.finiteFamily
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false } ] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def limitAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@price_record_third_layer_mass_vanishing) (Realization limitSignature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass.price_record_third_layer_mass_vanishing.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass.limitFamily
  realizationSource := none
  generated := false
  arena := .source ⟨limitArena⟩
  objectArena := .source ⟨limitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source limitArena ⟨limitFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize limitSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false } ] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms finiteFamily
#print axioms finiteAudit
#print axioms limitFamily
#print axioms limitAudit

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualThirdLayerMass
