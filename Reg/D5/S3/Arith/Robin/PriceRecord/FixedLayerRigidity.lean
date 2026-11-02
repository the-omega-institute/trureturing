import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import Reg.Support.DependentFamily

/-! Source-bound audit of uniform fixed prime-layer rigidity. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity

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

/-- Only the threshold's occurrence on the left of the largest-prime premise is
observed. The positive existential threshold, all records at positive prices,
and the complete absolute-ratio conclusion retain their original scope. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ) (_hj : 2 ≤ j) (epsilon : ℝ) (_hepsilon : 0 < epsilon),
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      R.readout () () T ≤ (largestPrime m : ℝ) →
      |(layerPrime m j : ℝ) ^ j / (largestPrime m : ℝ) - (j : ℝ)| < epsilon

private theorem first_two_layer :
    goldenLayerMarginal 2 1 * Real.log (2 : ℝ) = Real.log (3 / 2 : ℝ) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold goldenLayerMarginal
  norm_num only [Nat.cast_ofNat]
  rw [div_mul_cancel₀ _ hlog]

theorem half_first_two_layer_pos : 0 < goldenLayerMarginal 2 1 / 2 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hmarginal : 0 < goldenLayerMarginal 2 1 :=
    (mul_pos_iff_of_pos_right hlog).mp (by rwa [first_two_layer])
  exact div_pos hmarginal (by norm_num)

theorem two_record_at_half_first_layer :
    ∀ n : ℕ, 0 < n → n < 2 →
      goldenResourceObjective (goldenLayerMarginal 2 1 / 2) n <
        goldenResourceObjective (goldenLayerMarginal 2 1 / 2) 2 := by
  have hstep :
      goldenResourceObjective (goldenLayerMarginal 2 1 / 2) 2 -
          goldenResourceObjective (goldenLayerMarginal 2 1 / 2) 1 =
        (goldenLayerMarginal 2 1 - goldenLayerMarginal 2 1 / 2) *
          Real.log (2 : ℝ) := by
    simpa using golden_resource_objective_single_layer_delta
      (goldenLayerMarginal 2 1 / 2) (n := 1) (p := 2) (by norm_num) (by norm_num)
  have hpos : 0 <
      (goldenLayerMarginal 2 1 - goldenLayerMarginal 2 1 / 2) * Real.log (2 : ℝ) :=
    mul_pos (by linarith [half_first_two_layer_pos]) (Real.log_pos (by norm_num))
  intro n hn hnm
  have hn1 : n = 1 := by omega
  subst n
  linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨T, _hT, hrecord⟩ := h 2 (by norm_num) 1 (by norm_num)
  have hp : (2 : ℕ).primeFactors = {2} := (by norm_num : Nat.Prime 2).primeFactors
  have hf : (2 : ℕ).factorization 2 = 1 :=
    (by norm_num : Nat.Prime 2).factorization_self
  have hP : largestPrime 2 = 2 := by simp [largestPrime, hp]
  have hL : layerPrime 2 2 = 1 := by norm_num [layerPrime, hp, hf]
  have hbad := hrecord 2 (by norm_num) (goldenLayerMarginal 2 1 / 2)
    half_first_two_layer_pos two_record_at_half_first_layer
    (by change (0 : ℝ) ≤ (largestPrime 2 : ℝ); rw [hP]; norm_num)
  norm_num [hP, hL] at hbad

def family : Registration arena (type_of% @price_record_fixed_layer_rigidity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@price_record_fixed_layer_rigidity, rejected, rejected_law⟩
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
    (@price_record_fixed_layer_rigidity) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity.price_record_fixed_layer_rigidity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
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

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
