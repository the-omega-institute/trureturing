import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison
import Reg.Support.DependentFamily

/-! Source-bound audit for the finite actual-record Euler deficit. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (tail largestPrime layerTail)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity (layerPrime)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Lattices.Klartag
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 2 ≤ m → ∀ {lambda : ℝ}, 0 < lambda →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
    0 ≤ tail (R.readout () () m) - finitePrimeSquareSum (R.readout () () m) ∧
      tail (R.readout () () m) - finitePrimeSquareSum (R.readout () () m) ≤
        6 / (largestPrime (R.readout () () m) : ℝ) ^ (2 / 3 : ℝ) +
          2 / (layerPrime (R.readout () () m) 2 : ℝ) ^ 3

private theorem two_record_at_one_hundredth :
    ∀ n : ℕ, 0 < n → n < 2 →
      goldenResourceObjective (1 / 100) n < goldenResourceObjective (1 / 100) 2 := by
  intro n hn hlt
  have hn1 : n = 1 := by omega
  subst n
  rw [golden_resource_sigma_identity _ (by norm_num : 1 ≤ (1 : ℕ)),
    golden_resource_sigma_identity _ (by norm_num : 1 ≤ (2 : ℕ))]
  have hs1 : (ArithmeticFunction.sigma 1 1 : ℝ) = 1 := by norm_num [ArithmeticFunction.sigma]
  have hs2 : (ArithmeticFunction.sigma 1 2 : ℝ) = 3 := by norm_num [ArithmeticFunction.sigma]
  rw [hs1, hs2]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, div_one, Real.log_one, mul_zero, sub_self]
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  norm_num at hh
  linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (m := 2) (by norm_num) (lambda := 1 / 100) (by norm_num)
    two_record_at_one_hundredth
  have hquad := neg_log_one_sub_le (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num)
  have htail : tail 3 = -Real.log (8 / 9 : ℝ) := by
    norm_num [tail, layerTail]
  have hsum : finitePrimeSquareSum 3 = (13 / 36 : ℝ) := by
    have hfilter : (Finset.Ioc 1 3).filter Nat.Prime = {2, 3} := by decide
    simp only [finitePrimeSquareSum, largestPrime, layerPrime]
    rw [hfilter]
    norm_num
  have hbad' :
      0 ≤ tail 3 - finitePrimeSquareSum 3 := by
    simpa [rejected, realize] using hbad.1
  rw [htail, hsum] at hbad'
  have hneg : -Real.log (8 / 9 : ℝ) - (13 / 36 : ℝ) < 0 := by
    have hq : -Real.log (8 / 9 : ℝ) ≤ (1 / 9 : ℝ) + (1 / 9 : ℝ) ^ 2 := by
      convert hquad using 1 <;> norm_num
    linarith
  exact (not_le_of_gt hneg) hbad'

def family : Registration arena (type_of% @actual_finite_euler_deficit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_finite_euler_deficit, rejected, rejected_law⟩
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
    change (0 : ℕ) ≠ 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@actual_finite_euler_deficit) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison.actual_finite_euler_deficit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "body", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_finite_euler_deficit
#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.FiniteDeficitComparison
