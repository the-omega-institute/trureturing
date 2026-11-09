import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin
import Reg.Support.DependentFamily

/-! Exact whole-law source mirror with the original F/T readouts and empty
   anchors. The actual law, literal source bridge, observational dependence
   and implication from whole-family rejection to RH are proved below.
   Full four-slot registration is not supplied. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter

namespace Reg.D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger (goldenResourceObjective)
open _root_.D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin (K)
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin (F T all_integer_sharp_margin)
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (D)
open _root_.D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ n => if role then T n else F n) (fun e => nomatch e)

/-- Both actual integer margin sequences are readouts. RH and the original
real-price/full-positive-predecessor witness telescope are retained verbatim.
The law has no desired endpoint as an added premise. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀ _hRH : RiemannHypothesis,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K - ε < V.readout false () n ∧
      Real.exp Real.eulerMascheroniConstant * K - ε < V.readout true () n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m : ℕ, ∃ lambda : ℝ,
      N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |V.readout false () m - K| < ε ∧
      |V.readout true () m - Real.exp Real.eulerMascheroniConstant * K| < ε) ∧
    Filter.liminf (fun n : ℕ => V.readout false () n) atTop = K ∧
    Filter.liminf (fun n : ℕ => V.readout true () n) atTop =
      Real.exp Real.eulerMascheroniConstant * K

private theorem actual_law : arena.Law actual := by
  exact @all_integer_sharp_margin

private theorem source_bridge :
    (type_of% (@all_integer_sharp_margin)) ↔ arena.Law actual := Iff.rfl

/-- Every whole-family rejection of this exact conditional law entails RH. -/
private theorem rejection_requires_rh (bad : Realization signature)
    (hbad : ¬ arena.Law bad) : RiemannHypothesis := by
  classical
  by_contra hnot
  apply hbad
  intro hRH
  exact (hnot hRH).elim

/-- The original observations vary on the actual natural state space. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  have h2 : (2 / 3 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have h2pos : 0 < Real.log 2 := by linarith
  have h2one : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hll : Real.log (Real.log 2) < 0 := Real.log_neg h2pos h2one
  have hhalf : -Real.log (Real.log 2) < (1 / 2 : ℝ) := by
    have hmon := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 / 3) h2
    have hsmall := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (3 / 2 : ℝ) ≠ 1)
    have hid : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
      rw [Real.log_div (by norm_num) (by norm_num),
        Real.log_div (by norm_num) (by norm_num)]
      ring
    rw [hid] at hmon
    linarith
  have hthird : Real.log (Real.log (Real.log 2)) < -(2 / 3 : ℝ) := by
    have hmon := Real.log_lt_log (neg_pos.mpr hll) hhalf
    rw [Real.log_neg_eq_log, Real.log_div (by norm_num) (by norm_num),
      Real.log_one, zero_sub] at hmon
    linarith
  have hsigma : ArithmeticFunction.sigma 1 2 = 3 := by
    have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hmargin : robinLogMargin 2 < 0 := by
    dsimp [robinLogMargin]
    rw [hsigma]
    norm_num only [Nat.cast_ofNat]
    have hab := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hF : 0 < F 2 := by
    change 0 < D (Real.log (2 : ℝ)) * robinLogMargin 2
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (Real.sqrt_pos.mpr h2pos) hll) hmargin
  have hT : T 2 < 0 := by
    dsimp [T]
    rw [hsigma]
    norm_num only [Nat.cast_ofNat]
    apply mul_neg_of_neg_of_pos
    · have h := mul_neg_of_pos_of_neg
        (Real.exp_pos Real.eulerMascheroniConstant) hll
      linarith
    · exact Real.sqrt_pos.mpr h2pos
  intro i
  refine ⟨(), 0, 2, ?_⟩
  cases i
  · change F 0 ≠ F 2
    have hz : F 0 = 0 := by simp [F, D]
    rw [hz]
    exact ne_of_lt hF
  · change T 0 ≠ T 2
    have hz : T 0 = 0 := by simp [T]
    rw [hz]
    exact ne_of_gt hT

/- The remaining audit obligations are whole-family intervention and
   sensitivity, followed by complete enrolled-template source-selection
   validation. The exact law is conditional on RH for every realization:
   rejecting any alternate family entails RH by rejection_requires_rh.
   Empty anchors add no rejection evidence. No Contract.Registration or
   declared_validated claim is supplied. -/

end Reg.D5.S3.Arith.Robin.Analytic.RHSharpAllIntegerMargin
