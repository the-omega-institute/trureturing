/- GID: D5/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency
   generality: G
   mirror-B: D5/B/S1/Words/Forbidden/BonaMagaRicheyHalfFrequency
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Half letter frequency characterizes balanced borders of nonempty binary words. -/
/-
proof_shape: lengthEval_eq: bind-only; consumer: lengthEval_ge_count_sub_one
proof_shape: avoidCount_zero: bind-only; consumer: lengthEval_ge_count_sub_one
proof_shape: lengthEval_ge_count_sub_one: bind-only; consumer: lengthEval_growthApproach_bound
proof_shape: lengthEval_growthApproach_bound: bind-only; consumer: lengthEval_growthApproach_pos
proof_shape: lengthEval_growthApproach_pos: bind-only; consumer: densityWeights_nonneg
proof_shape: lengthEval_growthApproach_atTop: bind-only; consumer: densityWeights_escape
proof_shape: densityWeights_nonneg: bind-only; consumer: assumed_limit_imbalance_ratio
proof_shape: densityWeights_summable: bind-only; consumer: assumed_limit_imbalance_ratio
proof_shape: densityWeights_total: bind-only; consumer: assumed_limit_imbalance_ratio
proof_shape: densityWeights_escape: content
proof_shape: signedDensity_bound: bind-only; consumer: assumed_limit_imbalance_ratio
proof_shape: densityWeights_signed_value: bind-only; consumer: assumed_limit_imbalance_ratio
proof_shape: assumed_limit_imbalance_ratio: content
proof_shape: assumed_half_imbalance_ratio_zero: bind-only; consumer: tendsto_half_implies_boundaryRight_zero
proof_shape: moment_ratio_cross: bind-only; consumer: tendsto_half_implies_boundaryRight_zero
proof_shape: boundaryLeft_continuous: bind-only; consumer: tendsto_half_implies_boundaryRight_zero
proof_shape: boundaryRight_continuous: bind-only; consumer: tendsto_half_implies_boundaryRight_zero
proof_shape: tendsto_half_implies_boundaryRight_zero: content
proof_shape: tendsto_half_implies_balanced_long: content
proof_shape: balanced_mixed_pair: bind-only; consumer: result
proof_shape: not_tendsto_half_00: bind-only; consumer: result
proof_shape: result: content
escape_witness: result on result's live proof path.
admission_basis: open-problem-resolution (#14224; Proved)
Direct frozen dependencies: none on the protected baseline.
Same-delivery dependencies: ForbiddenWordRationalBoundary.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.Forbidden.ForbiddenWordRationalBoundary
import Mathlib.Algebra.BigOperators.Field

open Filter Finset
open scoped Topology

namespace D5.S1.Words.Forbidden.BonaMagaRicheyHalfFrequency
open D5.S1.Words.Forbidden.ForbiddenWordCounting
open D5.S1.Words.Forbidden.ForbiddenWordGrowth
open D5.S1.Words.Forbidden.BorderImbalanceExclusion
open D5.S1.Words.Forbidden.BalancedBordersHalfFrequency
open D5.S1.Words.Forbidden.ForbiddenWordRationalBoundary

def claim : Prop :=
  ∀ w : List Bool, w ≠ [] →
    (Tendsto (rho w) atTop (𝓝 (1 / 2 : ℝ)) ↔ BalancedBorders w)

private noncomputable def densityWeights (w : List Bool) (x : ℝ) (m : ℕ) : ℝ :=
  ((m:ℝ)*avoidCount w m*x^m)/(seriesEval (realLengthSeries w)) x

private theorem lengthEval_eq (w : List Bool) (x : ℝ) :
    (seriesEval (realLengthSeries w)) x=∑' m : ℕ,(m:ℝ)*avoidCount w m*x^m := by
  simp [seriesEval,realLengthSeries,coeff_lengthMoment,realCountSeries]

private theorem avoidCount_zero {w : List Bool} (hw : w≠[]) : avoidCount w 0=1 := by
  have he := congrArg (Polynomial.eval (1 : ℚ)) (avoidCoeff_zero hw)
  have hc : ((omega w 0).card : ℚ) = 1 := by
    simpa [avoidCoeff, Polynomial.eval_finset_sum] using he
  unfold avoidCount
  exact_mod_cast hc

private theorem lengthEval_ge_count_sub_one {w : List Bool} (hw : w≠[]) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x < 1) :
    seriesEval (realCountSeries w) x-1 ≤ (seriesEval (realLengthSeries w)) x := by
  have ha := avoidCount_summable hw hx0 hx
  have hl := weighted_avoidCount_summable hw 1 hx0 hx
  simp only [pow_one] at hl
  have htail : (∑' m : ℕ,avoidCount w (m+1)*x^(m+1)) ≤
      ∑' m : ℕ,((m+1:ℕ):ℝ)*avoidCount w (m+1)*x^(m+1) := by
    apply Summable.tsum_le_tsum _ (ha.comp_injective (by intro i j h; exact Nat.add_right_cancel h))
      (hl.comp_injective (by intro i j h; exact Nat.add_right_cancel h))
    intro m
    have hb := avoidCount_pos hw (m+1)
    have hc : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ m+1)
    have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hb.le (pow_nonneg hx0 (m+1)))
    simpa [mul_assoc] using hh
  have hea := ha.sum_add_tsum_nat_add 1
  have hel := hl.sum_add_tsum_nat_add 1
  simp [avoidCount_zero hw] at hea hel
  simp only [Nat.cast_add,Nat.cast_one] at htail
  rw [lengthEval_eq]
  simp [seriesEval,realCountSeries]
  linarith

private theorem lengthEval_growthApproach_bound {w : List Bool} (hw : w≠[]) (t : ℕ) :
    (t:ℝ)+1 ≤ (seriesEval (realLengthSeries w)) (growthApproach w hw t) := by
  have hA := countSeriesEval_growthApproach hw t
  have hB := lengthEval_ge_count_sub_one hw (growthApproach_pos hw t).le (growthApproach_inside hw t)
  linarith

private theorem lengthEval_growthApproach_pos {w : List Bool} (hw : w≠[]) (t : ℕ) :
    0 < (seriesEval (realLengthSeries w)) (growthApproach w hw t) := by
  have hb := lengthEval_growthApproach_bound hw t
  have ht := Nat.cast_nonneg (α := ℝ) t
  linarith

private theorem lengthEval_growthApproach_atTop {w : List Bool} (hw : w≠[]) :
    Tendsto (fun t => (seriesEval (realLengthSeries w)) (growthApproach w hw t)) atTop atTop :=
  tendsto_atTop_mono (fun t => lengthEval_growthApproach_bound hw t)
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

private theorem densityWeights_nonneg {w : List Bool} (hw : w≠[]) (t m : ℕ) :
    0 ≤ densityWeights w (growthApproach w hw t) m := by
  unfold densityWeights
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (avoidCount_pos hw m).le)
    (pow_nonneg (growthApproach_pos hw t).le m)) (lengthEval_growthApproach_pos hw t).le

private theorem densityWeights_summable {w : List Bool} (hw : w≠[]) (t : ℕ) :
    Summable (densityWeights w (growthApproach w hw t)) := by
  have hm : Summable (fun m : ℕ => (m:ℝ)*avoidCount w m*(growthApproach w hw t)^m) := by
    simpa only [pow_one] using
      weighted_avoidCount_summable hw 1 (growthApproach_pos hw t).le (growthApproach_inside hw t)
  have he : densityWeights w (growthApproach w hw t)=
      (fun m : ℕ => ((m:ℝ)*avoidCount w m*(growthApproach w hw t)^m)*
        ((seriesEval (realLengthSeries w)) (growthApproach w hw t))⁻¹) := by
    funext m
    rfl
  rw [he]
  exact hm.mul_right _

private theorem densityWeights_total {w : List Bool} (hw : w≠[]) (t : ℕ) :
    (∑' m,densityWeights w (growthApproach w hw t) m)=1 := by
  unfold densityWeights
  rw [tsum_div_const,← lengthEval_eq,div_self (lengthEval_growthApproach_pos hw t).ne']

private theorem densityWeights_escape {w : List Bool} (hw : w≠[]) (N : ℕ) :
    Tendsto (fun t => ∑ m ∈ range N,densityWeights w (growthApproach w hw t) m) atTop (𝓝 0) := by
  have hnum : Continuous (fun x : ℝ => ∑ m ∈ range N,(m:ℝ)*avoidCount w m*x^m) := by fun_prop
  have ht := hnum.tendsto (1/growthRate w hw) |>.comp (growthApproach_tendsto hw)
  have hh := ht.div_atTop (lengthEval_growthApproach_atTop hw)
  simpa [densityWeights,← sum_div] using hh

private theorem signedDensity_bound {w : List Bool} (hw : w≠[]) (m : ℕ) :
    |2*rho w m-1| ≤ 1 := by
  have hlo := rho_nonneg w m
  have hhi : rho w m ≤ 1 := by
    cases m with
    | zero => simp [rho]
    | succ m => exact rho_le_one hw (by omega)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem densityWeights_signed_value {w : List Bool} (hw : w≠[]) (x : ℝ) (m : ℕ) :
    densityWeights w x m*(2*rho w m-1)=
      (PowerSeries.coeff m (realImbalanceSeries w)*x^m)/(seriesEval (realLengthSeries w)) x := by
  cases m with
  | zero =>
    have ho : avoidOnes w 0=0 := by
      unfold avoidOnes
      apply sum_eq_zero
      intro u hu
      have he : u=[] := List.length_eq_zero_iff.mp (mem_omega.mp hu).1
      subst u
      simp
    simp [densityWeights,realImbalanceSeries,ho]
  | succ m =>
    have hd : ((m+1:ℕ):ℝ)*avoidCount w (m+1) ≠ 0 := by
      exact ne_of_gt (mul_pos (by positivity) (avoidCount_pos hw _))
    have hc : ((omega w (m+1)).card:ℝ)≠0 := by
      exact_mod_cast (card_pos.mpr (omega_nonempty hw (m+1))).ne'
    unfold densityWeights rho realImbalanceSeries avoidCount avoidOnes at *
    simp only [PowerSeries.coeff_mk]
    field_simp [hc]
    <;> ring

private theorem assumed_limit_imbalance_ratio {w : List Bool} (hw : w≠[]) {a : ℝ}
    (hlim : Tendsto (rho w) atTop (𝓝 a)) :
    Tendsto (fun t => seriesEval (realImbalanceSeries w) (growthApproach w hw t)/
      (seriesEval (realLengthSeries w)) (growthApproach w hw t)) atTop (𝓝 (2*a-1)) := by
  have hu : Tendsto (fun m => 2*rho w m-1) atTop (𝓝 (2*a-1)) :=
    (hlim.const_mul 2).sub_const 1
  have hB (m : ℕ) : |2*rho w m-1-(2*a-1)| ≤ 1+|2*a-1| := by
    calc
      _ ≤ |2*rho w m-1|+|2*a-1| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (2*rho w m-1) 0 (2*a-1)
      _ ≤ _ := add_le_add (signedDensity_bound hw m) le_rfl
  have hh := weighted_tsum_tendsto atTop (fun t => densityWeights w (growthApproach w hw t))
    (fun m => 2*rho w m-1) (2*a-1) (1+|2*a-1|) (densityWeights_nonneg hw)
    (densityWeights_summable hw) (densityWeights_total hw) (by positivity) hB hu (densityWeights_escape hw)
  have he : (fun t => ∑' m,densityWeights w (growthApproach w hw t) m*(2*rho w m-1))=
      (fun t => seriesEval (realImbalanceSeries w) (growthApproach w hw t)/
        (seriesEval (realLengthSeries w)) (growthApproach w hw t)) := by
    funext t
    simp_rw [densityWeights_signed_value hw]
    rw [tsum_div_const]
    rfl
  rw [he] at hh
  exact hh

private theorem assumed_half_imbalance_ratio_zero {w : List Bool} (hw : w≠[])
    (hhalf : Tendsto (rho w) atTop (𝓝 (1/2:ℝ))) :
    Tendsto (fun t => seriesEval (realImbalanceSeries w) (growthApproach w hw t)/
      (seriesEval (realLengthSeries w)) (growthApproach w hw t)) atTop (𝓝 0) := by
  simpa using assumed_limit_imbalance_ratio hw hhalf

private noncomputable def boundaryLeft (w : List Bool) (x : ℝ) : ℝ :=
  overlapLengthEval w x*denomEval w x-overlapEval w x*denomLengthEval w x

private noncomputable def boundaryRight (w : List Bool) (x : ℝ) : ℝ :=
  overlapMomentEval w x*denomEval w x-overlapEval w x*denomMomentEval w x

private theorem moment_ratio_cross {w : List Bool} (hw : w≠[]) (t : ℕ) :
    (seriesEval (realImbalanceSeries w) (growthApproach w hw t)/
      (seriesEval (realLengthSeries w)) (growthApproach w hw t))*boundaryLeft w (growthApproach w hw t)=
      boundaryRight w (growthApproach w hw t) := by
  let x := growthApproach w hw t
  have hc := scalar_counting_identity hw (growthApproach_pos hw t).le (growthApproach_inside hw t)
  have hm := scalar_moment_identity hw (growthApproach_pos hw t).le (growthApproach_inside hw t)
  have hl := scalar_length_identity hw (growthApproach_pos hw t).le (growthApproach_inside hw t)
  have hb := lengthEval_growthApproach_pos hw t
  have heL : boundaryLeft w x=(seriesEval (realLengthSeries w)) x*(denomEval w x)^2 := by
    unfold boundaryLeft
    calc
      _ = (seriesEval (realLengthSeries w) x*denomEval w x+
        seriesEval (realCountSeries w) x*denomLengthEval w x)*denomEval w x-
        (seriesEval (realCountSeries w) x*denomEval w x)*denomLengthEval w x := by rw [hc,hl]
      _ = _ := by ring
  have heR : boundaryRight w x=seriesEval (realImbalanceSeries w) x*(denomEval w x)^2 := by
    unfold boundaryRight
    calc
      _ = (seriesEval (realImbalanceSeries w) x*denomEval w x+
        seriesEval (realCountSeries w) x*denomMomentEval w x)*denomEval w x-
        (seriesEval (realCountSeries w) x*denomEval w x)*denomMomentEval w x := by rw [hc,hm]
      _ = _ := by ring
  change (seriesEval (realImbalanceSeries w) x/(seriesEval (realLengthSeries w)) x)*boundaryLeft w x=boundaryRight w x
  rw [heL,heR]
  have hbx : (seriesEval (realLengthSeries w)) x≠0 := ne_of_gt hb
  field_simp [hbx]

private theorem boundaryLeft_continuous (w : List Bool) : Continuous (boundaryLeft w) := by
  unfold boundaryLeft denomLengthEval denomEval overlapLengthEval overlapEval
  fun_prop

private theorem boundaryRight_continuous (w : List Bool) : Continuous (boundaryRight w) := by
  unfold boundaryRight denomMomentEval denomEval overlapMomentEval overlapEval
  fun_prop

private theorem tendsto_half_implies_boundaryRight_zero {w : List Bool} (hw : w≠[])
    (hhalf : Tendsto (rho w) atTop (𝓝 (1/2:ℝ))) :
    boundaryRight w (1/growthRate w hw)=0 := by
  have hr := assumed_half_imbalance_ratio_zero hw hhalf
  have hl := (boundaryLeft_continuous w).tendsto (1/growthRate w hw) |>.comp (growthApproach_tendsto hw)
  have hz := hr.mul hl
  simp only [zero_mul] at hz
  have he : (fun t => (seriesEval (realImbalanceSeries w) (growthApproach w hw t)/
        (seriesEval (realLengthSeries w)) (growthApproach w hw t))*boundaryLeft w (growthApproach w hw t))=
      (fun t => boundaryRight w (growthApproach w hw t)) := by
    funext t
    exact moment_ratio_cross hw t
  simp only [Function.comp_def] at hz
  rw [he] at hz
  have hc := (boundaryRight_continuous w).tendsto (1/growthRate w hw) |>.comp (growthApproach_tendsto hw)
  exact (tendsto_nhds_unique hz hc).symm

private theorem tendsto_half_implies_balanced_long {w : List Bool} (hn : 3 ≤ w.length)
    (hhalf : Tendsto (rho w) atTop (𝓝 (1/2:ℝ))) : BalancedBorders w := by
  have hw : w≠[] := by intro h; simp [h] at hn
  by_contra hnb
  have hz := tendsto_half_implies_boundaryRight_zero hw hhalf
  have hQ := growthRadius_denominator_zero hw
  have hT := unbalanced_boundary_moment_ne_zero hn hnb (growthRate_gt_three_halves hn hw)
    (growthRate_lt_two hw) (growthRate_root hw)
  have hrpos : 0 ≤ 1/growthRate w hw := div_nonneg (by norm_num) (Real.exp_pos _).le
  have hR := overlapEval_ge_one hw hrpos
  unfold boundaryRight at hz
  rw [hQ,mul_zero,zero_sub,neg_eq_zero] at hz
  exact hT ((mul_eq_zero.mp hz).resolve_left (by linarith))

private theorem balanced_mixed_pair (b : Bool) : BalancedBorders [b,!b] := by
  rw [balanced_iff_imbalance_zero]
  intro j hj
  cases b
  · simp only [Bool.not_false] at hj ⊢
    have he : borderLengths [false,true]={2} := by decide
    rw [he,Finset.mem_singleton] at hj
    subst j
    simp [imbalance]
  · simp only [Bool.not_true] at hj ⊢
    have he : borderLengths [true,false]={2} := by decide
    rw [he,Finset.mem_singleton] at hj
    subst j
    simp [imbalance]

private theorem not_tendsto_half_00 : ¬ Tendsto (rho [false,false]) atTop (𝓝 (1/2:ℝ)) := by
  have he := flip_tendsto_half_iff (w := [true,true]) (by simp)
  simp only [List.map_cons,List.map_nil,Bool.not_true] at he
  exact fun h => not_tendsto_half_11 (he.mp h)

theorem result : claim := by
  intro w hw
  constructor
  · intro hh
    cases w with
    | nil => exact False.elim (hw rfl)
    | cons b w =>
      cases w with
      | nil => exact False.elim (singleton_not_tendsto_half b hh)
      | cons c w =>
        cases w with
        | nil =>
          cases b <;> cases c
          · exact False.elim (not_tendsto_half_00 hh)
          · exact balanced_mixed_pair false
          · exact balanced_mixed_pair true
          · exact False.elim (not_tendsto_half_11 hh)
        | cons d w => exact tendsto_half_implies_balanced_long (by simp) hh
  · exact balanced_tendsto_half hw

end D5.S1.Words.Forbidden.BonaMagaRicheyHalfFrequency
