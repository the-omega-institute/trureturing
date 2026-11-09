/- GID: D5/S3/Zeros/Resolvent/ActualXiDictionary
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiDictionary
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: Actual xi Taylor series normal convergence quantitative remainders and real-polynomial Hankel identity. -/

import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
import Mathlib.Tactic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-!
The indices are distinct actual zeros, with their original analytic multiplicities.
Positive height selects one representative of reflection, not of conjugation.
Off-line zeros are retained. These classical spectral coordinates make no
claim of ordinary mathematical originality or unconditional positivity.
-/
namespace D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum

open Complex D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open scoped ComplexConjugate

abbrev PositiveZero := {n : ℕ // 0 < (actualData.zero n).im}

def node (n : PositiveZero) : ℂ := ((actualData.gamma n) ^ 2)⁻¹

def weight (n : PositiveZero) : ℂ :=
  2 * ((actualData.multiplicity n : ℂ) *
    (1 / (actualData.zero n * (1 - actualData.zero n)))) * node n

theorem gamma_re (n : ℕ) : (actualData.gamma n).re = (actualData.zero n).im := by
  simp [ZeroData.gamma, spectralParameter, D5.S3.Weil.Convention.criticalAbscissa]

theorem gamma_norm_gt_one (n : ℕ) : 1 < ‖actualData.gamma n‖ := by
  have h := actual_ordinate_sq_gt_one n
  have hs := Complex.sq_norm_sub_sq_re (actualData.gamma n)
  rw [gamma_re] at hs
  nlinarith [norm_nonneg (actualData.gamma n), sq_nonneg (actualData.gamma n).im]

theorem gamma_ne_zero (n : ℕ) : actualData.gamma n ≠ 0 := by
  intro h
  have hn := gamma_norm_gt_one n
  rw [h, norm_zero] at hn
  norm_num at hn

theorem node_norm (n : PositiveZero) : ‖node n‖ = (‖actualData.gamma n‖ ^ 2)⁻¹ := by
  simp [node, norm_inv, norm_pow]

theorem node_norm_lt_one (n : PositiveZero) : ‖node n‖ < 1 := by
  rw [node_norm]
  exact inv_lt_one_of_one_lt₀ (by nlinarith [gamma_norm_gt_one n])

def tau (n : PositiveZero) : PositiveZero :=
  ⟨actualData.reflection (actualData.conjugation n), by
    rw [actualData.zero_reflection, actualData.zero_conjugation]
    simpa using n.property⟩

theorem gamma_tau (n : PositiveZero) :
    actualData.gamma (tau n) = conj (actualData.gamma n) := by
  simp [tau]

theorem tau_involutive : Function.Involutive tau := by
  intro n
  apply Subtype.ext
  apply actualData.zero_injective
  simp only [tau, actualData.zero_reflection, actualData.zero_conjugation,
    map_sub, map_one, Complex.conj_conj]
  ring

def conjugation : Equiv.Perm PositiveZero := tau_involutive.toPerm tau

theorem node_conjugation (n : PositiveZero) : node (conjugation n) = conj (node n) := by
  change ((actualData.gamma (tau n)) ^ 2)⁻¹ = _
  simp [gamma_tau, node]

theorem multiplicity_conjugation (n : PositiveZero) :
    actualData.multiplicity (conjugation n) = actualData.multiplicity n := by
  change actualData.multiplicity (actualData.reflection (actualData.conjugation n)) = _
  rw [actualData.multiplicity_reflection, actualData.multiplicity_conjugation]

theorem weight_conjugation (n : PositiveZero) :
    weight (conjugation n) = conj (weight n) := by
  have hz : actualData.zero (conjugation n) = 1 - conj (actualData.zero n) := by
    change actualData.zero (actualData.reflection (actualData.conjugation n)) = _
    rw [actualData.zero_reflection, actualData.zero_conjugation]
  simp only [weight, node_conjugation, multiplicity_conjugation, hz]
  have htwo : conj (2 : ℂ) = 2 := by
    change conj ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ)
    exact Complex.conj_ofReal 2
  norm_num
  exact Or.inl (by rw [htwo]; ring)

theorem node_injective : Function.Injective node := by
  intro n k h
  have hs : (actualData.gamma n) ^ 2 = (actualData.gamma k) ^ 2 := inv_injective h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hp | hm
  · apply Subtype.ext
    apply actualData.zero_injective
    rw [actualData.zero_eq_critical_add_I_mul_gamma n,
      actualData.zero_eq_critical_add_I_mul_gamma k, hp]
  · have hr := congrArg Complex.re hm
    rw [Complex.neg_re, gamma_re, gamma_re] at hr
    linarith [n.property, k.property]

theorem node_real_iff (n : PositiveZero) :
    (node n).im = 0 ↔ (actualData.zero n).re = 1 / 2 := by
  have hc : (node n).im = 0 ↔ conj (node n) = node n := by
    constructor
    · intro h; apply Complex.ext <;> simp [h]
    · intro h; have hi := congrArg Complex.im h; simp only [Complex.conj_im] at hi; linarith
  rw [hc, ← node_conjugation, node_injective.eq_iff]
  constructor
  · intro h
    have hz := congrArg (fun k : PositiveZero => (actualData.zero k).re) h
    change (actualData.zero (actualData.reflection (actualData.conjugation n))).re = _ at hz
    rw [actualData.zero_reflection, actualData.zero_conjugation] at hz
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hz
    linarith
  · intro h
    apply Subtype.ext
    apply actualData.zero_injective
    change actualData.zero (actualData.reflection (actualData.conjugation n)) = _
    rw [actualData.zero_reflection, actualData.zero_conjugation]
    apply Complex.ext <;> simp [h] <;> ring

theorem node_denominator_ne_zero (n : PositiveZero) : 1 + node n / 4 ≠ 0 := by
  intro h
  have he : node n = -4 := by linear_combination 4 * h
  have hn := node_norm_lt_one n
  rw [he] at hn
  norm_num at hn

theorem pair_weight_node (n : PositiveZero) :
    1 / (actualData.zero n * (1 - actualData.zero n)) = node n / (1 + node n / 4) := by
  have hg := gamma_ne_zero n
  have hz : actualData.zero n * (1 - actualData.zero n) =
      1 / 4 + (actualData.gamma n) ^ 2 := by
    rw [actualData.zero_eq_critical_add_I_mul_gamma]
    dsimp [D5.S3.Weil.Convention.criticalAbscissa]
    ring_nf
    simp [I_sq]
    ring
  rw [hz]
  dsimp [node]
  field_simp
  <;> ring

theorem weight_node (n : PositiveZero) :
    weight n = 2 * (actualData.multiplicity n : ℂ) * node n ^ 2 / (1 + node n / 4) := by
  rw [weight, pair_weight_node]
  ring

theorem weight_norm_summable : Summable (fun n : PositiveZero => ‖weight n‖) := by
  have hs := actual_complex_pairWeight_hasSum.summable.norm.subtype
    (fun n => 0 < (actualData.zero n).im)
  apply (hs.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [weight, norm_mul, norm_mul, norm_ofNat]
  exact mul_le_of_le_one_right (by positivity) (node_norm_lt_one n).le

theorem node_real_positive (n : PositiveZero) (h : (node n).im = 0) :
    0 < (node n).re ∧ 0 < (weight n).re ∧ (weight n).im = 0 := by
  have hx := (node_real_iff n).mp h
  have hg : actualData.gamma n = ((actualData.zero n).im : ℂ) := by
    apply Complex.ext <;>
      simp [ZeroData.gamma, spectralParameter, D5.S3.Weil.Convention.criticalAbscissa, hx]
  have hn : node n = (((actualData.zero n).im ^ 2)⁻¹ : ℝ) := by
    simp [node, hg]
  have hp : 0 < ((actualData.zero n).im ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos n.property)
  have hw : weight n = ((2 * (actualData.multiplicity n : ℝ) *
      (((actualData.zero n).im ^ 2)⁻¹) ^ 2 /
        (1 + ((actualData.zero n).im ^ 2)⁻¹ / 4) : ℝ) : ℂ) := by
    rw [weight_node, hn]
    push_cast
    rfl
  rw [hn, hw]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨hp, by have hm := actualData.multiplicity_pos n; positivity, trivial⟩

end D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum

/-!
The left side is defined from the original xiReading and real firstLiMass.
Only convergent normalized sums are subtracted. The square-source product
and reflection proofs are reused, and the center is treated without dividing
by the spectral variable. No RH or positivity premise is used.
-/
namespace D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open Complex Filter D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open scoped Topology ComplexConjugate

/-- The actual xi expression, independently of every zero sum. -/
def xiOdd (w : ℂ) : ℂ :=
  (I * logDeriv xiReading ((1 / 2 : ℂ) - I * w) - (firstLiMass : ℂ) * w) /
    (w ^ 2 + 1 / 4)

private theorem reflection_fold_hasSum (f : ℕ → ℂ) (a : ℂ)
    (hf : HasSum f a) (hr : ∀ n, f (actualData.reflection n) = f n) :
    HasSum (fun n : PositiveZero => 2 * f n) a := by
  classical
  let p : ℕ → ℂ := {n | 0 < (actualData.zero n).im}.indicator f
  have hp : Summable p := hf.summable.indicator _
  have hpr := actualData.reflection.hasSum_iff.mpr hp.hasSum
  have hpair (n : ℕ) : f n = p n + p (actualData.reflection n) := by
    have hn : (actualData.zero n).im ≠ 0 := by
      intro hz
      have h := actual_ordinate_sq_gt_one n
      rw [hz] at h
      norm_num at h
    dsimp [p, Set.indicator]
    simp only [actualData.zero_reflection, Complex.sub_im, Complex.one_im, zero_sub, hr]
    by_cases h : 0 < (actualData.zero n).im
    · rw [if_pos h, if_neg (by linarith), add_zero]
    · rw [if_neg h, if_pos (by rcases lt_or_gt_of_ne hn with h | h <;> linarith), zero_add]
  have he : (2 : ℂ) * (∑' n, p n) = a := by
    simpa only [two_mul] using ((hp.hasSum.add hpr).congr_fun hpair).unique hf
  have hs : HasSum (fun n => 2 * p n) a := he ▸ hp.hasSum.mul_left 2
  apply (hasSum_subtype_iff_indicator (s := {n : ℕ | 0 < (actualData.zero n).im})
    (f := fun n => 2 * f n)).mpr
  convert hs using 1
  funext n
  by_cases h : 0 < (actualData.zero n).im <;> simp [p, h]

theorem folded_mass_hasSum :
    HasSum (fun n : PositiveZero => 2 * (actualData.multiplicity n : ℂ) *
      (1 / (actualData.zero n * (1 - actualData.zero n)))) (firstLiMass : ℂ) := by
  have h := reflection_fold_hasSum _ _ actual_complex_pairWeight_hasSum (fun n => by
    rw [actualData.multiplicity_reflection, actualData.zero_reflection]
    congr 2 <;> ring)
  convert h using 1
  funext n
  ring

private theorem xi_disk_nonzero (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    xiReading ((1 / 2 : ℂ) + I * w) ≠ 0 := by
  intro hz
  have hz' := (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
    _).mp hz
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hz'
  have hlow := actual_ordinate_sq_gt_one n
  have hi := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, zero_add, one_mul] at hi
  norm_num at hi
  rw [hi] at hlow
  have hs := Complex.sq_norm_sub_sq_re w
  nlinarith [norm_nonneg w, sq_nonneg w.im]

private theorem square_disk_nonzero (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    xiSquareSource (w ^ 2) ≠ 0 := by
  rw [xi_square_source_entire_and_composition.2]
  exact div_ne_zero (xi_disk_nonzero w hw) (by
    have h := xi_disk_nonzero 0 (by norm_num)
    simpa using h)

theorem xiOdd_square (w : ℂ) :
    xiOdd w = w * (-2 * logDeriv xiSquareSource (w ^ 2) - firstLiMass) /
      (w ^ 2 + 1 / 4) := by
  have hc := xi_square_logDeriv_composition w
  have hr : logDeriv xiReading ((1 / 2 : ℂ) - I * w) =
      -logDeriv xiReading ((1 / 2 : ℂ) + I * w) := by
    rw [show (1 / 2 : ℂ) - I * w = 1 - ((1 / 2 : ℂ) + I * w) by ring]
    exact xi_logDeriv_reflection _
  unfold xiOdd
  rw [hr]
  congr 1
  linear_combination hc

theorem disk_denominator_ne_zero (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    w ^ 2 + 1 / 4 ≠ 0 := by
  intro h
  have he : w ^ 2 = -(1 / 4 : ℂ) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg norm he
  simp only [norm_pow, norm_neg, norm_div, norm_one, norm_ofNat] at hn
  nlinarith [norm_nonneg w]

theorem resolvent_denominator_ne_zero (n : PositiveZero) (w : ℂ) (hw : ‖w‖ < 1) :
    1 - node n * w ^ 2 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn := congrArg norm h
  rw [norm_one, norm_mul, norm_pow] at hn
  have hx := node_norm_lt_one n
  have hp : ‖node n‖ * ‖w‖ ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_right hx.le (sq_nonneg ‖w‖)).trans_lt
      (by nlinarith [norm_nonneg w])
  linarith

/-- The complete, multiplicity-faithful actual xi folded resolvent, including zero. -/
theorem actual_xi_folded_hasSum (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    HasSum (fun n : PositiveZero => w * weight n / (1 - node n * w ^ 2)) (xiOdd w) := by
  classical
  by_cases hw0 : w = 0
  · subst w
    rw [xiOdd_square]
    simp
  have hF := square_disk_nonzero w hw
  have ha := actual_positive_square_resolvent_hasSum actualData w hw0 hF
  have hs : HasSum (fun n : PositiveZero =>
      (actualData.multiplicity n : ℂ) / (w ^ 2 - (actualData.gamma n) ^ 2))
      (logDeriv xiSquareSource (w ^ 2)) := by
    apply (hasSum_subtype_iff_indicator (s := {n : ℕ | 0 < (actualData.zero n).im})
      (f := fun n => (actualData.multiplicity n : ℂ) /
        (w ^ 2 - (actualData.gamma n) ^ 2))).mpr
    convert ha using 1
    funext n
    simp [positiveSquareResolvent, gamma_re, Set.indicator]
  have hd := disk_denominator_ne_zero w hw
  have h := (((hs.mul_left (-2)).sub folded_mass_hasSum).div_const
    (w ^ 2 + 1 / 4)).mul_left w
  rw [xiOdd_square]
  convert h.congr_fun (fun n => ?_) using 1
  · ring
  · have hg := gamma_ne_zero n
    have hg2 := pow_ne_zero 2 hg
    have hn := node_denominator_ne_zero n
    have hr := resolvent_denominator_ne_zero n w (by linarith)
    have hden : w ^ 2 - (actualData.gamma n) ^ 2 ≠ 0 := by
      intro hzero
      apply hr
      rw [sub_eq_zero.mp hzero]
      simp [node, hg2]
    have hgl : (actualData.gamma n) ^ 2 * node n = 1 := by simp [node, hg2]
    have hres : (actualData.multiplicity n : ℂ) /
        (w ^ 2 - (actualData.gamma n) ^ 2) =
        -((actualData.multiplicity n : ℂ) * node n) / (1 - node n * w ^ 2) := by
      apply (div_eq_div_iff hden hr).mpr
      linear_combination -(actualData.multiplicity n : ℂ) * hgl
    rw [weight_node, pair_weight_node, hres]
    conv_rhs => rw [← mul_div_assoc]
    apply (div_eq_div_iff hr hd).mpr
    have hn4 : (4 : ℂ) + node n ≠ 0 := by
      intro he
      apply hn
      linear_combination (1 / 4 : ℂ) * he
    have hr' : 1 - w ^ 2 * node n ≠ 0 := by simpa [mul_comm] using hr
    field_simp [hn, hr, hn4, hr']
    ring

end D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent

/-!
All sums are over distinct actual positive-height zeros with analytic multiplicity
in the weights. The full Taylor identification is for the independently defined
xiOdd, not a function defined by the series. The complex square in the subsequent
Hankel identity is not a modulus square. No ordinary novelty is claimed.
-/
namespace D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
open Complex Filter Finset
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open scoped Topology ComplexConjugate

def totalWeight : ℝ := ∑' n : PositiveZero, ‖weight n‖

def radius : ℝ := sSup (insert 0 (Set.range (fun n : PositiveZero => ‖node n‖)))

private theorem radius_bdd : BddAbove (insert 0 (Set.range (fun n : PositiveZero => ‖node n‖))) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨n, rfl⟩)
  · norm_num
  · exact (node_norm_lt_one n).le

theorem radius_bounds : 0 ≤ radius ∧ radius ≤ 1 := by
  constructor
  · exact le_csSup radius_bdd (Set.mem_insert 0 _)
  · apply csSup_le (Set.insert_nonempty _ _)
    rintro x (rfl | ⟨n, rfl⟩)
    · norm_num
    · exact (node_norm_lt_one n).le

theorem node_norm_le_radius (n : PositiveZero) : ‖node n‖ ≤ radius :=
  le_csSup radius_bdd (Set.mem_insert_of_mem _ ⟨n, rfl⟩)

def moment (j : ℕ) : ℂ := ∑' n : PositiveZero, weight n * node n ^ j

theorem moment_summable (j : ℕ) : Summable (fun n : PositiveZero => weight n * node n ^ j) := by
  apply (weight_norm_summable.mul_right (radius ^ j)).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (node_norm_le_radius n) _)
    (norm_nonneg _)

theorem moment_bound (j : ℕ) : ‖moment j‖ ≤ totalWeight * radius ^ j := by
  apply tsum_of_norm_bounded ((weight_norm_summable.hasSum).mul_right (radius ^ j))
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (node_norm_le_radius n) _)
    (norm_nonneg _)

theorem moment_real (j : ℕ) : (moment j).im = 0 := by
  have hc : conj (moment j) = moment j := by
    rw [moment, Complex.conj_tsum]
    calc
      (∑' n : PositiveZero, conj (weight n * node n ^ j)) =
          ∑' n : PositiveZero, weight (conjugation n) * node (conjugation n) ^ j := by
        apply tsum_congr
        intro n
        simp [weight_conjugation, node_conjugation]
      _ = moment j := by
        simpa only [moment] using
          conjugation.tsum_eq (fun n : PositiveZero => weight n * node n ^ j)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

private theorem moment_bound_mass (j : ℕ) : ‖moment j‖ ≤ totalWeight := by
  calc
    ‖moment j‖ ≤ totalWeight * radius ^ j := moment_bound j
    _ ≤ totalWeight * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ radius_bounds.1 radius_bounds.2) (tsum_nonneg (fun _ => norm_nonneg _))
    _ = totalWeight := mul_one _

private theorem double_summable (w : ℂ) (hw : ‖w‖ < 1) :
    Summable (fun p : PositiveZero × ℕ => weight p.1 * node p.1 ^ p.2 * w ^ (2 * p.2 + 1)) := by
  have hq : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  have hs := (weight_norm_summable.mul_right ‖w‖).mul_of_nonneg
    (hasSum_geometric_of_lt_one (sq_nonneg ‖w‖) hq).summable
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun j => pow_nonneg (sq_nonneg _) j)
  apply hs.of_norm_bounded
  intro p
  simp only [norm_mul, norm_pow]
  have hn : ‖node p.1‖ ^ p.2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (node_norm_lt_one _).le
  calc
    ‖weight p.1‖ * ‖node p.1‖ ^ p.2 * ‖w‖ ^ (2 * p.2 + 1) ≤
        ‖weight p.1‖ * 1 * ‖w‖ ^ (2 * p.2 + 1) := by gcongr
    _ = (‖weight p.1‖ * ‖w‖) * (‖w‖ ^ 2) ^ p.2 := by rw [pow_add, pow_mul]; ring

/-- Full odd-power expansion, with absolute double summability justifying the exchange. -/
theorem actual_xi_moment_hasSum (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    HasSum (fun j : ℕ => moment j * w ^ (2 * j + 1)) (xiOdd w) := by
  have hp := double_summable w (by linarith)
  have hrow (n : PositiveZero) : HasSum
      (fun j : ℕ => weight n * node n ^ j * w ^ (2 * j + 1))
      (w * weight n / (1 - node n * w ^ 2)) := by
    have hnorm : ‖node n * w ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact (mul_le_mul_of_nonneg_right (node_norm_lt_one n).le (sq_nonneg ‖w‖)).trans_lt
        (by nlinarith [norm_nonneg w])
    convert (hasSum_geometric_of_norm_lt_one hnorm).mul_left (w * weight n) using 1
    · funext j
      rw [mul_pow, pow_add, pow_mul]
      ring
    · simp [div_eq_mul_inv]
  have he : (∑' j : ℕ, moment j * w ^ (2 * j + 1)) = xiOdd w := by
    simp_rw [moment, ← tsum_mul_right]
    rw [Summable.tsum_comm (f := fun (n : PositiveZero) (j : ℕ) =>
      weight n * node n ^ j * w ^ (2 * j + 1)) hp]
    simp_rw [(hrow _).tsum_eq]
    exact (actual_xi_folded_hasSum w hw).tsum_eq
  rw [← he]
  apply Summable.hasSum
  convert hp.prod_symm.prod using 1
  funext j
  exact (tsum_mul_right).symm

/-- All even coefficients are zero; odd coefficients are the convergent actual moments. -/
def coefficient (k : ℕ) : ℂ := if k % 2 = 1 then moment (k / 2) else 0

private theorem coefficient_odd (j : ℕ) : coefficient (2 * j + 1) = moment j := by
  simp [coefficient, show (2 * j + 1) / 2 = j by omega]

private theorem coefficient_bound (k : ℕ) : ‖coefficient k‖ ≤ totalWeight := by
  unfold coefficient
  split_ifs
  · exact moment_bound_mass _
  · simpa only [norm_zero, totalWeight] using
      (tsum_nonneg (fun n : PositiveZero => norm_nonneg (weight n)))

/-- The genuine xi expression has this full scalar power series on the specified disk. -/
theorem actual_xi_powerSeries : HasFPowerSeriesOnBall xiOdd
    (FormalMultilinearSeries.ofScalars ℂ coefficient) 0 (ENNReal.ofReal (1 / 4)) := by
  constructor
  · apply le_trans (show ENNReal.ofReal (1 / 4) ≤ (1 : ENNReal) by norm_num)
    apply FormalMultilinearSeries.le_radius_of_bound _ totalWeight (r := 1)
    intro k
    simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
      using coefficient_bound k
  · norm_num
  · intro w hw
    have hnorm : ‖w‖ < 1 / 4 := by
      simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
        ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)] using hw
    have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
      intro a b h
      dsimp at h
      omega
    have hout : ∀ k : ℕ, k ∉ Set.range (fun j : ℕ => 2 * j + 1) →
        coefficient k * w ^ k = 0 := by
      intro k hk
      have hmod : k % 2 ≠ 1 := by
        intro h
        apply hk
        refine ⟨k / 2, ?_⟩
        dsimp
        omega
      simp [coefficient, hmod]
    have h := (hi.hasSum_iff hout).mp
      ((actual_xi_moment_hasSum w hnorm).congr_fun (fun j => by
        simp only [Function.comp_apply, coefficient_odd]))
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using h

/-- The analytic Taylor coefficient is identified with the actual moment, at every order. -/
theorem actual_xi_coefficient_derivative (k : ℕ) :
    coefficient k = iteratedDeriv k xiOdd 0 / (k.factorial : ℂ) := by
  have h := actual_xi_powerSeries.factorial_smul (1 : ℂ) k
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    nsmul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv] at h
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero k)).mpr
  simpa [mul_comm] using h

theorem actual_xi_taylor_moment (j : ℕ) :
    iteratedDeriv (2 * j + 1) xiOdd 0 / ((2 * j + 1).factorial : ℂ) = moment j := by
  rw [← actual_xi_coefficient_derivative, coefficient_odd]

end D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary

/-! Uniform absolute majorants and geometric remainders for the actual xi dictionary. -/
namespace D5.S3.Zeros.Resolvent.ActualXiTaylorBounds
open Complex Filter Finset
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
open scoped Topology

private theorem ratio_bounds (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4) :
    0 ≤ radius * r ^ 2 ∧ radius * r ^ 2 < 1 := by
  have hΛ := radius_bounds.1
  have h := mul_le_mul_of_nonneg_right radius_bounds.2 (sq_nonneg r)
  constructor
  · positivity
  · nlinarith

private theorem power_term_bound (r : ℝ) (hr : 0 ≤ r) (w : ℂ) (hw : ‖w‖ ≤ r) (j : ℕ) :
    ‖moment j * w ^ (2 * j + 1)‖ ≤ totalWeight * r * (radius * r ^ 2) ^ j := by
  have hW : 0 ≤ totalWeight := tsum_nonneg (fun _ => norm_nonneg _)
  have hΛ := radius_bounds.1
  rw [norm_mul, norm_pow]
  calc
    ‖moment j‖ * ‖w‖ ^ (2 * j + 1) ≤
        (totalWeight * radius ^ j) * r ^ (2 * j + 1) := by
      gcongr
      exact moment_bound j
    _ = totalWeight * r * (radius * r ^ 2) ^ j := by rw [mul_pow, pow_add, pow_mul]; ring

private theorem folded_term_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (w : ℂ) (hw : ‖w‖ ≤ r) (n : PositiveZero) :
    ‖w * weight n / (1 - node n * w ^ 2)‖ ≤
      ‖weight n‖ * r / (1 - radius * r ^ 2) := by
  have hΛ := radius_bounds.1
  have hq := ratio_bounds r hr hr1
  have hd : 1 - radius * r ^ 2 ≤ ‖1 - node n * w ^ 2‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (node n * w ^ 2)
    rw [norm_one, norm_mul, norm_pow] at ht
    have hm : ‖node n‖ * ‖w‖ ^ 2 ≤ radius * r ^ 2 := by
      gcongr
      exact node_norm_le_radius n
    linarith
  rw [norm_div, norm_mul]
  calc
    ‖w‖ * ‖weight n‖ / ‖1 - node n * w ^ 2‖ ≤
        r * ‖weight n‖ / (1 - radius * r ^ 2) := by
      apply div_le_div₀ (by positivity) (by gcongr) (by linarith) hd
    _ = ‖weight n‖ * r / (1 - radius * r ^ 2) := by ring

/-- A summable majorant on every closed subdisk proves normal folded convergence. -/
theorem actual_xi_folded_normal (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4) :
    Summable (fun n : PositiveZero => ‖weight n‖ * r / (1 - radius * r ^ 2)) ∧
    HasSumUniformlyOn (fun n : PositiveZero => fun w : ℂ =>
      w * weight n / (1 - node n * w ^ 2)) xiOdd (Metric.closedBall 0 r) := by
  have hs := (weight_norm_summable.mul_right r).div_const (1 - radius * r ^ 2)
  refine ⟨hs, ?_⟩
  have hu := HasSumUniformlyOn.of_norm_le_summable (s := Metric.closedBall (0 : ℂ) r)
    hs (fun n w hw =>
    folded_term_bound r hr hr1 w (by simpa using hw) n)
  apply hu.congr_right (fun w hw => ?_)
  exact (actual_xi_folded_hasSum w ((show ‖w‖ ≤ r by simpa using hw).trans_lt hr1)).tsum_eq

/-- Compact-disk bound using the actual supremum of the folded node norms. -/
theorem actual_xi_disk_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (w : ℂ) (hw : ‖w‖ ≤ r) :
    ‖xiOdd w‖ ≤ totalWeight * r / (1 - radius * r ^ 2) := by
  have hs := (weight_norm_summable.hasSum.mul_right r).div_const (1 - radius * r ^ 2)
  exact (actual_xi_folded_hasSum w (hw.trans_lt hr1)).norm_le_of_bounded hs
    (fun n => folded_term_bound r hr hr1 w hw n)

/-- The actual moment series also converges normally on each closed subdisk. -/
theorem actual_xi_taylor_normal (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4) :
    Summable (fun j : ℕ => totalWeight * r * (radius * r ^ 2) ^ j) ∧
    HasSumUniformlyOn (fun j : ℕ => fun w : ℂ => moment j * w ^ (2 * j + 1))
      xiOdd (Metric.closedBall 0 r) := by
  have hq := ratio_bounds r hr hr1
  have hs := (hasSum_geometric_of_lt_one hq.1 hq.2).summable.mul_left (totalWeight * r)
  refine ⟨hs, ?_⟩
  have hu := HasSumUniformlyOn.of_norm_le_summable (s := Metric.closedBall (0 : ℂ) r) hs
    (fun j w hw => power_term_bound r hr w (by simpa using hw) j)
  apply hu.congr_right (fun w hw => ?_)
  exact (actual_xi_moment_hasSum w ((show ‖w‖ ≤ r by simpa using hw).trans_lt hr1)).tsum_eq

/-- Uniform geometric remainder after the odd terms through index J. -/
theorem actual_xi_taylor_remainder (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 4)
    (w : ℂ) (hw : ‖w‖ ≤ r) (J : ℕ) :
    ‖xiOdd w - ∑ j ∈ range (J + 1), moment j * w ^ (2 * j + 1)‖ ≤
      totalWeight * r * (radius * r ^ 2) ^ (J + 1) / (1 - radius * r ^ 2) := by
  have hq := ratio_bounds r hr hr1
  have hs := (actual_xi_moment_hasSum w (hw.trans_lt hr1)).summable
  have he := hs.sum_add_tsum_nat_add (J + 1)
  rw [(actual_xi_moment_hasSum w (hw.trans_lt hr1)).tsum_eq] at he
  have he' : xiOdd w - ∑ j ∈ range (J + 1), moment j * w ^ (2 * j + 1) =
      ∑' j : ℕ, moment (j + (J + 1)) * w ^ (2 * (j + (J + 1)) + 1) := by
    linear_combination -he
  rw [he']
  have hgeom := (hasSum_geometric_of_lt_one hq.1 hq.2).mul_left
    (totalWeight * r * (radius * r ^ 2) ^ (J + 1))
  have hval : totalWeight * r * (radius * r ^ 2) ^ (J + 1) * (1 - radius * r ^ 2)⁻¹ =
      totalWeight * r * (radius * r ^ 2) ^ (J + 1) / (1 - radius * r ^ 2) := by rfl
  rw [hval] at hgeom
  apply tsum_of_norm_bounded hgeom
  intro j
  calc
    ‖moment (j + (J + 1)) * w ^ (2 * (j + (J + 1)) + 1)‖ ≤
        totalWeight * r * (radius * r ^ 2) ^ (j + (J + 1)) := power_term_bound r hr w hw _
    _ = totalWeight * r * (radius * r ^ 2) ^ (J + 1) * (radius * r ^ 2) ^ j := by
      rw [pow_add]; ring

end D5.S3.Zeros.Resolvent.ActualXiTaylorBounds

/-!
The coefficients on the left are derivatives of the original xi expression.
The right side uses a complex square, never a modulus square. Nonnegativity
requires the explicitly stated Riemann hypothesis. Spectral powers do not
assert any physical-space moment condition. Distinct off-line conjugate pairs,
not analytic multiplicities, are the folded negative-index counting objects;
no negative-index theorem is asserted here.
-/
namespace D5.S3.Zeros.Resolvent.ActualXiHankelDictionary
open Complex Finset
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary

/-- Real Taylor coefficients of the independently defined actual xi function. -/
def xiCoefficient (j : ℕ) : ℝ :=
  (iteratedDeriv (2 * j + 1) xiOdd 0 / ((2 * j + 1).factorial : ℂ)).re

private theorem xiCoefficient_eq (j : ℕ) : (xiCoefficient j : ℂ) = moment j := by
  apply Complex.ext
  · simp only [Complex.ofReal_re, xiCoefficient, actual_xi_taylor_moment]
  · simp only [Complex.ofReal_im, moment_real]

private theorem finite_square (N m : ℕ) (u : Fin (N + 1) → ℝ) (n : PositiveZero) :
    weight n * (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2 =
      ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        ((u a : ℂ) * (u b : ℂ)) * (weight n * node n ^ (2 * m + (a : ℕ) + (b : ℕ))) := by
  rw [pow_two]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  simp only [pow_add, pow_mul]
  ring

private theorem hankel_hasSum (N m : ℕ) (u : Fin (N + 1) → ℝ) :
    HasSum (fun n : PositiveZero => weight n *
      (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2)
      (∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
        ((u a : ℂ) * (u b : ℂ)) * moment (2 * m + (a : ℕ) + (b : ℕ))) := by
  have h := hasSum_sum (s := (univ : Finset (Fin (N + 1)))) (fun a _ =>
    hasSum_sum (s := (univ : Finset (Fin (N + 1)))) (fun b _ =>
      ((moment_summable (2 * m + (a : ℕ) + (b : ℕ))).hasSum).mul_left
        ((u a : ℂ) * (u b : ℂ))))
  exact h.congr_fun (finite_square N m u)

/-- The full finite real-polynomial dictionary, with its essential complex square. -/
theorem actual_xi_hankel_identity (N m : ℕ) (u : Fin (N + 1) → ℝ) :
    (∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      u a * u b * xiCoefficient (2 * m + (a : ℕ) + (b : ℕ))) =
    (∑' n : PositiveZero, weight n *
      (node n ^ m * ∑ a : Fin (N + 1), (u a : ℂ) * node n ^ (a : ℕ)) ^ 2).re := by
  rw [(hankel_hasSum N m u).tsum_eq]
  simp_rw [← xiCoefficient_eq]
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    ]

/-- Under RH only, the same actual derivative Hankel form is nonnegative. -/
theorem actual_xi_hankel_nonnegative_of_rh (hRH : RiemannHypothesis)
    (N m : ℕ) (u : Fin (N + 1) → ℝ) :
    0 ≤ ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
      u a * u b * xiCoefficient (2 * m + (a : ℕ) + (b : ℕ)) := by
  rw [actual_xi_hankel_identity]
  rw [Complex.re_tsum (hankel_hasSum N m u).summable]
  apply tsum_nonneg
  intro n
  have hz := actualData.zero_isNontrivial n
  have hx : (actualData.zero n).re = 1 / 2 := by
    apply hRH _ hz.1
    · rintro ⟨k, hk⟩
      have hi := congrArg Complex.im hk
      norm_num at hi
      linarith [n.property]
    · intro h
      have h1 := congrArg Complex.re h
      norm_num at h1
      linarith [hz.2.2]
  have hn := (node_real_iff n).mpr hx
  have hp := node_real_positive n hn
  have he : node n = ((node n).re : ℂ) := by
    apply Complex.ext <;> simp [hn]
  have hw : weight n = ((weight n).re : ℂ) := by
    apply Complex.ext <;> simp [hp.2.2]
  rw [he, hw]
  have hpoly : (∑ a : Fin (N + 1), (u a : ℂ) * ((node n).re : ℂ) ^ (a : ℕ)) =
      ((∑ a : Fin (N + 1), u a * (node n).re ^ (a : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hpoly]
  norm_cast
  exact mul_nonneg hp.2.1.le (sq_nonneg _)

end D5.S3.Zeros.Resolvent.ActualXiHankelDictionary
