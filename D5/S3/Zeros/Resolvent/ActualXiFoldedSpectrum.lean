/- GID: D5/S3/Zeros/Resolvent/ActualXiFoldedSpectrum
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiFoldedSpectrum
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: Fold the actual xi zeros by reflection with their exact complex nodes and weights. -/

import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
import Mathlib.Tactic

/-!
The indices are distinct actual zeros, with their original analytic multiplicities.
Positive height selects one representative of reflection, not of conjugation.
Off-line zeros are retained. These classical spectral coordinates make no
claim of ordinary mathematical originality or unconditional positivity.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
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

theorem node_ne_zero (n : PositiveZero) : node n ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (gamma_ne_zero n))

theorem node_norm (n : PositiveZero) : ‖node n‖ = (‖actualData.gamma n‖ ^ 2)⁻¹ := by
  simp [node, norm_inv, norm_pow]

theorem node_norm_lt_one (n : PositiveZero) : ‖node n‖ < 1 := by
  rw [node_norm]
  exact inv_lt_one_of_one_lt₀ (by nlinarith [gamma_norm_gt_one n])

theorem node_original (n : PositiveZero) :
    node n = -1 / (actualData.zero n - 1 / 2) ^ 2 := by
  have h : (actualData.gamma n) ^ 2 = -(actualData.zero n - 1 / 2) ^ 2 := by
    dsimp [ZeroData.gamma, spectralParameter, D5.S3.Weil.Convention.criticalAbscissa]
    push_cast
    ring_nf
    norm_num [I_sq]
    ring
  rw [node, h]
  simp [div_eq_mul_inv]

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

theorem weight_ne_zero (n : PositiveZero) : weight n ≠ 0 := by
  rw [weight_node]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Nat.cast_ne_zero.mpr (actualData.multiplicity_pos n).ne'))
    (pow_ne_zero _ (node_ne_zero n))) (node_denominator_ne_zero n)

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

theorem node_large_finite (ε : ℝ) (hε : 0 < ε) :
    {n : PositiveZero | ε ≤ ‖node n‖}.Finite := by
  have hf : {n : PositiveZero | ‖actualData.gamma n‖ ≤ 1 / ε + 1}.Finite :=
    (actualData.locallyFinite (1 / ε + 1)).preimage (fun _ _ _ _ h => Subtype.ext h)
  apply hf.subset
  intro n hn
  change ε ≤ ‖node n‖ at hn
  rw [node_norm] at hn
  have hx := gamma_norm_gt_one n
  have hs : 0 < ‖actualData.gamma n‖ ^ 2 := by positivity
  have he : ε * ‖actualData.gamma n‖ ^ 2 ≤ 1 :=
    (le_div_iff₀ hs).mp (by simpa only [one_div] using hn)
  have hi : 0 < 1 / ε := one_div_pos.mpr hε
  have he' : ‖actualData.gamma n‖ ^ 2 ≤ 1 / ε :=
    (le_div_iff₀ hε).mpr (by nlinarith [he])
  change ‖actualData.gamma n‖ ≤ 1 / ε + 1
  nlinarith [sq_nonneg (‖actualData.gamma n‖ - 1)]

end D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
