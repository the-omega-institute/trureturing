/- GID: D5/S3/Weil/ZetaBridge/ActualFullSymbolTail
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualFullSymbolTail
   mirror-E: none(waiver:general-analytic-identity-and-tail-estimate)
   anchors: []
   utility: none
   digest: Actual first-moment, signed mixed and full arithmetic-symbol tails with both first-jet signs. -/

/-
SOURCE_ONLY_UNCOMPILED. This source candidate is not an accepted Lean result.
The pinned imports and intended public statements are preserved; concrete
hosted diagnostics and signed-sum binding are repaired below.
The companion Reg source attempts select existing absolute-value/norm function
operands; they introduce no mathematical declarations in this D5 module.
Elaboration, kernel and axiom checks, compiled source selection, registration
assessment, scoped reports, Scribe emission, required CI and delivery are pending.

Utility classification: none. Every declaration, including private helpers,
is a parameterized sum definition, phase identity, geometric or signed Abel
estimate, smooth-weight comparison, absolute-convergence argument, square-tail
estimate or first-jet pairing identity. The cutoffs, block starts and lengths,
complex coefficients, finite head sets and coefficient functions remain arbitrary;
the tails range over all natural indices, with c=2 and zero-length blocks retained.
No declaration supplies bounded enumeration, checker/reflection infrastructure,
numerical-certificate reduction or a certified fixed instance. Other utility
fields are not-applicable(kind=none). Generality I records specialization to the
actual arithmetic symbol independently of utility classification.

All prime powers, the actual pole and Gamma terms, both head moments, both
exterior signs, and the exact constants remain present. No signed arithmetic-form
positivity, physical operator identification, RH or Robin conclusion is claimed.
-/
import D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
import D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
import D5.S3.Weil.ZetaBridge.ActualColumnRemainder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
open scoped BigOperators Topology
open Filter
open D5.S3.Weil.ZetaBridge.ActualColumnRemainder
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram

/-- Every q in [2,c), including every prime power, contributes its actual phase.
The denominator is proved nonzero in the consumed first-moment argument. -/
def primeFirstMoment (c : ℕ) : ℝ :=
  ∑ q ∈ primeIndices c, 2 * |primeWeight q| / ‖1 - primePhase c q‖

/-- The exact refined full-symbol budget; the mixed term is paid twice. -/
def fullSymbolTailBudget (c N : ℕ) : ℝ :=
  PrimeSymbolResonance.tailBudget c N + smoothEnvelope c N ^ 2 / (N : ℝ) +
    2 * primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2

private theorem firstMoment_nonneg (c : ℕ) : 0 ≤ primeFirstMoment c :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (by positivity) (norm_nonneg _))

private theorem actual_phase_ne_one {c q : ℕ} (hc : 2 ≤ c)
    (hq : q ∈ primeIndices c) : primePhase c q ≠ 1 := by
  obtain ⟨hlo, hhi⟩ := phase_geometry hc hq
  have ha : 0 < 2 * Real.pi * theta c q := mul_pos (by positivity) hlo
  have hb : 2 * Real.pi * theta c q < 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hd : |2 * Real.pi * theta c q - 0| < 2 * Real.pi := by
    simpa only [sub_zero, abs_of_pos ha] using hb
  have hz : circleMap (0 : ℂ) 1 0 = 1 := by simp [circleMap]
  intro h
  have he : 2 * Real.pi * theta c q = 0 :=
    eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0) hd
      (show circleMap (0 : ℂ) 1 (2 * Real.pi * theta c q) = circleMap 0 1 0 from
        h.trans hz.symm)
  linarith

private theorem im_sum (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ q ∈ s, f q).im = ∑ q ∈ s, (f q).im :=
  map_sum Complex.imAddGroupHom f s

/-- Actual first-moment block bound. Its start is arbitrary, k=0 is allowed,
and the phase denominators follow from 0<theta<1 rather than a spacing premise. -/
theorem prime_first_moment_block {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (k : ℕ) :
    |∑ j ∈ Finset.range k, primeSymbol c (M + (j : ℤ))| ≤ primeFirstMoment c := by
  classical
  let T : ℂ := ∑ q ∈ primeIndices c,
    (primeWeight q : ℂ) * ∑ j ∈ Finset.range k, primePhase c q ^ (M + (j : ℤ))
  have hid : (∑ j ∈ Finset.range k, primeSymbol c (M + (j : ℤ))) = T.im := by
    simp_rw [primeSymbol_is_im]
    rw [← im_sum]
    congr 1
    dsimp [T]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  rw [hid]
  calc
    |T.im| ≤ ‖T‖ := Complex.abs_im_le_norm _
    _ ≤ ∑ q ∈ primeIndices c,
        ‖(primeWeight q : ℂ) * ∑ j ∈ Finset.range k, primePhase c q ^ (M + (j : ℤ))‖ :=
      norm_sum_le _ _
    _ ≤ primeFirstMoment c := by
      apply Finset.sum_le_sum
      intro q hq
      have hg := geometric_block_norm (primePhase_norm c q) (actual_phase_ne_one hc hq) M k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |primeWeight q| * (2 / ‖1 - primePhase c q‖) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg _)
        _ = _ := by ring

private theorem actual_smooth_split (c : ℕ) {m : ℕ} (hm : 0 < m) :
    arithmeticBoundarySymbol c (m : ℤ) =
      -(m : ℝ) ^ 2 * smoothWeight c m - primeSymbol c (m : ℤ) := by
  simpa only [owner_prime_sum_eq] using arithmetic_symbol_smooth_split c hm

private def mixedTerm (c m : ℕ) : ℝ :=
  primeSymbol c (m : ℤ) *
    (arithmeticBoundarySymbol c (m : ℤ) + primeSymbol c (m : ℤ)) / (m : ℝ) ^ 2

private theorem mixedTerm_eq (c : ℕ) {m : ℕ} (hm : 0 < m) :
    mixedTerm c m = -(primeSymbol c (m : ℤ) * smoothWeight c m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mixedTerm, actual_smooth_split c hm]
  field_simp [hmR.ne']
  <;> ring

private theorem weight_div_bound {c n m : ℕ} (hc : 2 ≤ c)
    (hn : 0 < n) (hnm : n ≤ m) :
    smoothWeight c m ≤ smoothEnvelope c n / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hn hnm)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).mpr
  simpa only [mul_comm] using (smooth_weight_envelope hc hn hnm).2

private theorem signed_weighted_partial {c N : ℕ} (hc : 2 ≤ c) (k : ℕ) :
    |∑ j ∈ Finset.range k,
      primeSymbol c ((N + j + 1 : ℕ) : ℤ) * smoothWeight c (N + j + 1)| ≤
        primeFirstMoment c * smoothWeight c (N + 1) := by
  let x : ℕ → ℝ := fun j => primeSymbol c ((N + j + 1 : ℕ) : ℤ)
  let w : ℕ → ℝ := fun j => smoothWeight c (N + j + 1)
  have he (j : ℕ) : (N : ℤ) + 1 + (j : ℤ) = ((N + j + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have hblocks (l : ℕ) : |∑ j ∈ Finset.range l, x j| ≤ primeFirstMoment c := by
    simpa only [x, he] using prime_first_moment_block hc ((N : ℤ) + 1) l
  have hw (j : ℕ) : 0 ≤ w j := smooth_weight_nonneg hc (by omega)
  have hanti (j : ℕ) : w (j + 1) ≤ w j := by
    exact smooth_weight_antitone hc (by omega) (by omega)
  have hplus (l : ℕ) : (∑ j ∈ Finset.range l, x j) ≤ (l : ℝ) * 0 + primeFirstMoment c := by
    simpa only [mul_zero, zero_add] using (abs_le.mp (hblocks l)).2
  have hminus (l : ℕ) : (∑ j ∈ Finset.range l, -x j) ≤ (l : ℝ) * 0 + primeFirstMoment c := by
    rw [Finset.sum_neg_distrib]
    have hh := (abs_le.mp (hblocks l)).1
    simpa only [mul_zero, zero_add] using (show -(∑ j ∈ Finset.range l, x j) ≤ primeFirstMoment c by linarith)
  -- These are the two actual signed applications; no endpoint is dropped.
  have hp := finite_abel_majorant x w 0 (primeFirstMoment c)
    (firstMoment_nonneg c) hw hanti hplus k
  have hn := finite_abel_majorant (fun j => -x j) w 0 (primeFirstMoment c)
    (firstMoment_nonneg c) hw hanti hminus k
  simp only [zero_mul, zero_add] at hp hn
  have hneg : (∑ j ∈ Finset.range k, (-x j) * w j) =
      -(∑ j ∈ Finset.range k, x j * w j) := by
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [hneg] at hn
  change |∑ j ∈ Finset.range k, x j * w j| ≤ primeFirstMoment c * w 0
  exact abs_le.mpr ⟨by linarith, hp⟩

/-- Signed finite mixed estimate at every finite block length, including zero. -/
theorem signed_mixed_partial {c N : ℕ} (hc : 2 ≤ c) (k : ℕ) :
    |∑ j ∈ Finset.range k,
      primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
        (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
          primeSymbol c ((N + j + 1 : ℕ) : ℤ)) / ((N + j + 1 : ℕ) : ℝ) ^ 2| ≤
      primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2 := by
  change |∑ j ∈ Finset.range k, mixedTerm c (N + j + 1)| ≤ _
  have he (j : ℕ) : mixedTerm c (N + j + 1) =
      -(primeSymbol c ((N + j + 1 : ℕ) : ℤ) * smoothWeight c (N + j + 1)) :=
    mixedTerm_eq c (by omega)
  simp_rw [he]
  rw [Finset.sum_neg_distrib, abs_neg]
  calc
    _ ≤ primeFirstMoment c * smoothWeight c (N + 1) := signed_weighted_partial hc k
    _ ≤ primeFirstMoment c * (smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (weight_div_bound hc (by omega) le_rfl) (firstMoment_nonneg c)
    _ = _ := by ring

private def primeAbsMass (c : ℕ) : ℝ := ∑ q ∈ primeIndices c, |primeWeight q|

private theorem prime_uniform (c : ℕ) (m : ℤ) : |primeSymbol c m| ≤ primeAbsMass c := by
  unfold primeSymbol primeAbsMass
  calc
    _ ≤ ∑ q ∈ primeIndices c, |primeWeight q * Real.sin (2 * Real.pi * (m : ℝ) * theta c q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun q _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

private theorem inverse_weight_eq (N j : ℕ) :
    inverseSquareWeight N j = 1 / ((N + j + 1 : ℕ) : ℝ) ^ 2 := by
  simp only [inverseSquareWeight, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, inv_pow]

private theorem inverse_weights_summable {N : ℕ} (hN : 0 < N) :
    Summable (inverseSquareWeight N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  exact inverse_square_summable hNR

private theorem inverse_weights_tsum {N : ℕ} (hN : 0 < N) :
    (∑' j : ℕ, inverseSquareWeight N j) ≤ 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  simpa only [inverseSquareWeight, one_div] using Real.tsum_le_of_sum_range_le
    (fun j => sq_nonneg (((N : ℝ) + (j : ℝ) + 1)⁻¹)) (inverse_square_partial_le hNR)

private theorem inverse_step_lower_candidate {x : ℝ} (hx : 0 < x) :
    x⁻¹ - (x + 1)⁻¹ ≤ (x⁻¹) ^ 2 := by
  have hx1 : 0 < x + 1 := by linarith
  have heq : x⁻¹ - (x + 1)⁻¹ = (x * (x + 1))⁻¹ := by
    field_simp [ne_of_gt hx, ne_of_gt hx1]
    <;> ring
  -- Normalize the equality on both sides, rather than reversing inv_pow
  -- against an expression that may not match that rewrite direction.
  have hpow : (x⁻¹) ^ 2 = (x ^ 2)⁻¹ := by
    simp only [inv_pow]
  rw [heq, hpow]
  exact (inv_le_inv₀ (mul_pos hx hx1) (by positivity : 0 < x ^ 2)).2
    (by nlinarith)

private theorem inverse_square_partial_lower_candidate {d : ℝ} (hd : 0 < d)
    (K : ℕ) :
    (d + 1)⁻¹ - (d + (K : ℝ) + 1)⁻¹ ≤
      ∑ j ∈ Finset.range K, ((d + (j : ℝ) + 1)⁻¹) ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hstep := inverse_step_lower_candidate
        (show 0 < d + (K : ℝ) + 1 by positivity)
      simp only [Nat.cast_succ, add_assoc]
      simp only [add_assoc] at hstep ih
      linarith

private theorem inverse_square_tsum_lower_candidate {d : ℝ} (hd : 0 < d) :
    (d + 1)⁻¹ ≤ ∑' j : ℕ, ((d + (j : ℝ) + 1)⁻¹) ^ 2 := by
  have hs : Summable (fun j : ℕ => ((d + (j : ℝ) + 1)⁻¹) ^ 2) :=
    WeilInfiniteComplementLeakage.inverse_square_summable hd
  have hnat : Tendsto (fun K : ℕ => d + (K : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hK : ∀ᶠ K : ℕ in atTop, b - d - 1 ≤ (K : ℝ) :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop).eventually_ge_atTop (b - d - 1)
    filter_upwards [hK] with K hK
    linarith
  have hzero : Tendsto (fun K : ℕ => (d + (K : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero :
      Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).comp hnat
  have hconst : Tendsto (fun _ : ℕ => (d + 1)⁻¹) atTop (𝓝 ((d + 1)⁻¹)) :=
    tendsto_const_nhds
  have hlim : Tendsto
      (fun K : ℕ => (d + 1)⁻¹ - (d + (K : ℝ) + 1)⁻¹) atTop
      (𝓝 ((d + 1)⁻¹)) := by
    simpa only [sub_zero] using hconst.sub hzero
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro K
  exact (inverse_square_partial_lower_candidate hd K).trans
    (Summable.sum_le_tsum (Finset.range K) (fun _ _ => sq_nonneg _) hs)

private theorem weight_tail_dom {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (j : ℕ) :
    smoothWeight c (N + j + 1) ≤ smoothEnvelope c N * inverseSquareWeight N j := by
  rw [inverse_weight_eq]
  simpa only [div_eq_mul_inv, one_mul] using weight_div_bound hc hN (show N ≤ N + j + 1 by omega)

private theorem mixed_abs_summable {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) :
    Summable (fun j : ℕ => |mixedTerm c (N + j + 1)|) := by
  have hdom (j : ℕ) : |mixedTerm c (N + j + 1)| ≤
      (primeAbsMass c * smoothEnvelope c N) * inverseSquareWeight N j := by
    rw [mixedTerm_eq c (by omega), abs_neg, abs_mul,
      abs_of_nonneg (smooth_weight_nonneg hc (by omega))]
    have hP : 0 ≤ primeAbsMass c := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    calc
      _ ≤ primeAbsMass c * smoothWeight c (N + j + 1) :=
        mul_le_mul_of_nonneg_right (prime_uniform c _) (smooth_weight_nonneg hc (by omega))
      _ ≤ primeAbsMass c * (smoothEnvelope c N * inverseSquareWeight N j) :=
        mul_le_mul_of_nonneg_left (weight_tail_dom hc hN j) hP
      _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hdom
    ((inverse_weights_summable hN).mul_left (primeAbsMass c * smoothEnvelope c N))

/-- Absolute convergence is proved by the finite prime absolute-weight mass
and inverse squares, separately from the signed Abel estimate. The inequality
is then passed to the genuine sum using HasSum.tendsto_sum_nat. -/
theorem signed_mixed_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) :
    Summable (fun j : ℕ =>
      |primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
        (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
          primeSymbol c ((N + j + 1 : ℕ) : ℤ)) / ((N + j + 1 : ℕ) : ℝ) ^ 2|) ∧
    |∑' j : ℕ, primeSymbol c ((N + j + 1 : ℕ) : ℤ) *
      (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
        primeSymbol c ((N + j + 1 : ℕ) : ℤ)) / ((N + j + 1 : ℕ) : ℝ) ^ 2| ≤
      primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2 := by
  have ha := mixed_abs_summable hc hN
  have hs : Summable (fun j : ℕ => mixedTerm c (N + j + 1)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using ha
  refine ⟨ha, ?_⟩
  have hl := (continuous_abs.tendsto _).comp hs.hasSum.tendsto_sum_nat
  exact le_of_tendsto hl (Filter.Eventually.of_forall (fun k => signed_mixed_partial hc k))

private def smoothSquare (c N j : ℕ) : ℝ :=
  (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
    primeSymbol c ((N + j + 1 : ℕ) : ℤ)) ^ 2 * inverseSquareWeight N j

private theorem smooth_square_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) :
    Summable (smoothSquare c N) ∧
    (∑' j : ℕ, smoothSquare c N j) ≤ smoothEnvelope c N ^ 2 / (N : ℝ) := by
  have hnon (j : ℕ) : 0 ≤ smoothSquare c N j := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdom (j : ℕ) : smoothSquare c N j ≤ smoothEnvelope c N ^ 2 * inverseSquareWeight N j := by
    have hb := (smooth_weight_envelope hc hN (show N ≤ N + j + 1 by omega)).2
    have hw : 0 ≤ ((N + j + 1 : ℕ) : ℝ) ^ 2 * smoothWeight c (N + j + 1) :=
      mul_nonneg (sq_nonneg _) (smooth_weight_nonneg hc (by omega))
    have he : arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) +
        primeSymbol c ((N + j + 1 : ℕ) : ℤ) =
        -(((N + j + 1 : ℕ) : ℝ) ^ 2 * smoothWeight c (N + j + 1)) := by
      rw [actual_smooth_split c (by omega)]
      ring
    unfold smoothSquare
    rw [he, neg_sq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw hb 2) (sq_nonneg _)
  have hmajor := (inverse_weights_summable hN).mul_left (smoothEnvelope c N ^ 2)
  have hs := Summable.of_nonneg_of_le hnon hdom hmajor
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, smoothEnvelope c N ^ 2 * inverseSquareWeight N j :=
      hs.tsum_le_tsum hdom hmajor
    _ = smoothEnvelope c N ^ 2 * (∑' j : ℕ, inverseSquareWeight N j) := tsum_mul_left
    _ ≤ smoothEnvelope c N ^ 2 * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_weights_tsum hN) (sq_nonneg _)
    _ = _ := by ring

private theorem full_real_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) :
    Summable (fun j : ℕ => arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ∧
    (∑' j : ℕ, arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ≤
      fullSymbolTailBudget c N := by
  obtain ⟨hp, hpb⟩ := PrimeSymbolResonance.prime_symbol_square_tail hc hN
  obtain ⟨hh, hhb⟩ := smooth_square_tail hc hN
  obtain ⟨hma, hmb⟩ := signed_mixed_tail hc hN
  have hm : Summable (fun j : ℕ => mixedTerm c (N + j + 1)) := by
    apply Summable.of_norm
    simpa only [mixedTerm, Real.norm_eq_abs] using hma
  have hid (j : ℕ) :
      arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j =
        primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j +
          smoothSquare c N j - 2 * mixedTerm c (N + j + 1) := by
    unfold smoothSquare mixedTerm
    rw [inverse_weight_eq]
    ring
  have hs := ((hp.add hh).sub (hm.mul_left 2)).congr (fun j => (hid j).symm)
  refine ⟨hs, ?_⟩
  have heq :
      (∑' j : ℕ, arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) =
        (∑' j : ℕ, primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) +
        (∑' j : ℕ, smoothSquare c N j) - 2 * (∑' j : ℕ, mixedTerm c (N + j + 1)) := by
    simp_rw [hid]
    rw [(hp.add hh).tsum_sub (hm.mul_left 2), hp.tsum_add hh, tsum_mul_left]
  rw [heq]
  have hlo := (abs_le.mp hmb).1
  change _ ≤ PrimeSymbolResonance.tailBudget c N + smoothEnvelope c N ^ 2 / (N : ℝ) +
    2 * primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2
  change - (primeFirstMoment c * smoothEnvelope c (N + 1) / ((N + 1 : ℕ) : ℝ) ^ 2) ≤
    ∑' j : ℕ, mixedTerm c (N + j + 1) at hlo
  calc
    _ ≤ PrimeSymbolResonance.tailBudget c N + smoothEnvelope c N ^ 2 / (N : ℝ) +
        2 * (primeFirstMoment c * smoothEnvelope c (N + 1) /
          ((N + 1 : ℕ) : ℝ) ^ 2) := by
      linarith only [hpb, hhb, hlo]
    _ = _ := by ring

/- SOURCE_ONLY_UNCOMPILED. Splice after full_real_tail, before full_complex_energy,
inside the original ActualFullSymbolTail namespace/noncomputable section.
Requires input02 in its original Jet owner; no additional imports. -/

private theorem actual_full_real_tail_lower {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (hw : 1 ≤ frequency c ((M + 1 : ℕ) : ℤ)) :
    smoothFloor c ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) -
        2 * primeFirstMoment c * smoothEnvelope c (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤
      ∑' j : ℕ, arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
        inverseSquareWeight M j := by
  obtain ⟨hf, _⟩ := full_real_tail hc hM
  obtain ⟨hp, _⟩ := PrimeSymbolResonance.prime_symbol_square_tail hc hM
  obtain ⟨hh, _⟩ := smooth_square_tail hc hM
  obtain ⟨hma, hmb⟩ := signed_mixed_tail hc hM
  have hm : Summable (fun j : ℕ => mixedTerm c (M + j + 1)) := by
    apply Summable.of_norm
    simpa only [mixedTerm, Real.norm_eq_abs] using hma
  have hi := (inverse_weights_summable hM).mul_left (smoothFloor c ^ 2)
  have hL : 0 < logLength c := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hc)
  have hfreq (j : ℕ) : 1 ≤ frequency c ((M + j + 1 : ℕ) : ℤ) := by
    refine hw.trans ?_
    unfold frequency
    apply div_le_div_of_nonneg_right ?_ hL.le
    apply mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ 2 * Real.pi)
    exact_mod_cast (show M + 1 ≤ M + j + 1 by omega)
  have hpoint (j : ℕ) :
      smoothFloor c ^ 2 * inverseSquareWeight M j ≤ smoothSquare c M j := by
    obtain ⟨hd, hH⟩ := smooth_weight_floor hc (by omega) (hfreq j)
    have he : arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) +
        primeSymbol c ((M + j + 1 : ℕ) : ℤ) =
        -(((M + j + 1 : ℕ) : ℝ) ^ 2 * smoothWeight c (M + j + 1)) := by
      rw [actual_smooth_split c (by omega)]
      ring
    unfold smoothSquare
    rw [he, neg_sq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd.le hH 2) (sq_nonneg _)
  have hfloor : smoothFloor c ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) ≤
      ∑' j : ℕ, smoothSquare c M j := by
    calc
      _ = ∑' j : ℕ, smoothFloor c ^ 2 * inverseSquareWeight M j := tsum_mul_left.symm
      _ ≤ _ := hi.tsum_le_tsum hpoint hh
  have hid (j : ℕ) :
      arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j =
        primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j +
          smoothSquare c M j - 2 * mixedTerm c (M + j + 1) := by
    unfold smoothSquare mixedTerm
    rw [inverse_weight_eq]
    ring
  have heq :
      (∑' j : ℕ, arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
        inverseSquareWeight M j) =
        (∑' j : ℕ, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) +
        (∑' j : ℕ, smoothSquare c M j) - 2 * (∑' j : ℕ, mixedTerm c (M + j + 1)) := by
    exact hf.hasSum.unique
      (((hp.hasSum.add hh.hasSum).sub (hm.hasSum.mul_left 2)).congr_fun hid)
  have hp0 : 0 ≤ (∑' j : ℕ, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
      inverseSquareWeight M j) :=
    tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hupper := (abs_le.mp hmb).2
  change (∑' j : ℕ, mixedTerm c (M + j + 1)) ≤
    primeFirstMoment c * smoothEnvelope c (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2 at hupper
  rw [heq]
  calc
    _ = smoothFloor c ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) -
        2 * (primeFirstMoment c * smoothEnvelope c (M + 1) /
          ((M + 1 : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ _ := by linarith only [hfloor, hp0, hupper]

private theorem actual_full_real_tail_lower_coarse {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (hw : 1 ≤ frequency c ((M + 1 : ℕ) : ℤ)) :
    let U : ℝ := 2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
    let D0 : ℝ := 2 * primeFirstMoment c * (2 + U)
    smoothFloor c ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) -
        D0 / ((M + 1 : ℕ) : ℝ) ^ 2 ≤
      ∑' j : ℕ, arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
        inverseSquareWeight M j := by
  let a : ℝ := 2 * Real.pi / logLength c
  let U : ℝ := 2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
  let D0 : ℝ := 2 * primeFirstMoment c * (2 + U)
  change smoothFloor c ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) -
    D0 / ((M + 1 : ℕ) : ℝ) ^ 2 ≤ _
  have hL : 0 < logLength c := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hc)
  have ha : 0 < a := div_pos (by positivity) hL
  have hU : 0 ≤ U := div_nonneg
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_cosh _))) ha.le
  have ht : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ M + 1 by omega)
  have henv : smoothEnvelope c (M + 1) ≤ 2 + U := by
    calc
      _ ≤ 2 + U / ((M + 1 : ℕ) : ℝ) := by
        unfold smoothEnvelope
        with_unfolding_all
          change min (2 + U / ((M + 1 : ℕ) : ℝ))
            (Real.pi / 4 + (U + 3 / (4 * a)) / ((M + 1 : ℕ) : ℝ)) ≤
              2 + U / ((M + 1 : ℕ) : ℝ)
        exact min_le_left _ _
      _ ≤ 2 + U := by
        simpa only [add_comm] using (add_le_add_left (div_le_self hU ht) 2)
  have herr :
      2 * primeFirstMoment c * smoothEnvelope c (M + 1) / ((M + 1 : ℕ) : ℝ) ^ 2 ≤
        D0 / ((M + 1 : ℕ) : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left henv (mul_nonneg (by norm_num) (firstMoment_nonneg c)))
      (sq_nonneg _)
  exact (sub_le_sub_left herr _).trans (actual_full_real_tail_lower hc hM hw)

private theorem full_complex_energy (c N j : ℕ) (β : ℂ) :
    ‖β * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) /
      ((N + j + 1 : ℕ) : ℂ)‖ ^ 2 =
      ‖β‖ ^ 2 * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) := by
  have hm : ‖((N + j + 1 : ℕ) : ℂ)‖ = (N : ℝ) + (j : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (N + j + 1)
  rw [norm_div, norm_mul, div_pow, mul_pow, hm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [inverseSquareWeight, div_eq_mul_inv, inv_pow]
  ring

/-- Absolutely summable full arithmetic-symbol square tail, at the original
normalization and for arbitrary complex beta. Every prime power, actual pole,
actual Gamma term, and the factor two on the signed mixed bound are retained. -/
theorem full_symbol_square_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (β : ℂ) :
    Summable (fun j : ℕ =>
      ‖β * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) /
        ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧
    (∑' j : ℕ, ‖β * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) /
      ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤ ‖β‖ ^ 2 * fullSymbolTailBudget c N := by
  obtain ⟨hs, hb⟩ := full_real_tail hc hN
  constructor
  · exact (hs.mul_left (‖β‖ ^ 2)).congr (fun j => (full_complex_energy c N j β).symm)
  · simp_rw [full_complex_energy]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

private theorem collect_first_jet (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :
    couplingFirstJet c S v m =
      ((∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) -
        (arithmeticBoundarySymbol c m : ℂ) * (∑ n ∈ S, v n)) /
        ((Real.pi : ℂ) * (m : ℂ)) := by
  rw [canonical_first_jet_split]
  unfold canonicalPrimeFirstJetFar
  push_cast
  ring

-- A consumed private pairing calculation, reusing native oddness. It is not
-- a copied/redeclared public parity theorem.
private theorem first_jet_pair (c N j : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) :
    let m : ℤ := ((N + j + 1 : ℕ) : ℤ)
    ‖couplingFirstJet c S v m‖ ^ 2 + ‖couplingFirstJet c S v (-m)‖ ^ 2 =
      (2 / Real.pi ^ 2) *
        (‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n‖ ^ 2 * inverseSquareWeight N j +
          ‖(∑ n ∈ S, v n) * (arithmeticBoundarySymbol c m : ℂ) /
            ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) := by
  dsimp only
  let m : ℤ := ((N + j + 1 : ℕ) : ℤ)
  let α : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n
  let β : ℂ := ∑ n ∈ S, v n
  let V : ℂ := -(arithmeticBoundarySymbol c m : ℂ) * β
  let z : ℂ := (Real.pi : ℂ) * (m : ℂ)
  have hp : couplingFirstJet c S v m = (α + V) / z := by
    rw [collect_first_jet]
    dsimp [α, V, z]
    ring
  have hn : couplingFirstJet c S v (-m) = -(α - V) / z := by
    rw [collect_first_jet, arithmetic_boundary_symbol_neg]
    dsimp [α, V, z]
    push_cast
    simp only [mul_neg, div_neg]
    ring
  have hz : ‖z‖ ^ 2 = Real.pi ^ 2 * ((N + j + 1 : ℕ) : ℝ) ^ 2 := by
    have hm : ‖(((N + j + 1 : ℕ) : ℤ) : ℂ)‖ = ((N + j + 1 : ℕ) : ℝ) := by
      simpa only [Int.cast_natCast] using Complex.norm_natCast (N + j + 1)
    dsimp only [z, m]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hm]
  have hV : ‖V‖ ^ 2 = arithmeticBoundarySymbol c m ^ 2 * ‖β‖ ^ 2 := by
    dsimp [V]
    rw [norm_mul, mul_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change ‖couplingFirstJet c S v m‖ ^ 2 + ‖couplingFirstJet c S v (-m)‖ ^ 2 = _
  rw [hp, hn, norm_div, norm_div, norm_neg, div_pow, div_pow, ← add_div,
    parallelogram_law_with_norm ℂ α V, hz, hV, full_complex_energy, inverse_weight_eq]
  have hmR : (0 : ℝ) < ((N + j + 1 : ℕ) : ℝ) := by positivity
  dsimp [α, β, m]
  field_simp [Real.pi_ne_zero, hmR.ne']
  <;> ring

/-- Both exterior signs, enumerated by m=N+j+1 and -m. The factor 2/pi^2
comes from native oddness and the complex parallelogram identity, with both
head moments present. This is a lattice first-jet bound, not a column or
physical Weil-operator remainder bound. -/
theorem paired_first_jet_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N)
    (S : Finset ℤ) (v : ℤ → ℂ) :
    Summable (fun j : ℕ =>
      ‖couplingFirstJet c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingFirstJet c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ,
      (‖couplingFirstJet c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingFirstJet c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      (2 / Real.pi ^ 2) *
        (‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n‖ ^ 2 / (N : ℝ) +
          ‖∑ n ∈ S, v n‖ ^ 2 * fullSymbolTailBudget c N) := by
  obtain ⟨hs, hb⟩ := full_symbol_square_tail hc hN (∑ n ∈ S, v n)
  have hi := (inverse_weights_summable hN).mul_left
    (‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n‖ ^ 2)
  constructor
  · exact ((hi.add hs).mul_left (2 / Real.pi ^ 2)).congr
      (fun j => (first_jet_pair c N j S v).symm)
  · simp_rw [first_jet_pair]
    rw [tsum_mul_left, hi.tsum_add hs, tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ hb
    calc
      _ ≤ ‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n‖ ^ 2 * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (inverse_weights_tsum hN) (sq_nonneg _)
      _ = _ := by ring

/-!
## Actual weighted remainder and paired column

SOURCE_ONLY_UNCOMPILED: the following extension is a source proof candidate.
The old declarations above are preserved. The singleton estimate retains the
actual symbol and |n|, including n=0. The finite Cauchy--Schwarz argument below
passes to the genuine infinite sum with the same square-root budget.
-/

/-- Exactly the old paired first-jet budget, with both complex moments. -/
def pairedJetBudget (c M : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) : ℝ :=
  (2 / Real.pi ^ 2) *
    (‖∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n‖ ^ 2 / (M : ℝ) +
      ‖∑ n ∈ S, v n‖ ^ 2 * fullSymbolTailBudget c M)

-- Consumed finite Cauchy--Schwarz, with the exact square-root sum budget.
-- This private analytic calculation makes no new public framework or claim.
private theorem finite_add_energy {ι : Type*} (s : Finset ι) (x y : ι → ℂ)
    {J R : ℝ} (hx : (∑ i ∈ s, ‖x i‖ ^ 2) ≤ J)
    (hy : (∑ i ∈ s, ‖y i‖ ^ 2) ≤ R) :
    (∑ i ∈ s, ‖x i + y i‖ ^ 2) ≤ (Real.sqrt J + Real.sqrt R) ^ 2 := by
  have hx0 : 0 ≤ ∑ i ∈ s, ‖x i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy0 : 0 ≤ ∑ i ∈ s, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hJ0 : 0 ≤ J := hx0.trans hx
  have hR0 : 0 ≤ R := hy0.trans hy
  have hcross := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖x i‖) (fun i => ‖y i‖)
  have hcross' : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ≤ Real.sqrt J * Real.sqrt R :=
    hcross.trans (mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ ≤ ∑ i ∈ s, (‖x i‖ ^ 2 + 2 * (‖x i‖ * ‖y i‖) + ‖y i‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (x i) (y i)) 2
      nlinarith
    _ = (∑ i ∈ s, ‖x i‖ ^ 2) + 2 * (∑ i ∈ s, ‖x i‖ * ‖y i‖) +
        (∑ i ∈ s, ‖y i‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ J + 2 * (Real.sqrt J * Real.sqrt R) + R := by linarith
    _ = _ := by nlinarith [Real.sq_sqrt hJ0, Real.sq_sqrt hR0]

/-- The actual paired full-column energy, with arbitrary complex head data.
The infinite sum has the exact (sqrt(J)+sqrt(R))^2 budget. Under the two actual
head moment equations J vanishes and this same result gives R; no cancellation
premise is imposed. Fourier/operator identification and RH positivity remain
separate, and the FIB five-mode model is not five arbitrary Fourier coefficients.
All assertions in this extension remain SOURCE_ONLY_UNCOMPILED. -/
theorem paired_coupling_column_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) (hsep : A < (M : ℝ) + 1) :
    Summable (fun j : ℕ =>
      ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    (∑' j : ℕ,
      (‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2)) ≤
      (Real.sqrt (pairedJetBudget c M S v) +
        Real.sqrt (pairedRemainderBudget c M A S v)) ^ 2 := by
  classical
  obtain ⟨hj, hjb⟩ := paired_first_jet_tail hc hM S v
  obtain ⟨hr, hrb⟩ := paired_first_jet_remainder_tail hc hM S v hA hS hsep
  let q : ℕ → ℝ := fun j =>
    ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
    ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2
  have hpartial (k : ℕ) : (∑ j ∈ Finset.range k, q j) ≤
      (Real.sqrt (pairedJetBudget c M S v) +
        Real.sqrt (pairedRemainderBudget c M A S v)) ^ 2 := by
    let s : Finset (ℕ × Bool) := Finset.range k ×ˢ Finset.univ
    let mode : ℕ × Bool → ℤ := fun i =>
      if i.2 then ((M + i.1 + 1 : ℕ) : ℤ) else -((M + i.1 + 1 : ℕ) : ℤ)
    let x : ℕ × Bool → ℂ := fun i => couplingFirstJet c S v (mode i)
    let y : ℕ × Bool → ℂ := fun i => couplingColumn c S v (mode i) - x i
    have hx : (∑ i ∈ s, ‖x i‖ ^ 2) ≤ pairedJetBudget c M S v := by
      have h := (Summable.sum_le_tsum (Finset.range k)
        (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) hj).trans hjb
      simpa [s, x, mode, Finset.sum_product, pairedJetBudget, add_comm] using h
    have hy : (∑ i ∈ s, ‖y i‖ ^ 2) ≤ pairedRemainderBudget c M A S v := by
      have h := (Summable.sum_le_tsum (Finset.range k)
        (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) hr).trans hrb
      simpa [s, y, x, mode, Finset.sum_product, add_comm] using h
    have h := finite_add_energy s x y hx hy
    have hxy (i : ℕ × Bool) : x i + y i = couplingColumn c S v (mode i) := by
      dsimp [y]
      ring
    simp_rw [hxy] at h
    simpa [q, s, mode, Finset.sum_product, add_comm] using h
  have hnon (j : ℕ) : 0 ≤ q j := add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hnon hpartial,
    Real.tsum_le_of_sum_range_le hnon hpartial⟩

private def jetEnergyAlpha (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) : ℂ :=
  ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n

private def jetEnergyBeta (S : Finset ℤ) (v : ℤ → ℂ) : ℂ :=
  ∑ n ∈ S, v n

private def pairedJetEnergyTerm (c M : ℕ) (S : Finset ℤ) (v : ℤ → ℂ)
    (j : ℕ) : ℝ :=
  ‖couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
    ‖couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2

private def pairedColumnEnergyTerm (c M : ℕ) (S : Finset ℤ) (v : ℤ → ℂ)
    (j : ℕ) : ℝ :=
  ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
    ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2

private def pairedJetRemainderEnergyTerm (c M : ℕ) (S : Finset ℤ)
    (v : ℤ → ℂ) (j : ℕ) : ℝ :=
  ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ) -
    couplingFirstJet c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
    ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ)) -
      couplingFirstJet c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2

-- The two component series are summable before any tsum identity is used.
-- No equality is inferred from the existing upper first-jet budget.
private theorem paired_first_jet_energy_exact {c M : ℕ}
    (hc : 2 ≤ c) (hM : 0 < M) (S : Finset ℤ) (v : ℤ → ℂ) :
    Summable (pairedJetEnergyTerm c M S v) ∧
    (∑' j : ℕ, pairedJetEnergyTerm c M S v j) =
      (2 / Real.pi ^ 2) *
        (‖jetEnergyAlpha c S v‖ ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) +
          ‖jetEnergyBeta S v‖ ^ 2 *
            (∑' j : ℕ, arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
              inverseSquareWeight M j)) := by
  have hw : Summable (inverseSquareWeight M) := inverse_weights_summable hM
  have ht : Summable (fun j : ℕ =>
      arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
        inverseSquareWeight M j) := (full_real_tail hc hM).1
  have ha : Summable (fun j : ℕ =>
      ‖jetEnergyAlpha c S v‖ ^ 2 * inverseSquareWeight M j) :=
    hw.mul_left (‖jetEnergyAlpha c S v‖ ^ 2)
  have hb : Summable (fun j : ℕ =>
      ‖jetEnergyBeta S v‖ ^ 2 *
        (arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
          inverseSquareWeight M j)) :=
    ht.mul_left (‖jetEnergyBeta S v‖ ^ 2)
  have hpair (j : ℕ) : pairedJetEnergyTerm c M S v j =
      (2 / Real.pi ^ 2) *
        (‖jetEnergyAlpha c S v‖ ^ 2 * inverseSquareWeight M j +
          ‖jetEnergyBeta S v‖ ^ 2 *
            (arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
              inverseSquareWeight M j)) := by
    simpa only [pairedJetEnergyTerm, jetEnergyAlpha, jetEnergyBeta,
      full_complex_energy] using (first_jet_pair c M j S v)
  have hj : Summable (pairedJetEnergyTerm c M S v) :=
    ((ha.add hb).mul_left (2 / Real.pi ^ 2)).congr (fun j => (hpair j).symm)
  refine ⟨hj, ?_⟩
  calc
    (∑' j : ℕ, pairedJetEnergyTerm c M S v j) =
        ∑' j : ℕ, (2 / Real.pi ^ 2) *
          (‖jetEnergyAlpha c S v‖ ^ 2 * inverseSquareWeight M j +
            ‖jetEnergyBeta S v‖ ^ 2 *
              (arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
                inverseSquareWeight M j)) := tsum_congr hpair
    _ = (2 / Real.pi ^ 2) *
        (∑' j : ℕ, (‖jetEnergyAlpha c S v‖ ^ 2 * inverseSquareWeight M j +
          ‖jetEnergyBeta S v‖ ^ 2 *
            (arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
              inverseSquareWeight M j))) := (ha.add hb).tsum_mul_left _
    _ = (2 / Real.pi ^ 2) *
        ((∑' j : ℕ, ‖jetEnergyAlpha c S v‖ ^ 2 * inverseSquareWeight M j) +
          (∑' j : ℕ, ‖jetEnergyBeta S v‖ ^ 2 *
            (arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
              inverseSquareWeight M j))) := by rw [ha.tsum_add hb]
    _ = (2 / Real.pi ^ 2) *
        (‖jetEnergyAlpha c S v‖ ^ 2 * (∑' j : ℕ, inverseSquareWeight M j) +
          ‖jetEnergyBeta S v‖ ^ 2 *
            (∑' j : ℕ, arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 *
              inverseSquareWeight M j)) := by
      rw [hw.tsum_mul_left (‖jetEnergyAlpha c S v‖ ^ 2),
        ht.tsum_mul_left (‖jetEnergyBeta S v‖ ^ 2)]

-- Valid for every actual integer mode; the next consumer uses m and -m.
private theorem actual_first_jet_reverse_pointwise (c : ℕ)
    (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :
    ‖couplingFirstJet c S v m‖ ^ 2 ≤
      2 * ‖couplingColumn c S v m‖ ^ 2 +
        2 * ‖couplingColumn c S v m - couplingFirstJet c S v m‖ ^ 2 := by
  have htriangle : ‖couplingFirstJet c S v m‖ ≤
      ‖couplingColumn c S v m‖ +
        ‖couplingColumn c S v m - couplingFirstJet c S v m‖ := by
    calc
      ‖couplingFirstJet c S v m‖ =
          ‖couplingColumn c S v m -
            (couplingColumn c S v m - couplingFirstJet c S v m)‖ := by
        congr 1
        ring
      _ ≤ _ := norm_sub_le _ _
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  nlinarith [sq_nonneg (‖couplingColumn c S v m‖ -
    ‖couplingColumn c S v m - couplingFirstJet c S v m‖)]

-- Direct tsum comparison, after obtaining ALL three actual summability proofs.
private theorem paired_actual_reverse_energy {c M : ℕ}
    (hc : 2 ≤ c) (hM : 0 < M) (S : Finset ℤ) (v : ℤ → ℂ)
    {A : ℝ} (hA : 0 ≤ A) (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A)
    (hsep : A < (M : ℝ) + 1) :
    Summable (pairedColumnEnergyTerm c M S v) ∧
    Summable (pairedJetEnergyTerm c M S v) ∧
    Summable (pairedJetRemainderEnergyTerm c M S v) ∧
    (∑' j : ℕ, pairedJetEnergyTerm c M S v j) ≤
      2 * (∑' j : ℕ, pairedColumnEnergyTerm c M S v j) +
        2 * (∑' j : ℕ, pairedJetRemainderEnergyTerm c M S v j) ∧
    (∑' j : ℕ, pairedJetRemainderEnergyTerm c M S v j) ≤
      pairedRemainderBudget c M A S v := by
  have hcolumn : Summable (pairedColumnEnergyTerm c M S v) :=
    (paired_coupling_column_tail hc hM S v hA hS hsep).1
  have hjet : Summable (pairedJetEnergyTerm c M S v) :=
    (paired_first_jet_tail hc hM S v).1
  obtain ⟨hrem0, hremb0⟩ := paired_first_jet_remainder_tail hc hM S v hA hS hsep
  have hrem : Summable (pairedJetRemainderEnergyTerm c M S v) := hrem0
  have hremb : (∑' j : ℕ, pairedJetRemainderEnergyTerm c M S v j) ≤
      pairedRemainderBudget c M A S v := hremb0
  have hcolumn2 : Summable (fun j : ℕ => 2 * pairedColumnEnergyTerm c M S v j) :=
    hcolumn.mul_left 2
  have hrem2 : Summable (fun j : ℕ => 2 * pairedJetRemainderEnergyTerm c M S v j) :=
    hrem.mul_left 2
  have hpoint (j : ℕ) : pairedJetEnergyTerm c M S v j ≤
      2 * pairedColumnEnergyTerm c M S v j +
        2 * pairedJetRemainderEnergyTerm c M S v j := by
    have hp := actual_first_jet_reverse_pointwise c S v ((M + j + 1 : ℕ) : ℤ)
    have hn := actual_first_jet_reverse_pointwise c S v (-((M + j + 1 : ℕ) : ℤ))
    dsimp only [pairedJetEnergyTerm, pairedColumnEnergyTerm,
      pairedJetRemainderEnergyTerm]
    linarith only [hp, hn]
  have hreverse : (∑' j : ℕ, pairedJetEnergyTerm c M S v j) ≤
      2 * (∑' j : ℕ, pairedColumnEnergyTerm c M S v j) +
        2 * (∑' j : ℕ, pairedJetRemainderEnergyTerm c M S v j) := by
    calc
      (∑' j : ℕ, pairedJetEnergyTerm c M S v j) ≤
          ∑' j : ℕ, (2 * pairedColumnEnergyTerm c M S v j +
            2 * pairedJetRemainderEnergyTerm c M S v j) :=
        hjet.tsum_le_tsum hpoint (hcolumn2.add hrem2)
      _ = (∑' j : ℕ, 2 * pairedColumnEnergyTerm c M S v j) +
          (∑' j : ℕ, 2 * pairedJetRemainderEnergyTerm c M S v j) :=
        hcolumn2.tsum_add hrem2
      _ = 2 * (∑' j : ℕ, pairedColumnEnergyTerm c M S v j) +
          2 * (∑' j : ℕ, pairedJetRemainderEnergyTerm c M S v j) := by
        rw [hcolumn.tsum_mul_left 2, hrem.tsum_mul_left 2]
  exact ⟨hcolumn, hjet, hrem, hreverse, hremb⟩

/- SOURCE_ONLY_UNCOMPILED. Splice inside the original Full owner, after input03's
paired_actual_reverse_energy (omit its optional final packaging bridge), input04's
three private declarations and input10's two private declarations. Input02 belongs
in Jet. Full must import/open ActualColumnRemainder after the genuine input06
migration; retain paired_coupling_column_tail in Full. No new imports here. -/

private theorem column_lower_remainder_scalar {m t A q K : ℝ}
    (hm : 0 < m) (ht : 0 < t) (htm : t ≤ 2 * m) (hgap : 2 * A ≤ t)
    (hq : 0 < q) (hK : 0 ≤ K) (hcut : 256 * K / (3 * q) ≤ m ^ 2) :
    8 * K * t ^ 2 / (3 * Real.pi ^ 2 * m ^ 3 * (t - A) ^ 2) ≤
      q / (4 * Real.pi ^ 2 * t) := by
  have hg : 0 < t - A := by linarith
  have hg2 : t ^ 2 ≤ 4 * (t - A) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ t / 2)
      (show t / 2 ≤ t - A by linarith) 2
    nlinarith only [hs]
  have hcoarse :
      8 * K * t ^ 2 / (3 * Real.pi ^ 2 * m ^ 3 * (t - A) ^ 2) ≤
        32 * K / (3 * Real.pi ^ 2 * m ^ 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hh := mul_le_mul_of_nonneg_left hg2
      (show 0 ≤ 8 * K * (3 * Real.pi ^ 2 * m ^ 3) by positivity)
    nlinarith only [hh]
  have hc : 256 * K ≤ m ^ 2 * (3 * q) :=
    (div_le_iff₀ (by positivity)).1 hcut
  have hscale : 128 * K * t ≤ 3 * q * m ^ 3 := by
    have hleft := mul_le_mul_of_nonneg_left htm hK
    have hright := mul_le_mul_of_nonneg_right hc hm.le
    nlinarith only [hleft, hright]
  refine hcoarse.trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hp := mul_le_mul_of_nonneg_left hscale (sq_nonneg Real.pi)
  nlinarith only [hp]

/-- Actual paired column energy has an inverse-linear lower tail when its two
actual head moments give positive q and the explicit full cutoffs hold. -/
theorem paired_coupling_column_tail_lower {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ A) :
    let alpha : ℂ := ∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n
    let beta : ℂ := ∑ n ∈ S, v n
    let q : ℝ := ‖alpha‖ ^ 2 + smoothFloor c ^ 2 * ‖beta‖ ^ 2
    let U : ℝ := 2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
    let D0 : ℝ := 2 * primeFirstMoment c * (2 + U)
    1 ≤ frequency c ((M + 1 : ℕ) : ℤ) →
    2 * A ≤ (M : ℝ) + 1 →
    0 < q →
    2 * ‖beta‖ ^ 2 * D0 / q ≤ (M : ℝ) + 1 →
    256 * arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S v ^ 2 / (3 * q) ≤
      (M : ℝ) ^ 2 →
    Summable (fun j : ℕ =>
      ‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
    q / (4 * Real.pi ^ 2 * ((M : ℝ) + 1)) ≤
      ∑' j : ℕ, (‖couplingColumn c S v ((M + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((M + j + 1 : ℕ) : ℤ))‖ ^ 2) := by
  dsimp only
  intro hw hgap hq hmix hcut
  let t : ℝ := (M : ℝ) + 1
  let a : ℝ := ‖jetEnergyAlpha c S v‖ ^ 2
  let b : ℝ := ‖jetEnergyBeta S v‖ ^ 2
  let q : ℝ := a + smoothFloor c ^ 2 * b
  let U : ℝ := 2 * (Real.cosh (logLength c / 2) - 1) / (2 * Real.pi / logLength c)
  let D0 : ℝ := 2 * primeFirstMoment c * (2 + U)
  let W : ℝ := ∑' j : ℕ, inverseSquareWeight M j
  let T : ℝ := ∑' j : ℕ,
    arithmeticBoundarySymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j
  change 0 < q at hq
  change 2 * b * D0 / q ≤ t at hmix
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have ht : 0 < t := by dsimp [t]; positivity
  have hsep : A < (M : ℝ) + 1 := by dsimp [t] at ht; linarith
  obtain ⟨hcol, hjet, hrem, hreverse, hremb⟩ :=
    paired_actual_reverse_energy hc hM S v hA hS hsep
  have hid : (∑' j : ℕ, pairedJetEnergyTerm c M S v j) =
      (2 / Real.pi ^ 2) * (a * W + b * T) :=
    (paired_first_jet_energy_exact hc hM S v).2
  have hW : 1 / t ≤ W := by
    simpa only [t, W, inverseSquareWeight, one_div] using
      (inverse_square_tsum_lower_candidate hm)
  have hT : smoothFloor c ^ 2 * W - D0 / t ^ 2 ≤ T := by
    simpa only [W, T, D0, U, t, Nat.cast_add, Nat.cast_one] using
      (actual_full_real_tail_lower_coarse hc hM hw)
  have hweighted := mul_le_mul_of_nonneg_left hT (show 0 ≤ b by dsimp [b]; positivity)
  have hWq := mul_le_mul_of_nonneg_left hW hq.le
  have hmain : q / t - b * D0 / t ^ 2 ≤ a * W + b * T := by
    calc
      _ = q * (1 / t) - b * D0 / t ^ 2 := by ring
      _ ≤ q * W - b * D0 / t ^ 2 := sub_le_sub_right hWq _
      _ = a * W + b * (smoothFloor c ^ 2 * W - D0 / t ^ 2) := by
        dsimp only [q]
        ring
      _ ≤ _ := add_le_add le_rfl hweighted
  have hmix' : 2 * b * D0 ≤ t * q := (div_le_iff₀ hq).1 hmix
  have herr : b * D0 / t ^ 2 ≤ q / (2 * t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_right hmix' ht.le]
  have hbase : q / (2 * t) ≤ a * W + b * T := by
    have he : q / t = 2 * (q / (2 * t)) := by
      field_simp [ht.ne'] <;> ring
    linarith only [hmain, herr, he]
  have hjlow : q / (Real.pi ^ 2 * t) ≤
      ∑' j : ℕ, pairedJetEnergyTerm c M S v j := by
    calc
      _ = (2 / Real.pi ^ 2) * (q / (2 * t)) := by
        field_simp [Real.pi_pos.ne', ht.ne'] <;> ring
      _ ≤ (2 / Real.pi ^ 2) * (a * W + b * T) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := hid.symm
  let K : ℝ := arithmeticBoundaryBudget c ^ 2 * weightedHeadMass S v ^ 2
  have hcut' : 256 * K / (3 * q) ≤ (M : ℝ) ^ 2 := by
    simpa only [K, q, a, b, jetEnergyAlpha, jetEnergyBeta, mul_assoc] using hcut
  have hrbudget : pairedRemainderBudget c M A S v ≤ q / (4 * Real.pi ^ 2 * t) := by
    have hb := column_lower_remainder_scalar hm ht
      (show t ≤ 2 * (M : ℝ) by dsimp [t]; linarith) hgap hq
      (show 0 ≤ K by dsimp [K]; positivity) hcut'
    simpa only [pairedRemainderBudget, K, t, mul_assoc] using hb
  have hrsmall := hremb.trans hrbudget
  refine ⟨hcol, ?_⟩
  change q / (4 * Real.pi ^ 2 * t) ≤ ∑' j : ℕ, pairedColumnEnergyTerm c M S v j
  have hfour : q / (Real.pi ^ 2 * t) =
      4 * (q / (4 * Real.pi ^ 2 * t)) := by
    field_simp [Real.pi_pos.ne', ht.ne'] <;> ring
  linarith only [hjlow, hreverse, hrsmall, hfour]

end D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
