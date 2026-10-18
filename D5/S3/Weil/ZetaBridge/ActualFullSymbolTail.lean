/- GID: D5/S3/Weil/ZetaBridge/ActualFullSymbolTail
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualFullSymbolTail
   mirror-E: none(waiver:general-analytic-identity-and-tail-estimate)
   anchors: []
   utility: none
   digest: Actual first-moment, signed mixed and full arithmetic-symbol tails with both first-jet signs. -/

/-
SOURCE_ONLY_UNCOMPILED. This source candidate is not an accepted Lean result.
The complete pinned import, declaration, definition and proof body is unchanged.
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

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
open scoped BigOperators
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
  simpa only [one_div] using Real.tsum_le_of_sum_range_le
    (fun j => sq_nonneg (((N : ℝ) + (j : ℝ) + 1)⁻¹)) (inverse_square_partial_le hNR)

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
    simpa only [Real.norm_eq_abs] using hma
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
  linarith

private theorem full_complex_energy (c N j : ℕ) (β : ℂ) :
    ‖β * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) /
      ((N + j + 1 : ℕ) : ℂ)‖ ^ 2 =
      ‖β‖ ^ 2 * (arithmeticBoundarySymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) := by
  have hm : ‖((N + j + 1 : ℕ) : ℂ)‖ = (N : ℝ) + (j : ℝ) + 1 := by simp
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
    dsimp [z, m]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp
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
      ‖couplingFirstJet c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
      ‖couplingFirstJet c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ≤
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

end D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
