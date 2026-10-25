/- GID: D5/S3/Analytic/KarpZhangGamma/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangGamma/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: Paired gamma kernels give coefficientwise positivity of the two-variable transform. -/

import D5.S3.Analytic.KarpZhangGamma.Smoothing
import D5.S3.Analytic.KummerRatio.BetaIntegral
import Mathlib.RingTheory.Binomial

/-!
admission_basis: escape-witness
content theorem: pairedKernel_sign, consumed by two_variable_nonneg.
escape_witness: The Gamma recurrence and increasing increments of (x-1)/(S-x) give the
backward step for the four-term bracket. pairedKernel_sign inductively
propagates nonpositivity across arbitrary index gaps, contradicting an
earlier positive entry. Pairing counts the middle term once. The nonnegative
total and increasing smoothed weights prove two_variable_nonneg.
The convolution helpers apply pinned Chu–Vandermonde through
Ring.descPochhammer_smeval_add and KummerRatio.BetaIntegral.gamma_pochhammer,
then use Real.convexOn_log_Gamma. These helpers and the paired total are
bind-only; the sign propagation supplies the module content.
The gamma-series identification is supplied by Series, not this module.

Per-declaration proof_shape (Kernel names belong to the kernel namespace;
other local names belong to Result; cross-module names have prefix D5.S3.Analytic):
* Kernel.binomialGamma_sum: proof_shape: bind-only; escape_witness: none;
  reuse: KummerRatio.BetaIntegral.gamma_pochhammer, divided by positive Gamma;
  consumers: reciprocalGamma_sum.
* Kernel.reciprocalGamma_sum: proof_shape: bind-only; escape_witness: none;
  consumers: kernel_sum_nonneg.
* Kernel.gamma_balanced_shift: proof_shape: bind-only; escape_witness: none;
  consumers: Kernel.kernel_sum_nonneg, reciprocalPair_balanced.
* Kernel.kernel: proof_shape: bind-only (definition); escape_witness: none;
  consumers: Kernel.kernel_sum_nonneg, finite_pairing, pairedKernel, pairedKernel_bracket, pairedKernel_sum_nonneg, transformDelta, two_variable_nonneg, KarpZhangGamma.Series.transformed_delta.
* Kernel.kernel_sum_nonneg: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sum_nonneg.

* pairedKernel: proof_shape: bind-only (definition); escape_witness: none;
  consumers: finite_pairing, pairedKernel_bracket, pairedKernel_sign, pairedKernel_sum_nonneg, two_variable_nonneg.
* reciprocalPair: proof_shape: bind-only (definition); escape_witness: none;
  consumers: fourBracket, fourBracket_backward, fourBracket_swap, pairedKernel_bracket, reciprocalPair_balanced, reciprocalPair_step.
* fourBracket: proof_shape: bind-only (definition); escape_witness: none;
  consumers: bracket_backward_nat, fourBracket_backward, fourBracket_swap, pairedKernel_bracket, pairedKernel_sign.
* reciprocalPair_balanced: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* reciprocalPair_step: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* recurrenceFactor: proof_shape: bind-only (definition); escape_witness: none;
  consumers: fourBracket_backward, recurrenceFactor_increment, recurrenceFactor_mono.
* recurrenceFactor_mono: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* recurrenceFactor_increment: proof_shape: bind-only; escape_witness: none;
  consumers: fourBracket_backward.
* fourBracket_backward: proof_shape: bind-only; escape_witness: none;
  consumers: bracket_backward_nat.
* fourBracket_swap: proof_shape: bind-only; escape_witness: none;
  consumers: bracket_backward_nat.
* bracket_backward_nat: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sign.
* pairedKernel_bracket: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sign.
* pairedKernel_sign: proof_shape: content; escape_witness: pairedKernel_sign;
  consumers: two_variable_nonneg.
* pair_sum: proof_shape: bind-only; escape_witness: none;
  consumers: finite_pairing.
* finite_pairing: proof_shape: bind-only; escape_witness: none;
  consumers: pairedKernel_sum_nonneg, two_variable_nonneg.
* pairedKernel_sum_nonneg: proof_shape: bind-only; escape_witness: none;
  consumers: two_variable_nonneg.
* transformDelta: proof_shape: bind-only (definition); escape_witness: none;
  consumers: two_variable_nonneg, KarpZhangGamma.Series.gamma_half, KarpZhangGamma.Series.transformed_delta.
* two_variable_nonneg: proof_shape: content; escape_witness: pairedKernel_sign;
  consumers: KarpZhangGamma.Series.gamma_half.

Direct frozen D5 dependencies, with same-delivery helpers recursively inlined:
* F1: GID D5/S3/Analytic/KummerRatio/BetaIntegral.gamma_pochhammer;
  declaration statement_id:
  sha256:1059688f4875284d841121819603b9b49cf825aab8e4de735ff76c3e200ab797.
Per-declaration live-path dependencies (F labels above; omitted declarations: none):
* KarpZhangGamma.Kernel.binomialGamma_sum: F1.
* KarpZhangGamma.Kernel.reciprocalGamma_sum: F1.
* KarpZhangGamma.Kernel.kernel_sum_nonneg: F1.
* KarpZhangGamma.Result.pairedKernel_sum_nonneg: F1.
* KarpZhangGamma.Result.two_variable_nonneg: F1.
All KarpZhang dependencies are same-delivery declarations.
Consumers are taken from compiled proof
terms, with declaration types also counted for definitions. The listed
content witnesses remain on the corresponding live mathematical paths.
Utility is none: all statements are general identities or inequalities,
not bounded enumeration, checkers, numerical reductions or certified instances.
-/

noncomputable section
open scoped BigOperators
open Finset

open Polynomial

namespace D5.S3.Analytic.KarpZhangGamma.Kernel

open Smoothing

private theorem binomialGamma_sum (m : ℕ) : ∀ b c : ℝ, 0 < b → 0 < c →
    binomialProduct (fun k => 1 / Real.Gamma (b + k))
      (fun k => 1 / Real.Gamma (c + k)) m =
    (ascPochhammer ℝ m).eval (b + c + m - 1) /
      (Real.Gamma (b + m) * Real.Gamma (c + m)) := by
  intro b c hb hc
  have ratio (x : ℝ) (hx : 0 < x) (n : ℕ) :
      Real.Gamma (x + n) / Real.Gamma x = (ascPochhammer ℝ n).eval x := by
    exact (div_eq_iff (Real.Gamma_pos_of_pos hx).ne').2
      (D5.S3.Analytic.KummerRatio.BetaIntegral.gamma_pochhammer hx n)
  have hv := Ring.descPochhammer_smeval_add (R := ℝ)
    (r := c + m - 1) (s := b + m - 1) m (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  simp only [descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval] at hv
  have hl : c + (m : ℝ) - 1 + (b + m - 1) - m + 1 = b + c + m - 1 := by ring
  rw [hl] at hv
  have hgb : Real.Gamma (b + m) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hgc : Real.Gamma (c + m) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  apply (eq_div_iff (mul_ne_zero hgb hgc)).2
  unfold binomialProduct
  rw [sum_mul, hv]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Finset.mem_range_succ_iff.mp hk
  dsimp only
  have hec : c + (m : ℝ) - 1 - k + 1 = c + (m - k : ℕ) := by rw [Nat.cast_sub hkm]; ring
  have heb : b + (m : ℝ) - 1 - (m - k : ℕ) + 1 = b + k := by rw [Nat.cast_sub hkm]; ring
  rw [hec, heb, ← ratio (c + (m - k : ℕ)) (by positivity) k,
    ← ratio (b + k) (by positivity) (m - k)]
  have hec' : c + (m - k : ℕ) + k = c + m := by rw [Nat.cast_sub hkm]; ring
  have heb' : b + (k : ℝ) + (m - k : ℕ) = b + m := by rw [Nat.cast_sub hkm]; ring
  rw [hec', heb']
  have hgbk : Real.Gamma (b + k) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hgck : Real.Gamma (c + (m - k : ℕ)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  field_simp [hgbk, hgck]

/-- Identity (3.11), stated as a finite sum. The m=0 case needs no positivity
of the displayed Pochhammer argument. -/
theorem reciprocalGamma_sum (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (m : ℕ) :
    (∑ k ∈ range (m + 1),
      1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
        Real.Gamma (b + k) * Real.Gamma (c + (m - k)))) =
    (ascPochhammer ℝ m).eval (b + c + m - 1) /
      ((m.factorial : ℝ) * Real.Gamma (b + m) * Real.Gamma (c + m)) := by
  calc
    _ = productCoeff (fun k => 1 / Real.Gamma (b + k))
        (fun k => 1 / Real.Gamma (c + k)) m := by
      unfold productCoeff
      apply sum_congr rfl
      intro k hk
      dsimp only
      rw [Nat.cast_sub (Nat.le_of_lt_succ (mem_range.mp hk))]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = _ := by
      rw [productCoeff_eq, binomialGamma_sum m b c hb hc]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem gamma_balanced_shift (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Real.Gamma (a + α) * Real.Gamma (a + β) ≤
      Real.Gamma a * Real.Gamma (a + α + β) := by
  by_cases hz : α + β = 0
  · have hαz : α = 0 := by linarith
    have hβz : β = 0 := (eq_zero_iff_eq_zero_of_add_eq_zero hz).mp hαz
    simp [hαz, hβz]
  · have ht : 0 < α + β := lt_of_le_of_ne (add_nonneg hα hβ) (Ne.symm hz)
    have hw : β / (α + β) + α / (α + β) = 1 := by
      field_simp [ne_of_gt ht]
      <;> ring
    have hw' : α / (α + β) + β / (α + β) = 1 := by linarith
    have harg1 : β / (α + β) * a + α / (α + β) * (a + α + β) = a + α := by
      field_simp [ne_of_gt ht]
      <;> ring
    have harg2 : α / (α + β) * a + β / (α + β) * (a + α + β) = a + β := by
      field_simp [ne_of_gt ht]
      <;> ring
    have h1 := Real.convexOn_log_Gamma.2 ha
      (show 0 < a + α + β by linarith)
      (div_nonneg hβ (le_of_lt ht)) (div_nonneg hα (le_of_lt ht)) hw
    have h2 := Real.convexOn_log_Gamma.2 ha
      (show 0 < a + α + β by linarith)
      (div_nonneg hα (le_of_lt ht)) (div_nonneg hβ (le_of_lt ht)) hw'
    simp only [Function.comp_apply, smul_eq_mul] at h1 h2
    rw [harg1] at h1
    rw [harg2] at h2
    have hlog : Real.log (Real.Gamma (a + α)) + Real.log (Real.Gamma (a + β)) ≤
        Real.log (Real.Gamma a) + Real.log (Real.Gamma (a + α + β)) := by
      calc
        _ ≤ (β / (α + β) * Real.log (Real.Gamma a) +
              α / (α + β) * Real.log (Real.Gamma (a + α + β))) +
            (α / (α + β) * Real.log (Real.Gamma a) +
              β / (α + β) * Real.log (Real.Gamma (a + α + β))) := add_le_add h1 h2
        _ = (β / (α + β) + α / (α + β)) * Real.log (Real.Gamma a) +
              (α / (α + β) + β / (α + β)) *
                Real.log (Real.Gamma (a + α + β)) := by ring
        _ = _ := by rw [hw, hw', one_mul, one_mul]
    have hp := Real.Gamma_pos_of_pos ha
    have hpα := Real.Gamma_pos_of_pos (show 0 < a + α by linarith)
    have hpβ := Real.Gamma_pos_of_pos (show 0 < a + β by linarith)
    have hpαβ := Real.Gamma_pos_of_pos (show 0 < a + α + β by linarith)
    apply (Real.log_le_log_iff (mul_pos hpα hpβ) (mul_pos hp hpαβ)).mp
    rw [Real.log_mul (ne_of_gt hpα) (ne_of_gt hpβ),
      Real.log_mul (ne_of_gt hp) (ne_of_gt hpαβ)]
    exact hlog

/-- The unpaired reciprocal-gamma kernel M from (3.3). -/
def kernel (a α β : ℝ) (m k : ℕ) : ℝ :=
  (1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ))) *
    (1 / (Real.Gamma (a + α + k) * Real.Gamma (a + β + (m - k))) -
      1 / (Real.Gamma (a + k) * Real.Gamma (a + α + β + (m - k))))

/-- The total unpaired kernel is nonnegative for all nonnegative real shifts.
This is the weak sum assertion needed by the weighting principle; it does
not supply the separate one-sign-change hypothesis for the paired kernel. -/
theorem kernel_sum_nonneg (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (m : ℕ) :
    0 ≤ ∑ k ∈ range (m + 1), kernel a α β m k := by
  have hsum : (∑ k ∈ range (m + 1), kernel a α β m k) =
      (ascPochhammer ℝ m).eval (2 * a + α + β + m - 1) / (m.factorial : ℝ) *
        (1 / (Real.Gamma (a + α + m) * Real.Gamma (a + β + m)) -
          1 / (Real.Gamma (a + m) * Real.Gamma (a + α + β + m))) := by
    calc
      _ = (∑ k ∈ range (m + 1),
          1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
            Real.Gamma (a + α + k) * Real.Gamma (a + β + (m - k)))) -
          ∑ k ∈ range (m + 1),
            1 / ((k.factorial : ℝ) * ((m - k).factorial : ℝ) *
              Real.Gamma (a + k) * Real.Gamma (a + α + β + (m - k))) := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro k _
        simp only [kernel, div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
      _ = _ := by
        rw [reciprocalGamma_sum (a + α) (a + β) (by linarith) (by linarith) m,
          reciprocalGamma_sum a (a + α + β) ha (by linarith) m]
        rw [show (a + α) + (a + β) + (m : ℝ) - 1 =
            2 * a + α + β + m - 1 by ring,
          show a + (a + α + β) + (m : ℝ) - 1 =
            2 * a + α + β + m - 1 by ring]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hp : 0 ≤ (ascPochhammer ℝ m).eval (2 * a + α + β + m - 1) := by
    cases m with
    | zero => simp
    | succ n =>
      apply le_of_lt
      apply ascPochhammer_pos
      push_cast
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  have hbal := gamma_balanced_shift (a + m) α β (by positivity) hα hβ
  have harg1 : (a + (m : ℝ)) + α = a + α + m := add_right_comm a (m : ℝ) α
  have harg2 : (a + (m : ℝ)) + β = a + β + m := add_right_comm a (m : ℝ) β
  have harg3 : (a + (m : ℝ)) + α + β = a + α + β + m := by ring
  rw [harg3, harg1, harg2] at hbal
  have hden : 0 < Real.Gamma (a + α + m) * Real.Gamma (a + β + m) :=
    mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  rw [hsum]
  exact mul_nonneg (div_nonneg hp (by positivity))
    (sub_nonneg.mpr (one_div_le_one_div_of_le hden hbal))

end D5.S3.Analytic.KarpZhangGamma.Kernel


namespace D5.S3.Analytic.KarpZhangGamma.Result

open Smoothing Kernel

/-- The paired kernel counts the middle index only once. -/
def pairedKernel (a α β : ℝ) (m k : ℕ) : ℝ :=
  if 2 * k < m then kernel a α β m k + kernel a α β m (m - k)
  else kernel a α β m k

private def reciprocalPair (x z : ℝ) : ℝ :=
  1 / (Real.Gamma x * Real.Gamma z)

private def fourBracket (x z α β : ℝ) : ℝ :=
  reciprocalPair (x + α) (z + β) + reciprocalPair (x + β) (z + α) -
    reciprocalPair x (z + α + β) - reciprocalPair (x + α + β) z

private theorem reciprocalPair_balanced (x α β : ℝ) (hx : 0 < x)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    reciprocalPair x (x + α + β) ≤ reciprocalPair (x + α) (x + β) := by
  exact one_div_le_one_div_of_le
    (mul_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos (by linarith))) (gamma_balanced_shift x α β hx hα hβ)

private theorem reciprocalPair_step (x z : ℝ) (hx : 1 < x) (hz : 0 < z) :
    reciprocalPair (x - 1) (z + 1) = reciprocalPair x z * ((x - 1) / z) := by
  have hΓ : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
    convert Real.Gamma_add_one (show x - 1 ≠ 0 by linarith) using 1 <;> ring
  unfold reciprocalPair
  rw [hΓ, Real.Gamma_add_one (ne_of_gt hz)]
  field_simp [ne_of_gt hz, show x - 1 ≠ 0 by linarith,
    ne_of_gt (Real.Gamma_pos_of_pos (show 0 < x - 1 by linarith)),
    ne_of_gt (Real.Gamma_pos_of_pos hz)]
  <;> ring

private def recurrenceFactor (S x : ℝ) : ℝ := (x - 1) / (S - x)

private theorem recurrenceFactor_mono (S x z : ℝ) (hS : 1 ≤ S)
    (hxz : x ≤ z) (hz : z < S) : recurrenceFactor S x ≤ recurrenceFactor S z := by
  unfold recurrenceFactor
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hxz) (sub_nonneg.mpr hS)]

private theorem recurrenceFactor_increment (S x α β : ℝ) (hS : 1 ≤ S)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hd : x + α + β < S) :
    recurrenceFactor S (x + β) - recurrenceFactor S x ≤
      recurrenceFactor S (x + α + β) - recurrenceFactor S (x + α) := by
  have hd0 : 0 < S - (x + α + β) := sub_pos.mpr hd
  have hd1 : 0 < S - (x + α) := by linarith
  have hd2 : 0 < S - (x + β) := by linarith
  have hd3 : 0 < S - x := by linarith
  have hfirst : recurrenceFactor S (x + β) - recurrenceFactor S x =
      β * (S - 1) / ((S - (x + β)) * (S - x)) := by
    unfold recurrenceFactor
    field_simp [ne_of_gt hd2, ne_of_gt hd3]
    <;> ring
  have hsecond : recurrenceFactor S (x + α + β) - recurrenceFactor S (x + α) =
      β * (S - 1) / ((S - (x + α + β)) * (S - (x + α))) := by
    unfold recurrenceFactor
    field_simp [ne_of_gt hd0, ne_of_gt hd1]
    <;> ring
  have hden : (S - (x + α + β)) * (S - (x + α)) ≤
      (S - (x + β)) * (S - x) :=
    mul_le_mul (by linarith) (by linarith) (le_of_lt hd1) (le_of_lt hd2)
  rw [hfirst, hsecond, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hd0 hd1) hden)
    (mul_nonneg hβ (sub_nonneg.mpr hS))

/-- Backward propagation of a nonpositive four-term bracket. The recurrence
factor has increasing increments; no differentiability of Gamma is needed. -/
private theorem fourBracket_backward (x z α β : ℝ) (hx : 1 < x) (hxz : x ≤ z)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hB : fourBracket x z α β ≤ 0) :
    fourBracket (x - 1) (z + 1) α β ≤ 0 := by
  let S := x + z + α + β
  let u := reciprocalPair (x + α) (z + β)
  let v := reciprocalPair (x + β) (z + α)
  let r := reciprocalPair x (z + α + β)
  let s := reciprocalPair (x + α + β) z
  have hβ : 0 ≤ β := hα.trans hαβ
  have hz : 0 < z := by linarith
  have hru : r ≤ u := by
    have h := reciprocalPair_balanced x α (z - x + β) (by linarith) hα
      (by linarith)
    change reciprocalPair x (z + α + β) ≤ reciprocalPair (x + α) (z + β)
    simpa only [show x + α + (z - x + β) = z + α + β by ring,
      show x + (z - x + β) = z + β by ring] using h
  have huv : u ≤ v := by
    have h := reciprocalPair_balanced (x + α) (β - α) (z - x)
      (by linarith) (by linarith) (by linarith)
    change reciprocalPair (x + α) (z + β) ≤ reciprocalPair (x + β) (z + α)
    rw [show x + α + (β - α) + (z - x) = z + β by ring,
      show x + α + (β - α) = x + β by ring,
      show x + α + (z - x) = z + α by ring] at h
    exact h
  have hs : 0 ≤ s := by
    dsimp [s, reciprocalPair]
    exact le_of_lt (one_div_pos.mpr (mul_pos (Real.Gamma_pos_of_pos (by linarith))
      (Real.Gamma_pos_of_pos hz)))
  have hvs : v ≤ s := by dsimp [fourBracket] at hB; dsimp [u, v, r, s] at *; linarith
  have hrs : r ≤ s := hru.trans (huv.trans hvs)
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hd : x + α + β < S := by dsimp [S]; linarith
  have hbc := recurrenceFactor_mono S (x + α) (x + β) hS (by linarith)
    (by linarith)
  have hab := recurrenceFactor_mono S x (x + α) hS (by linarith) (by linarith)
  have hb0 : 0 ≤ recurrenceFactor S (x + α) := by
    dsimp [recurrenceFactor]
    exact div_nonneg (by linarith) (by linarith)
  have hconv := recurrenceFactor_increment S x α β hS hα hβ hd
  have hu : reciprocalPair (x - 1 + α) (z + 1 + β) =
      u * recurrenceFactor S (x + α) := by
    have h := reciprocalPair_step (x + α) (z + β) (by linarith) (by linarith)
    dsimp [u, recurrenceFactor]
    rw [show S - (x + α) = z + β by dsimp [S]; ring]
    simpa only [show x + α - 1 = x - 1 + α by ring,
      show z + β + 1 = z + 1 + β by ring] using h
  have hv : reciprocalPair (x - 1 + β) (z + 1 + α) =
      v * recurrenceFactor S (x + β) := by
    have h := reciprocalPair_step (x + β) (z + α) (by linarith) (by linarith)
    dsimp [v, recurrenceFactor]
    rw [show S - (x + β) = z + α by dsimp [S]; ring]
    simpa only [show x + β - 1 = x - 1 + β by ring,
      show z + α + 1 = z + 1 + α by ring] using h
  have hr : reciprocalPair (x - 1) (z + 1 + α + β) =
      r * recurrenceFactor S x := by
    have h := reciprocalPair_step x (z + α + β) hx (by linarith)
    dsimp [r, recurrenceFactor]
    rw [show S - x = z + α + β by dsimp [S]; ring]
    simpa only [show z + α + β + 1 = z + 1 + α + β by ring] using h
  have ht : reciprocalPair (x - 1 + α + β) (z + 1) =
      s * recurrenceFactor S (x + α + β) := by
    have h := reciprocalPair_step (x + α + β) z (by linarith) hz
    dsimp [s, recurrenceFactor]
    rw [show S - (x + α + β) = z by dsimp [S]; ring]
    simpa only [show x + α + β - 1 = x - 1 + α + β by ring] using h
  have hterm := mul_nonpos_of_nonneg_of_nonpos hb0 hB
  have hvterm := mul_le_mul_of_nonneg_right hvs (sub_nonneg.mpr hbc)
  have hrterm := mul_le_mul_of_nonneg_right hrs (sub_nonneg.mpr hab)
  have hlast := mul_nonpos_of_nonneg_of_nonpos hs
    (show (recurrenceFactor S (x + β) - recurrenceFactor S x) -
      (recurrenceFactor S (x + α + β) - recurrenceFactor S (x + α)) ≤ 0 by linarith)
  change u + v - r - s ≤ 0 at hB
  change recurrenceFactor S (x + α) * (u + v - r - s) ≤ 0 at hterm
  unfold fourBracket
  rw [hu, hv, hr, ht]
  nlinarith

private theorem fourBracket_swap (x z α β : ℝ) :
    fourBracket x z α β = fourBracket x z β α := by
  unfold fourBracket
  rw [show z + α + β = z + β + α by ring,
    show x + α + β = x + β + α by ring]
  ring

private theorem bracket_backward_nat (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (m k : ℕ) (hk : k + 1 ≤ m / 2)
    (hB : fourBracket (a + (k + 1 : ℕ)) (a + (m - (k + 1))) α β ≤ 0) :
    fourBracket (a + k) (a + (m - k)) α β ≤ 0 := by
  have hstep (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β)
      (h : fourBracket (a + (k + 1 : ℕ)) (a + (m - (k + 1))) α β ≤ 0) :
      fourBracket (a + k) (a + (m - k)) α β ≤ 0 := by
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := Nat.cast_add_one k
    have horder : k + 1 ≤ m - (k + 1) := by omega
    have horder' : ((k + 1 : ℕ) : ℝ) ≤ ((m - (k + 1) : ℕ) : ℝ) := Nat.cast_le.mpr horder
    rw [Nat.cast_sub (by omega : k + 1 ≤ m), hcast] at horder'
    have h := fourBracket_backward (a + (k + 1 : ℕ))
      (a + (m - (k + 1))) α β (by
        rw [hcast]
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg' k
        linarith)
      (by rw [hcast]; linarith only [horder']) hα hαβ h
    have hxarg : a + ((k + 1 : ℕ) : ℝ) - 1 = a + k := by rw [hcast]; ring
    have hzarg : a + ((m : ℝ) - ((k : ℝ) + 1)) + 1 = a + (m - k) := by ring
    rwa [hxarg, hzarg] at h
  by_cases hab : α ≤ β
  · exact hstep α β hα hab hB
  · rw [fourBracket_swap] at hB ⊢
    exact hstep β α hβ (le_of_not_ge hab) hB

private theorem pairedKernel_bracket (a α β : ℝ) (m k : ℕ) (hk : k ≤ m / 2) :
    pairedKernel a α β m k =
      fourBracket (a + k) (a + (m - k)) α β /
        (if 2 * k < m then (k.factorial : ℝ) * ((m - k).factorial : ℝ)
         else 2 * (k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
  have hmk : m - (m - k) = k := by omega
  have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) :=
    Nat.cast_sub (by omega)
  unfold pairedKernel kernel fourBracket reciprocalPair
  split_ifs with h
  · rw [hmk, hcast, show (m : ℝ) - ((m : ℝ) - (k : ℝ)) = k by ring]
    simp only [add_assoc, add_left_comm, add_comm, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  · have hmid : m - k = k := by omega
    have hmid' : (m : ℝ) - (k : ℝ) = k := by rw [← hcast, hmid]
    rw [hmid, hmid']
    simp only [add_assoc, add_left_comm, add_comm, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring

/-- The weak sign pattern of `pairedKernel_sign`, including zero shifts: a positive paired
entry cannot be followed by a negative paired entry. -/
theorem pairedKernel_sign (a α β : ℝ) (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (m : ℕ) : ∀ i ≤ m / 2, ∀ j ≤ m / 2, i < j →
      0 < pairedKernel a α β m i → 0 ≤ pairedKernel a α β m j := by
  intro i hi j hj hij hpos
  have hden (k : ℕ) : 0 <
      (if 2 * k < m then (k.factorial : ℝ) * ((m - k).factorial : ℝ)
       else 2 * (k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
    split_ifs <;> positivity
  rw [pairedKernel_bracket a α β m i hi] at hpos
  have hBi : 0 < fourBracket (a + i) (a + (m - i)) α β :=
    (div_pos_iff_of_pos_right (hden i)).mp hpos
  rw [pairedKernel_bracket a α β m j hj]
  apply div_nonneg _ (le_of_lt (hden j))
  by_contra hn
  have hBj : fourBracket (a + j) (a + (m - j)) α β ≤ 0 := le_of_lt (lt_of_not_ge hn)
  have hprop : ∀ d, i + d ≤ m / 2 →
      fourBracket (a + (i + d : ℕ)) (a + (m - (i + d : ℕ))) α β ≤ 0 →
      fourBracket (a + i) (a + (m - i)) α β ≤ 0 := by
    intro d
    induction d with
    | zero => intro _ h; simpa only [Nat.add_zero] using h
    | succ d ih =>
      intro hd h
      apply ih (by omega)
      apply bracket_backward_nat a α β ha hα hβ m (i + d) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h
  have h := hprop (j - i) (by omega) (by simpa only [show i + (j - i) = j by omega] using hBj)
  exact (not_le_of_gt hBi) h

theorem pair_sum (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (m + 1), f k) = ∑ k ∈ range (m / 2 + 1),
      if 2 * k < m then f k + f (m - k) else f k := by
  classical
  have hlow : (range (m + 1)).filter (fun k => 2 * k ≤ m) = range (m / 2 + 1) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  have hhigh : (∑ k ∈ (range (m + 1)).filter (fun k => ¬ 2 * k ≤ m), f k) =
      ∑ k ∈ (range (m / 2 + 1)).filter (fun k => 2 * k < m), f (m - k) := by
    apply sum_bij (fun k _ => m - k)
    · intro k hk
      simp only [mem_filter, mem_range] at hk ⊢
      omega
    · intro k hk l hl hkl
      simp only [mem_filter, mem_range] at hk hl
      omega
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      refine ⟨m - k, ?_, ?_⟩
      · simp only [mem_filter, mem_range]
        omega
      · omega
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      congr 1
      omega
  rw [← sum_filter_add_sum_filter_not (range (m + 1)) (fun k => 2 * k ≤ m) f,
    hlow, hhigh, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  split_ifs <;> ring

/-- Exact finite pairing for any symmetric weights; a middle term is not doubled. -/
theorem finite_pairing (a α β : ℝ) (m : ℕ) (W : ℕ → ℝ)
    (hsym : ∀ k ≤ m, W (m - k) = W k) :
    (∑ k ∈ range (m + 1), kernel a α β m k * W k) =
      ∑ k ∈ range (m / 2 + 1), pairedKernel a α β m k * W k := by
  rw [pair_sum]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := mem_range.mp hk; omega
  unfold pairedKernel
  split_ifs with h
  · rw [hsym k hkm]
    ring
  · rfl

/-- The paired scalar kernel has the same nonnegative total as the unpaired kernel. -/
theorem pairedKernel_sum_nonneg (a α β : ℝ) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (m : ℕ) :
    0 ≤ ∑ k ∈ range (m / 2 + 1), pairedKernel a α β m k := by
  have h := finite_pairing a α β m (fun _ => 1) (by intros; rfl)
  simp only [mul_one] at h
  rw [← h]
  exact kernel_sum_nonneg a α β ha hα hβ m

/-- The degree-(N,m) coefficient of the Turanian of the two-variable
transform H(a;z,w), written with finite Cauchy sums. -/
def transformDelta (y : ℕ → ℝ) (a α β : ℝ) (N m : ℕ) : ℝ :=
  ∑ k ∈ range (m + 1), kernel a α β m k *
    productCoeff (fun r => y (2 * k + r)) (fun r => y (2 * (m - k) + r)) N

/-- `two_variable_nonneg` in coefficient form, for every bidegree and arbitrary
nonnegative real shifts, with no growth or convergence assumption. -/
theorem two_variable_nonneg (y : ℕ → ℝ)
    (hy : D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave y)
    (a α β : ℝ) (ha : 0 < a) (hα : 0 ≤ α) (hβ : 0 ≤ β) (N m : ℕ) :
    0 ≤ transformDelta y a α β N m := by
  have hcomm (f g : ℕ → ℝ) : productCoeff f g N = productCoeff g f N := by
    rw [productCoeff_eq, productCoeff_eq, binomialProduct_comm]
  unfold transformDelta
  rw [finite_pairing a α β m _ (by
    intro k hk
    rw [show m - (m - k) = k by omega]
    exact hcomm _ _)]
  exact smoothed_weighting hy (pairedKernel a α β m) m
    (pairedKernel_sign a α β ha hα hβ m)
    (pairedKernel_sum_nonneg a α β ha hα hβ m) N


end D5.S3.Analytic.KarpZhangGamma.Result
