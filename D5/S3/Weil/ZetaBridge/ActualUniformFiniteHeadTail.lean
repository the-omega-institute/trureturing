/- GID: D5/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualUniformFiniteHeadTail
   mirror-E: none(waiver:uniform-actual-arithmetic-tail-estimate)
   anchors: []
   utility: none
   digest: Uniform finite-head lower tails for the full arithmetic divided-difference column. -/

import D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
import D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling
import D5.S3.Weil.ZetaBridge.PrimePolynomialInterference
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Uniform actual finite-head tails

Finite Lagrange reconstruction, discrete polynomial sampling, signed Abel
summation and the parallelogram identity control both exterior signs. The
symbol and column are those of `WeilArithmeticCouplingJet`, including the
pole, the infinite Gamma series and the finite prime sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail

open scoped BigOperators
open Polynomial
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

private def gamma : ℝ := Real.pi / 4

private def energy (d : ℕ) (p : ℂ[X]) : ℝ :=
  ∑ r ∈ Finset.range d, ‖p.coeff r‖ ^ 2

private def totalEnergy (d N : ℕ) (p q : ℂ[X]) : ℝ :=
  ∑ r ∈ Finset.range d, (N : ℝ) ^ (2 * r) *
    (‖p.coeff r‖ ^ 2 + ‖q.coeff r‖ ^ 2)

private def part (d N : ℕ) (p : ℂ[X]) (odd : Bool) : ℂ[X] :=
  Polynomial.ofFn d (fun r =>
    if Even (r : ℕ) then
      if odd then 0 else p.coeff r * (N : ℂ) ^ (r : ℕ)
    else
      if odd then p.coeff r * (N : ℂ) ^ (r : ℕ) else 0)

private def F₁ (d N : ℕ) (p q : ℂ[X]) : ℂ[X] :=
  part d N p false + C (gamma : ℂ) * part d N q true

private def F₂ (d N : ℕ) (p q : ℂ[X]) : ℂ[X] :=
  part d N p true + C (gamma : ℂ) * part d N q false

private def B₁ (d N : ℕ) (q : ℂ[X]) : ℂ[X] := part d N q true

private def B₂ (d N : ℕ) (q : ℂ[X]) : ℂ[X] := part d N q false

private def remainder (c m : ℕ) : ℝ :=
  (m : ℝ) ^ 2 * smoothWeight c m - gamma

private theorem gamma_bounds : 0 < gamma ∧ gamma < 1 := by
  unfold gamma
  constructor <;> linarith [Real.pi_pos, Real.pi_lt_four]

private theorem energy_nonneg (d : ℕ) (p : ℂ[X]) : 0 ≤ energy d p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem totalEnergy_nonneg (d N : ℕ) (p q : ℂ[X]) :
    0 ≤ totalEnergy d N p q :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity)
    (add_nonneg (sq_nonneg _) (sq_nonneg _)))

private theorem part_coeff (d N : ℕ) (p : ℂ[X]) (odd : Bool)
    {r : ℕ} (hr : r < d) :
    (part d N p odd).coeff r =
      if Even r then (if odd then 0 else p.coeff r * (N : ℂ) ^ r)
      else (if odd then p.coeff r * (N : ℂ) ^ r else 0) := by
  classical
  simp only [part, Polynomial.ofFn_coeff_eq_val_of_lt _ hr]

private theorem part_degree (d N : ℕ) (hd : 0 < d) (p : ℂ[X]) (odd : Bool) :
    (part d N p odd).natDegree < d := by
  classical
  exact Polynomial.ofFn_natDegree_lt hd _

private theorem channel_degrees (d N : ℕ) (hd : 0 < d) (p q : ℂ[X]) :
    (F₁ d N p q).natDegree < d ∧ (F₂ d N p q).natDegree < d ∧
    (B₁ d N q).natDegree < d ∧ (B₂ d N q).natDegree < d := by
  have he (f : ℂ[X]) := part_degree d N hd f false
  have ho (f : ℂ[X]) := part_degree d N hd f true
  have hc (f : ℂ[X]) (b : Bool) :
      (C (gamma : ℂ) * part d N f b).natDegree < d :=
    (Polynomial.natDegree_C_mul_le _ _).trans_lt (part_degree d N hd f b)
  exact ⟨(Polynomial.natDegree_add_le _ _).trans_lt
      (max_lt (he p) (hc q true)),
    (Polynomial.natDegree_add_le _ _).trans_lt
      (max_lt (ho p) (hc q false)), ho q, he q⟩

private theorem scaled_monomial (N m r : ℕ) (hN : 0 < N) :
    (N : ℂ) ^ r * ((m : ℂ) / (N : ℂ)) ^ r = (m : ℂ) ^ r := by
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← mul_pow, mul_div_cancel₀ _ hNz]

private theorem part_evaluations (d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (p : ℂ[X]) (hp : p.natDegree < d) (m : ℕ) :
    p.eval (m : ℂ) = (part d N p false).eval ((m : ℂ) / (N : ℂ)) +
      (part d N p true).eval ((m : ℂ) / (N : ℂ)) ∧
    p.eval (-(m : ℂ)) = (part d N p false).eval ((m : ℂ) / (N : ℂ)) -
      (part d N p true).eval ((m : ℂ) / (N : ℂ)) := by
  have hde := part_degree d N hd p false
  have hdo := part_degree d N hd p true
  simp only [Polynomial.eval_eq_sum_range' hp,
    Polynomial.eval_eq_sum_range' hde, Polynomial.eval_eq_sum_range' hdo]
  constructor
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [part_coeff d N p false (Finset.mem_range.mp hr),
      part_coeff d N p true (Finset.mem_range.mp hr)]
    by_cases he : Even r <;> simp [he, mul_assoc, scaled_monomial N m r hN]
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [part_coeff d N p false (Finset.mem_range.mp hr),
      part_coeff d N p true (Finset.mem_range.mp hr)]
    by_cases he : Even r
    · simp [he, he.neg_pow, mul_assoc, scaled_monomial N m r hN]
    · have ho : Odd r := Nat.not_even_iff_odd.mp he
      simp [he, ho.neg_pow, mul_assoc, scaled_monomial N m r hN]

private theorem coefficient_channels (d N : ℕ) (p q : ℂ[X]) :
    energy d (F₁ d N p q) + energy d (F₂ d N p q) =
      totalEnergy d N p (C (gamma : ℂ) * q) ∧
    energy d (B₁ d N q) + energy d (B₂ d N q) =
      ∑ r ∈ Finset.range d, (N : ℝ) ^ (2 * r) * ‖q.coeff r‖ ^ 2 := by
  classical
  have hscale (a : ℂ) (r : ℕ) :
      ‖a * (N : ℂ) ^ r‖ ^ 2 = (N : ℝ) ^ (2 * r) * ‖a‖ ^ 2 := by
    rw [norm_mul, norm_pow]
    simp only [Complex.norm_natCast]
    rw [mul_pow, ← pow_mul, Nat.mul_comm r 2]
    ring
  constructor
  · unfold energy totalEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [F₁, F₂, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      part_coeff d N p false (Finset.mem_range.mp hr),
      part_coeff d N p true (Finset.mem_range.mp hr),
      part_coeff d N q false (Finset.mem_range.mp hr),
      part_coeff d N q true (Finset.mem_range.mp hr)]
    by_cases he : Even r <;>
      simp [he, hscale, norm_mul, norm_pow, Complex.norm_natCast,
        mul_pow, Complex.norm_real, sq_abs, ← pow_mul, Nat.mul_comm r 2] <;> ring
  · unfold energy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [B₁, B₂, part_coeff d N q false (Finset.mem_range.mp hr),
      part_coeff d N q true (Finset.mem_range.mp hr)]
    by_cases he : Even r <;>
      simp [he, hscale, norm_mul, norm_pow, Complex.norm_natCast,
        mul_pow, ← pow_mul, Nat.mul_comm r 2] <;> ring

private theorem channel_energy_bounds (d N : ℕ) (p q : ℂ[X]) :
    gamma ^ 2 * totalEnergy d N p q ≤
      energy d (F₁ d N p q) + energy d (F₂ d N p q) ∧
    energy d (F₁ d N p q) + energy d (F₂ d N p q) ≤ totalEnergy d N p q ∧
    energy d (B₁ d N q) + energy d (B₂ d N q) ≤ totalEnergy d N p q := by
  have hg : gamma ^ 2 ≤ 1 := by nlinarith [gamma_bounds.1, gamma_bounds.2]
  obtain ⟨hF, hB⟩ := coefficient_channels d N p q
  have hex : totalEnergy d N p (C (gamma : ℂ) * q) =
      ∑ r ∈ Finset.range d, (N : ℝ) ^ (2 * r) *
        (‖p.coeff r‖ ^ 2 + gamma ^ 2 * ‖q.coeff r‖ ^ 2) := by
    simp only [totalEnergy, Polynomial.coeff_C_mul, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hF, hex, hB]
  refine ⟨?_, ?_, ?_⟩
  · unfold totalEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have ht : 0 ≤ (N : ℝ) ^ (2 * r) := by positivity
    have hp := mul_nonneg (sub_nonneg.mpr hg) (sq_nonneg ‖p.coeff r‖)
    nlinarith only [mul_nonneg ht hp]
  · apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hg) (sq_nonneg ‖q.coeff r‖)]
  · apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _))
      (by positivity)

private theorem actual_symbol (c m : ℕ) (hm : 0 < m) :
    arithmeticBoundarySymbol c (m : ℤ) =
      -(gamma + primeSymbol c (m : ℤ) + remainder c m) := by
  rw [arithmetic_symbol_smooth_split c hm, owner_prime_sum_eq]
  unfold remainder
  ring

private theorem exact_channels (c d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (p q : ℂ[X]) (hp : p.natDegree < d) (hq : q.natDegree < d)
    (m : ℕ) (hm : 0 < m) :
    let t : ℂ := (m : ℂ) / (N : ℂ)
    let a : ℂ := ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ)
    let U₁ : ℂ := (F₁ d N p q).eval t + a * (B₁ d N q).eval t
    let U₂ : ℂ := (F₂ d N p q).eval t + a * (B₂ d N q).eval t
    p.eval (m : ℂ) - (arithmeticBoundarySymbol c (m : ℤ) : ℂ) * q.eval (m : ℂ)
        = U₁ + U₂ ∧
    p.eval (-(m : ℂ)) - (arithmeticBoundarySymbol c (-(m : ℤ)) : ℂ) *
        q.eval (-(m : ℂ)) = U₁ - U₂ ∧
    ‖p.eval (m : ℂ) - (arithmeticBoundarySymbol c (m : ℤ) : ℂ) * q.eval (m : ℂ)‖ ^ 2 +
      ‖p.eval (-(m : ℂ)) - (arithmeticBoundarySymbol c (-(m : ℤ)) : ℂ) *
        q.eval (-(m : ℂ))‖ ^ 2 = 2 * (‖U₁‖ ^ 2 + ‖U₂‖ ^ 2) := by
  dsimp only
  obtain ⟨hp_pos, hp_neg⟩ := part_evaluations d N hd hN p hp m
  obtain ⟨hq_pos, hq_neg⟩ := part_evaluations d N hd hN q hq m
  have hs := actual_symbol c m hm
  have hn := WeilArithmeticCouplingParityGram.arithmetic_boundary_symbol_neg c (m : ℤ)
  have h_pos : p.eval (m : ℂ) - (arithmeticBoundarySymbol c (m : ℤ) : ℂ) *
      q.eval (m : ℂ) =
      ((F₁ d N p q).eval ((m : ℂ) / (N : ℂ)) +
        ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
          (B₁ d N q).eval ((m : ℂ) / (N : ℂ))) +
      ((F₂ d N p q).eval ((m : ℂ) / (N : ℂ)) +
        ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
          (B₂ d N q).eval ((m : ℂ) / (N : ℂ))) := by
    rw [hp_pos, hq_pos, hs]
    simp only [F₁, F₂, B₁, B₂, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Complex.ofReal_neg, Complex.ofReal_add]
    ring
  have h_neg : p.eval (-(m : ℂ)) - (arithmeticBoundarySymbol c (-(m : ℤ)) : ℂ) *
      q.eval (-(m : ℂ)) =
      ((F₁ d N p q).eval ((m : ℂ) / (N : ℂ)) +
        ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
          (B₁ d N q).eval ((m : ℂ) / (N : ℂ))) -
      ((F₂ d N p q).eval ((m : ℂ) / (N : ℂ)) +
        ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
          (B₂ d N q).eval ((m : ℂ) / (N : ℂ))) := by
    rw [hp_neg, hq_neg, hn, hs]
    simp only [F₁, F₂, B₁, B₂, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Complex.ofReal_neg, Complex.ofReal_add]
    ring
  refine ⟨h_pos, h_neg, ?_⟩
  rw [h_pos, h_neg]
  exact parallelogram_law_with_norm ℂ _ _

private theorem square_expansion (F B : ℂ) (a : ℝ) :
    ‖F + (a : ℂ) * B‖ ^ 2 = ‖F‖ ^ 2 +
      2 * a * (F * star B).re + a ^ 2 * ‖B‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem square_error (F B : ℂ) (p δ : ℝ) :
    ‖F‖ ^ 2 + 2 * p * (F * star B).re -
      |δ| * (‖F‖ ^ 2 + ‖B‖ ^ 2) ≤
      ‖F + ((p + δ : ℝ) : ℂ) * B‖ ^ 2 := by
  have hre : |(F * star B).re| ≤ ‖F‖ * ‖B‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (F * star B)
  have hcs : 2 * |(F * star B).re| ≤ ‖F‖ ^ 2 + ‖B‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖F‖ - ‖B‖), hre]
  have hδ : -(|δ| * |(F * star B).re|) ≤ δ * (F * star B).re := by
    simpa only [abs_mul] using neg_abs_le (δ * (F * star B).re)
  have he := mul_le_mul_of_nonneg_left hcs (abs_nonneg δ)
  have hsq := mul_nonneg (sq_nonneg (p + δ)) (sq_nonneg ‖B‖)
  rw [square_expansion]
  nlinarith only [hδ, he, hsq]

private theorem evaluation_bound (d : ℕ) (F : ℂ[X]) (hF : F.natDegree < d)
    (t : ℂ) (ht : ‖t‖ ≤ 2) :
    ‖F.eval t‖ ^ 2 ≤ (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) * energy d F := by
  have htri : ‖F.eval t‖ ≤ ∑ r ∈ Finset.range d, ‖F.coeff r‖ * ‖t‖ ^ r := by
    rw [Polynomial.eval_eq_sum_range' hF]
    simpa only [norm_mul, norm_pow] using
      norm_sum_le (Finset.range d) (fun r => F.coeff r * t ^ r)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range d)
    (fun r => ‖F.coeff r‖) (fun r => ‖t‖ ^ r)
  have hpow : (∑ r ∈ Finset.range d, (‖t‖ ^ r) ^ 2) ≤
      ∑ r ∈ Finset.range d, (4 : ℝ) ^ r := by
    apply Finset.sum_le_sum
    intro r _
    calc
      (‖t‖ ^ r) ^ 2 ≤ ((2 : ℝ) ^ r) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) (pow_le_pow_left₀ (norm_nonneg _) ht _) 2
      _ = (4 : ℝ) ^ r := by rw [← pow_mul, Nat.mul_comm r 2, pow_mul]; norm_num
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
    (hcs.trans (by
      simpa only [energy, mul_comm] using
        mul_le_mul_of_nonneg_left hpow (energy_nonneg d F)))

private theorem firstMoment_nonneg (c : ℕ) :
    0 ≤ ActualFullSymbolTail.primeFirstMoment c := by
  unfold ActualFullSymbolTail.primeFirstMoment
  exact Finset.sum_nonneg (fun _ _ =>
    div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (norm_nonneg _))

private theorem one_channel_annulus {c : ℕ} (hc : 2 ≤ c) (d N : ℕ)
    (hN : 0 < N) (κ K : ℝ) (hK : 0 ≤ K)
    (hδ : ∀ m : ℕ, 0 < m → |remainder c m| ≤ K / (m : ℝ))
    (F B : ℂ[X]) (hF : F.natDegree < d) (hB : B.natDegree < d)
    (hsampling : κ * (N : ℝ) * energy d F ≤
      ∑ m ∈ Finset.Icc (N + 1) (2 * N), ‖F.eval ((m : ℂ) / (N : ℂ))‖ ^ 2) :
    κ * (N : ℝ) * energy d F -
        2 * ActualFullSymbolTail.primeFirstMoment c *
          (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) * (energy d F + energy d B) -
        K * (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
          (energy d F + energy d B) ≤
      ∑ m ∈ Finset.Icc (N + 1) (2 * N),
        ‖F.eval ((m : ℂ) / (N : ℂ)) +
          ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
            B.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 := by
  classical
  let I := Finset.Icc (N + 1) (2 * N)
  let R : ℝ := ∑ r ∈ Finset.range d, (4 : ℝ) ^ r
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcard : I.card = N := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hpoint (m : ℕ) (hm : m ∈ I) :
      |remainder c m| * (‖F.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 +
          ‖B.eval ((m : ℂ) / (N : ℂ))‖ ^ 2) ≤
        (K / (N : ℝ)) * R * (energy d F + energy d B) := by
    have hmem := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := by omega
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : N ≤ m)
    have hm2 : (m : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hmem.2
    have ht : ‖(m : ℂ) / (N : ℂ)‖ ≤ 2 := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
      exact (div_le_iff₀ hNR).mpr hm2
    have hδN : |remainder c m| ≤ K / (N : ℝ) := by
      refine (hδ m hmpos).trans ?_
      apply (div_le_div_iff₀ hmR hNR).mpr
      exact mul_le_mul_of_nonneg_left hNm hK
    have heF := evaluation_bound d F hF _ ht
    have heB := evaluation_bound d B hB _ ht
    have hsum : ‖F.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 +
        ‖B.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 ≤
        R * (energy d F + energy d B) := by
      dsimp [R]
      nlinarith only [heF, heB]
    calc
      _ ≤ (K / (N : ℝ)) * (‖F.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 +
          ‖B.eval ((m : ℂ) / (N : ℂ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hδN
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (K / (N : ℝ)) * (R *
          (energy d F + energy d B)) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hK hNR.le)
      _ = _ := by ring
  have hsmooth : (∑ m ∈ I, |remainder c m| *
      (‖F.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 +
        ‖B.eval ((m : ℂ) / (N : ℂ))‖ ^ 2)) ≤
      K * R * (energy d F + energy d B) := by
    calc
      _ ≤ ∑ _m ∈ I, (K / (N : ℝ)) * R *
          (energy d F + energy d B) :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp [hNR.ne'] <;> ring
  have hprime := PrimePolynomialInterference.prime_polynomial_interference_bound
    hc d hN F B hF hB
  change |∑ m ∈ I, primeSymbol c (m : ℤ) *
      (F.eval ((m : ℂ) / (N : ℂ)) * star (B.eval ((m : ℂ) / (N : ℂ)))).re| ≤
      ActualFullSymbolTail.primeFirstMoment c * R * (energy d F + energy d B) at hprime
  have hlower := (abs_le.mp hprime).1
  change κ * (N : ℝ) * energy d F ≤
    ∑ m ∈ I, ‖F.eval ((m : ℂ) / (N : ℂ))‖ ^ 2 at hsampling
  have hsq := Finset.sum_le_sum (s := I) (fun m _ =>
    square_error (F.eval ((m : ℂ) / (N : ℂ)))
      (B.eval ((m : ℂ) / (N : ℂ))) (primeSymbol c (m : ℤ))
      (remainder c m))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_assoc] at hsq
  change κ * (N : ℝ) * energy d F -
      2 * ActualFullSymbolTail.primeFirstMoment c * R * (energy d F + energy d B) -
      K * R * (energy d F + energy d B) ≤ _
  linarith

private theorem two_channel_annulus {c : ℕ} (hc : 2 ≤ c) (d N : ℕ)
    (hd : 0 < d) (hN : 0 < N) (h2d : 2 * d ≤ N)
    (κ K : ℝ) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hδ : ∀ m : ℕ, 0 < m → |remainder c m| ≤ K / (m : ℝ))
    (hsampling : ∀ M : ℕ, 2 * d ≤ M → ∀ f : ℂ[X], f.natDegree < d →
      κ * (M : ℝ) * energy d f ≤
        ∑ m ∈ Finset.Icc (M + 1) (2 * M), ‖f.eval ((m : ℂ) / (M : ℂ))‖ ^ 2)
    (p q : ℂ[X]) :
    (κ * gamma ^ 2 * (N : ℝ) -
      (∑ r ∈ Finset.range d, (4 : ℝ) ^ r) *
        (4 * ActualFullSymbolTail.primeFirstMoment c + 2 * K)) *
      totalEnergy d N p q ≤
      ∑ m ∈ Finset.Icc (N + 1) (2 * N),
        (‖(F₁ d N p q).eval ((m : ℂ) / (N : ℂ)) +
          ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
            (B₁ d N q).eval ((m : ℂ) / (N : ℂ))‖ ^ 2 +
         ‖(F₂ d N p q).eval ((m : ℂ) / (N : ℂ)) +
          ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
            (B₂ d N q).eval ((m : ℂ) / (N : ℂ))‖ ^ 2) := by
  obtain ⟨hF₁, hF₂, hB₁, hB₂⟩ := channel_degrees d N hd p q
  have h₁ := one_channel_annulus hc d N hN κ K hK hδ
    (F₁ d N p q) (B₁ d N q) hF₁ hB₁ (hsampling N h2d _ hF₁)
  have h₂ := one_channel_annulus hc d N hN κ K hK hδ
    (F₂ d N p q) (B₂ d N q) hF₂ hB₂ (hsampling N h2d _ hF₂)
  obtain ⟨hFlo, hFhi, hBhi⟩ := channel_energy_bounds d N p q
  let R : ℝ := ∑ r ∈ Finset.range d, (4 : ℝ) ^ r
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => by positivity)
  have hH := firstMoment_nonneg c
  have hsample := mul_le_mul_of_nonneg_left hFlo
    (mul_nonneg hκ.le (Nat.cast_nonneg (α := ℝ) N))
  have hprime := mul_le_mul_of_nonneg_left (add_le_add hFhi hBhi)
    (show 0 ≤ 2 * ActualFullSymbolTail.primeFirstMoment c * R by positivity)
  have hsmooth := mul_le_mul_of_nonneg_left (add_le_add hFhi hBhi)
    (show 0 ≤ K * R by positivity)
  rw [Finset.sum_add_distrib]
  dsimp [R] at hprime hsmooth
  nlinarith only [h₁, h₂, hsample, hprime, hsmooth]

private theorem annulus_reindex (N : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc (N + 1) (2 * N), f m) =
      ∑ j ∈ Finset.range N, f (N + j + 1) := by
  calc
    _ = ∑ m ∈ Finset.Ico (N + 1) (2 * N + 1), f m := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    _ = ∑ j ∈ Finset.range ((2 * N + 1) - (N + 1)), f ((N + 1) + j) :=
      Finset.sum_Ico_eq_sum_range f (N + 1) (2 * N + 1)
    _ = _ := by
      have hlen : (2 * N + 1) - (N + 1) = N := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      omega

private theorem nodal_exterior_bound (S : Finset ℤ) (A N : ℕ)
    (hbound : ∀ n ∈ S, n.natAbs ≤ A) (hAN : A ≤ N)
    (m : ℤ) (hm : (N : ℝ) < |(m : ℝ)|) (hm2 : |(m : ℝ)| ≤ 2 * (N : ℝ)) :
    m ∉ S ∧ (ActualNodalCoercivity.D S).eval (m : ℂ) ≠ 0 ∧
      ‖(ActualNodalCoercivity.D S).eval (m : ℂ)‖ ≤ (3 * (N : ℝ)) ^ S.card := by
  classical
  have hnode (n : ℤ) (hn : n ∈ S) : |(n : ℝ)| ≤ (A : ℝ) := by
    have h := hbound n hn
    have heq : |(n : ℝ)| = (n.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    rw [heq]
    exact_mod_cast h
  have hANR : (A : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAN
  have hnot : m ∉ S := by
    intro hmS
    exact (not_le_of_gt hm) ((hnode m hmS).trans hANR)
  refine ⟨hnot, ?_, ?_⟩
  · apply Lagrange.eval_nodal_not_at_node
    intro n hn hmn
    have heq : m = n := by exact_mod_cast hmn
    exact hnot (heq.symm ▸ hn)
  · unfold ActualNodalCoercivity.D
    rw [Lagrange.eval_nodal, norm_prod]
    calc
      (∏ n ∈ S, ‖(m : ℂ) - (n : ℂ)‖) ≤ ∏ _n ∈ S, 3 * (N : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro n hn
        calc
          ‖(m : ℂ) - (n : ℂ)‖ ≤ ‖(m : ℂ)‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
          _ ≤ 3 * (N : ℝ) := by
            rw [Complex.norm_intCast, Complex.norm_intCast]
            linarith [hnode n hn]
      _ = _ := by simp

private theorem actual_numerator_bound (c : ℕ) (S : Finset ℤ) (hS : S.Nonempty)
    (A N : ℕ) (hbound : ∀ n ∈ S, n.natAbs ≤ A) (hAN : A ≤ N)
    (v : ℤ → ℂ) (m : ℤ) (hm : (N : ℝ) < |(m : ℝ)|)
    (hm2 : |(m : ℝ)| ≤ 2 * (N : ℝ)) :
    ‖(ActualNodalCoercivity.P c S v).eval (m : ℂ) -
      (arithmeticBoundarySymbol c m : ℂ) * (ActualNodalCoercivity.Q S v).eval (m : ℂ)‖ ^ 2 ≤
      Real.pi ^ 2 * (3 * (N : ℝ)) ^ (2 * S.card) * ‖couplingColumn c S v m‖ ^ 2 := by
  obtain ⟨hnot, hDne, hD⟩ := nodal_exterior_bound S A N hbound hAN m hm hm2
  have hmodel := (ActualNodalCoercivity.actual_nodal_polynomial_model c S hS v).2.2 m hnot
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hquot : couplingColumn c S v m =
      ((ActualNodalCoercivity.P c S v).eval (m : ℂ) -
        (arithmeticBoundarySymbol c m : ℂ) * (ActualNodalCoercivity.Q S v).eval (m : ℂ)) /
      ((Real.pi : ℂ) * (ActualNodalCoercivity.D S).eval (m : ℂ)) := by
    apply (eq_div_iff (mul_ne_zero hpi hDne)).mpr
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hmodel
  have hnorm :
      ‖(ActualNodalCoercivity.P c S v).eval (m : ℂ) -
        (arithmeticBoundarySymbol c m : ℂ) * (ActualNodalCoercivity.Q S v).eval (m : ℂ)‖ ^ 2 =
      Real.pi ^ 2 * ‖(ActualNodalCoercivity.D S).eval (m : ℂ)‖ ^ 2 *
        ‖couplingColumn c S v m‖ ^ 2 := by
    have hclear := (eq_div_iff (mul_ne_zero hpi hDne)).mp hquot
    have hh := congrArg (fun z : ℂ => ‖z‖ ^ 2) hclear
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos] at hh
    nlinarith only [hh]
  rw [hnorm]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hp : ((3 * (N : ℝ)) ^ S.card) ^ 2 = (3 * (N : ℝ)) ^ (2 * S.card) := by
    rw [← pow_mul, Nat.mul_comm S.card 2]
  rw [hp] at hs
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (sq_nonneg Real.pi)) (sq_nonneg _)

/-- Every nonempty finite integer head has a coefficient-uniform positive
lower bound for the genuine paired exterior tail of the full actual column.
The positive constant and cutoff are chosen before both the head coefficients
and the tail index. -/
theorem actual_finite_head_uniform_tail_lower {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ v : ℤ → ℂ, ∀ N : ℕ, N0 ≤ N →
      Summable (fun j : ℕ =>
        ‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) ∧
      C * (∑ n ∈ S, ‖v n‖ ^ 2) / ((N : ℝ) + 1) ^ (2 * S.card - 1) ≤
        ∑' j : ℕ,
          (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
            ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) := by
  classical
  let d := S.card
  let A := max 1 (S.sup Int.natAbs)
  have hd : 0 < d := hS.card_pos
  have hA : 1 ≤ A := le_max_left _ _
  have hbound : ∀ n ∈ S, n.natAbs ≤ A := by
    intro n hn
    exact (Finset.le_sup hn).trans (le_max_right _ _)
  have hboundR : ∀ n ∈ S, |(n : ℝ)| ≤ (A : ℝ) := by
    intro n hn
    have heq : |(n : ℝ)| = (n.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    rw [heq]
    exact_mod_cast hbound n hn
  obtain ⟨κ, hκ, hsampling⟩ :=
    D5.S3.Analytic.Interpolation.DiscreteCoefficientSampling.discrete_coefficient_sampling_lower d hd
  obtain ⟨K, hK, hKasymp⟩ := smooth_weight_actual_asymptotic c hc
  have hδ : ∀ m : ℕ, 0 < m → |remainder c m| ≤ K / (m : ℝ) := by
    intro m hm
    simpa only [remainder, gamma] using hKasymp m hm
  let rho : ℝ := 1 / ((d : ℝ) ^ 2 * (A : ℝ) ^ (2 * (d - 1)))
  let R : ℝ := ∑ r ∈ Finset.range d, (4 : ℝ) ^ r
  let T : ℝ := R * (4 * ActualFullSymbolTail.primeFirstMoment c +
    2 * K)
  have hrho : 0 < rho := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hAR : 0 < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
    dsimp [rho]
    positivity
  have hkg : 0 < κ * gamma ^ 2 := mul_pos hκ (sq_pos_of_pos gamma_bounds.1)
  obtain ⟨L, hL⟩ := exists_nat_ge (2 * T / (κ * gamma ^ 2))
  let N0 : ℕ := max 1 (max (2 * A) (max (2 * d) L))
  let C₀ : ℝ := κ * gamma ^ 2 * rho / (Real.pi ^ 2 * (3 : ℝ) ^ (2 * d))
  have hC₀ : 0 < C₀ :=
    div_pos (mul_pos hkg hrho) (mul_pos (sq_pos_of_pos Real.pi_pos) (by positivity))
  refine ⟨C₀, hC₀, N0, ?_⟩
  intro v N hN0
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN0
  have hNA : 2 * A ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN0
  have hNd : 2 * d ≤ N := by
    exact (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)).trans hN0
  have hNL : L ≤ N := by
    exact (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)).trans hN0
  have hN : 0 < N := by omega
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hAN : A ≤ N := by omega
  have hsep : (A : ℝ) < (N : ℝ) + 1 := by
    have hh : (A : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAN
    linarith
  have hsum := (ActualFullSymbolTail.paired_coupling_column_tail hc hN S v
    (Nat.cast_nonneg A) hboundR hsep).1
  refine ⟨hsum, ?_⟩
  let p := ActualNodalCoercivity.P c S v
  let q := ActualNodalCoercivity.Q S v
  let E := totalEnergy d N p q
  have hE : 0 ≤ E := totalEnergy_nonneg d N p q
  obtain ⟨hp, hq, _⟩ := ActualNodalCoercivity.actual_nodal_polynomial_model c S hS v
  have hchannels := two_channel_annulus hc d N hd hN hNd κ K hκ hK.le hδ
    hsampling p q
  have hthreshold : 2 * T ≤ κ * gamma ^ 2 * (N : ℝ) := by
    have hLN : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNL
    have hh := (div_le_iff₀ hkg).mp (hL.trans hLN)
    nlinarith only [hh]
  have hpaired :
      (∑ m ∈ Finset.Icc (N + 1) (2 * N),
        (‖p.eval (m : ℂ) - (arithmeticBoundarySymbol c (m : ℤ) : ℂ) * q.eval (m : ℂ)‖ ^ 2 +
         ‖p.eval (-(m : ℂ)) - (arithmeticBoundarySymbol c (-(m : ℤ)) : ℂ) *
           q.eval (-(m : ℂ))‖ ^ 2)) =
      2 * ∑ m ∈ Finset.Icc (N + 1) (2 * N),
        (‖(F₁ d N p q).eval ((m : ℂ) / (N : ℂ)) +
          ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
            (B₁ d N q).eval ((m : ℂ) / (N : ℂ))‖ ^ 2 +
         ‖(F₂ d N p q).eval ((m : ℂ) / (N : ℂ)) +
          ((primeSymbol c (m : ℤ) + remainder c m : ℝ) : ℂ) *
            (B₂ d N q).eval ((m : ℂ) / (N : ℂ))‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmpos : 0 < m := by have hh := (Finset.mem_Icc.mp hm).1; omega
    exact (exact_channels c d N hd hN p q hp hq m hmpos).2.2
  have hnum : κ * gamma ^ 2 * (N : ℝ) * E ≤
      ∑ m ∈ Finset.Icc (N + 1) (2 * N),
        (‖p.eval (m : ℂ) - (arithmeticBoundarySymbol c (m : ℤ) : ℂ) * q.eval (m : ℂ)‖ ^ 2 +
         ‖p.eval (-(m : ℂ)) - (arithmeticBoundarySymbol c (-(m : ℤ)) : ℂ) *
           q.eval (-(m : ℂ))‖ ^ 2) := by
    rw [hpaired]
    change (κ * gamma ^ 2 * (N : ℝ) - T) * E ≤ _ at hchannels
    have ht := mul_nonneg (sub_nonneg.mpr hthreshold) hE
    nlinarith only [hchannels, ht]
  have hden : (∑ m ∈ Finset.Icc (N + 1) (2 * N),
        (‖p.eval (m : ℂ) - (arithmeticBoundarySymbol c (m : ℤ) : ℂ) * q.eval (m : ℂ)‖ ^ 2 +
         ‖p.eval (-(m : ℂ)) - (arithmeticBoundarySymbol c (-(m : ℤ)) : ℂ) *
           q.eval (-(m : ℂ))‖ ^ 2)) ≤
      Real.pi ^ 2 * (3 * (N : ℝ)) ^ (2 * d) *
        ∑ m ∈ Finset.Icc (N + 1) (2 * N),
          (‖couplingColumn c S v (m : ℤ)‖ ^ 2 +
           ‖couplingColumn c S v (-(m : ℤ))‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    have hml : (N : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : N < m)
    have hmh : (m : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hmhi
    have h_pos := actual_numerator_bound c S hS A N hbound hAN v (m : ℤ)
      (by simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))] using hml)
      (by simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))] using hmh)
    have h_neg := actual_numerator_bound c S hS A N hbound hAN v (-(m : ℤ))
      (by simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))] using hml)
      (by simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))] using hmh)
    simpa only [p, q, d, Int.cast_natCast, Int.cast_neg, mul_add] using add_le_add h_pos h_neg
  let U : ℝ := ∑ m ∈ Finset.Icc (N + 1) (2 * N),
    (‖couplingColumn c S v (m : ℤ)‖ ^ 2 + ‖couplingColumn c S v (-(m : ℤ))‖ ^ 2)
  have hmain : κ * gamma ^ 2 * (N : ℝ) * E ≤
      Real.pi ^ 2 * (3 * (N : ℝ)) ^ (2 * d) * U := hnum.trans hden
  have hpower : (N : ℝ) ^ (2 * d) = (N : ℝ) * (N : ℝ) ^ (2 * d - 1) := by
    have he : 2 * d = (2 * d - 1) + 1 := by omega
    calc
      (N : ℝ) ^ (2 * d) = (N : ℝ) ^ ((2 * d - 1) + 1) :=
        congrArg (fun k : ℕ => (N : ℝ) ^ k) he
      _ = _ := by rw [pow_succ]; ring
  have hcancel : κ * gamma ^ 2 * E ≤
      (Real.pi ^ 2 * (3 : ℝ) ^ (2 * d) * (N : ℝ) ^ (2 * d - 1)) * U := by
    rw [mul_pow, hpower] at hmain
    apply (mul_le_mul_iff_right₀ hNR).mp
    nlinarith only [hmain]
  have hrec : rho * (∑ n ∈ S, ‖v n‖ ^ 2) ≤ E :=
    ActualNodalCoercivity.uniform_coefficient_reconstruction S A hS hA hbound c v N hN
  have hrec' := mul_le_mul_of_nonneg_left hrec hkg.le
  have hpositive : 0 < Real.pi ^ 2 * (3 : ℝ) ^ (2 * d) *
      (N : ℝ) ^ (2 * d - 1) := by positivity
  have hfinite : C₀ * (∑ n ∈ S, ‖v n‖ ^ 2) / (N : ℝ) ^ (2 * d - 1) ≤ U := by
    have hh := (div_le_iff₀' hpositive).mpr (hrec'.trans hcancel)
    convert hh using 1 <;> dsimp [C₀] <;>
      field_simp [hNR.ne', Real.pi_ne_zero] <;> ring
  have hV : 0 ≤ ∑ n ∈ S, ‖v n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmono : C₀ * (∑ n ∈ S, ‖v n‖ ^ 2) / ((N : ℝ) + 1) ^ (2 * d - 1) ≤
      C₀ * (∑ n ∈ S, ‖v n‖ ^ 2) / (N : ℝ) ^ (2 * d - 1) := by
    apply div_le_div_of_nonneg_left (mul_nonneg hC₀.le hV) (pow_pos hNR _)
    exact pow_le_pow_left₀ hNR.le (by linarith) _
  have htail : U ≤ ∑' j : ℕ,
      (‖couplingColumn c S v ((N + j + 1 : ℕ) : ℤ)‖ ^ 2 +
        ‖couplingColumn c S v (-((N + j + 1 : ℕ) : ℤ))‖ ^ 2) := by
    dsimp only [U]
    rw [annulus_reindex]
    exact Summable.sum_le_tsum (Finset.range N)
      (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) hsum
  exact hmono.trans (hfinite.trans htail)

end D5.S3.Weil.ZetaBridge.ActualUniformFiniteHeadTail

