/- GID: D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/OrthocrossPairingPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian polynomials for inverse-frame pairings of orthocross vectors. -/

import D5.S3.Quantum.Measurement.OrthocrossInverseFrame
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.OrthocrossPairingPolynomial

open Matrix Complex Polynomial
open scoped ComplexOrder
open D5.S3.Quantum.Measurement.OrthocrossGramHalfInteger
open D5.S3.Quantum.Measurement.OrthocrossInverseFrame

private def gaussianI : GaussianInt := ⟨0, 1⟩

private noncomputable def entryPolynomial {d : ℕ} (j k : Fin d) : Polynomial GaussianInt :=
  if j = k then X ^ (d - 1) - C gaussianI else
    if j < k then (1 - X) * X ^ (d + j.val - k.val - 1) else
      C gaussianI * (1 - X) * X ^ (j.val - k.val - 1)

/-- The Gaussian polynomial obtained by expanding the two orthocross supports. -/
noncomputable def pairingPolynomial {d : ℕ} : Idx d → Idx d → Polynomial GaussianInt
  | .inl j, .inl k => entryPolynomial j k
  | .inl j, .inr (.inl p) => entryPolynomial j p.1.1 + entryPolynomial j p.1.2
  | .inl j, .inr (.inr p) => entryPolynomial j p.1.1 + C gaussianI * entryPolynomial j p.1.2
  | .inr (.inl p), .inl k => entryPolynomial p.1.1 k + entryPolynomial p.1.2 k
  | .inr (.inr p), .inl k => entryPolynomial p.1.1 k - C gaussianI * entryPolynomial p.1.2 k
  | .inr (.inl p), .inr (.inl r) =>
      entryPolynomial p.1.1 r.1.1 + entryPolynomial p.1.1 r.1.2 +
        entryPolynomial p.1.2 r.1.1 + entryPolynomial p.1.2 r.1.2
  | .inr (.inl p), .inr (.inr r) =>
      entryPolynomial p.1.1 r.1.1 + C gaussianI * entryPolynomial p.1.1 r.1.2 +
        entryPolynomial p.1.2 r.1.1 + C gaussianI * entryPolynomial p.1.2 r.1.2
  | .inr (.inr p), .inr (.inl r) =>
      entryPolynomial p.1.1 r.1.1 + entryPolynomial p.1.1 r.1.2 -
        C gaussianI * entryPolynomial p.1.2 r.1.1 - C gaussianI * entryPolynomial p.1.2 r.1.2
  | .inr (.inr p), .inr (.inr r) =>
      entryPolynomial p.1.1 r.1.1 + C gaussianI * entryPolynomial p.1.1 r.1.2 -
        C gaussianI * entryPolynomial p.1.2 r.1.1 + entryPolynomial p.1.2 r.1.2

private theorem entry_eval_one {d : ℕ} (j k : Fin d) :
    (entryPolynomial j k).eval 1 = if j = k then 1 - gaussianI else 0 := by
  dsimp only [entryPolynomial]
  split_ifs <;> simp

private theorem entry_derivative_eval_one {d : ℕ} (j k : Fin d) :
    (entryPolynomial j k).derivative.eval 1 =
      if j = k then ((d - 1 : ℕ) : GaussianInt) else if j < k then -1 else -gaussianI := by
  dsimp only [entryPolynomial]
  split_ifs <;> simp [derivative_mul, derivative_pow]

set_option maxHeartbeats 1000000 in
-- The support-order and phase cases require a larger elaboration budget.
/-- Every pairing polynomial is nonzero, including pairs with intersecting supports. -/
theorem pairingPolynomial_ne_zero {d : ℕ} (α β : Idx d) : pairingPolynomial α β ≠ 0 := by
  intro hz
  have hv := congrArg (fun p : Polynomial GaussianInt => p.eval 1) hz
  have hw := congrArg (fun p : Polynomial GaussianInt => p.derivative.eval 1) hz
  rcases α with j | ⟨⟨j, k⟩, hjk⟩ | ⟨⟨j, k⟩, hjk⟩ <;>
    rcases β with p | ⟨⟨p, r⟩, hpr⟩ | ⟨⟨p, r⟩, hpr⟩
  all_goals try simp only [Fin.lt_def] at hjk
  all_goals try simp only [Fin.lt_def] at hpr
  all_goals
    dsimp only [pairingPolynomial] at hv hw
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_zero,
      derivative_add, derivative_sub, derivative_C_mul, derivative_zero,
      entry_eval_one, entry_derivative_eval_one] at hv hw <;>
      (try split_ifs at hv) <;> (try split_ifs at hw) <;> try omega
  all_goals
    have hv' := congrArg GaussianInt.toComplex hv
    have hw' := congrArg GaussianInt.toComplex hw
    norm_num [GaussianInt.toComplex_def, gaussianI, Complex.ext_iff] at hv' <;>
      norm_num [GaussianInt.toComplex_def, gaussianI, Complex.ext_iff] at hw'

private theorem gaussianI_toComplex : (gaussianI : ℂ) = I := by
  simp [gaussianI, GaussianInt.toComplex_def]

private theorem entry_coeff_norm {d : ℕ} (hd : 2 ≤ d) (j k : Fin d) (n : ℕ) :
    ‖((entryPolynomial j k).coeff n : ℂ)‖ ≤ 1 := by
  have hm (e : ℕ) : (1 - X : Polynomial GaussianInt) * X ^ e = X ^ e - X ^ (e + 1) := by
    rw [sub_mul, one_mul, pow_succ']
  have hc (e : ℕ) : ‖(((X ^ e - X ^ (e + 1) : Polynomial GaussianInt).coeff n) : ℂ)‖ ≤ 1 := by
    simp only [coeff_sub, coeff_X_pow]
    split_ifs <;> norm_num [GaussianInt.toComplex_def] <;> omega
  dsimp only [entryPolynomial]
  split_ifs
  · simp only [coeff_sub, coeff_X_pow, coeff_C]
    split_ifs <;> norm_num [GaussianInt.toComplex_def, gaussianI] <;> omega
  · rw [hm]
    exact hc _
  · rw [mul_assoc, hm, coeff_C_mul, GaussianInt.toComplex_mul, gaussianI_toComplex, norm_mul, norm_I, one_mul]
    exact hc _

private theorem pairing_coeff_complex_norm {d : ℕ} (hd : 2 ≤ d) (α β : Idx d) (n : ℕ) :
    ‖((pairingPolynomial α β).coeff n : ℂ)‖ ≤ 4 := by
  have hc (j k : Fin d) := entry_coeff_norm hd j k n
  have hi (j k : Fin d) : ‖I * ((entryPolynomial j k).coeff n : ℂ)‖ ≤ 1 := by
    simpa only [norm_mul, norm_I, one_mul] using hc j k
  have hni (j k : Fin d) : ‖-(I * ((entryPolynomial j k).coeff n : ℂ))‖ ≤ 1 := by
    simpa only [norm_neg] using hi j k
  have h2 {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 4 :=
    (norm_add_le_of_le ha hb).trans (by norm_num)
  have h4 {a b c e : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
      (hc : ‖c‖ ≤ 1) (he : ‖e‖ ≤ 1) : ‖a + b + c + e‖ ≤ 4 := by
    convert norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le ha hb) hc) he using 1 <;> norm_num
  rcases α with j | p | p <;> rcases β with k | r | r
  all_goals dsimp only [pairingPolynomial]
  all_goals simp (config := { failIfUnchanged := false }) only
    [coeff_add, coeff_sub, coeff_neg, coeff_C_mul,
    GaussianInt.toComplex_neg, GaussianInt.toComplex_add, GaussianInt.toComplex_sub, GaussianInt.toComplex_mul,
    gaussianI_toComplex, sub_eq_add_neg]
  · exact (hc j k).trans (by norm_num)
  · exact h2 (hc _ _) (hc _ _)
  · exact h2 (hc _ _) (hi _ _)
  · exact h2 (hc _ _) (hc _ _)
  · exact h4 (hc _ _) (hc _ _) (hc _ _) (hc _ _)
  · exact h4 (hc _ _) (hi _ _) (hc _ _) (hi _ _)
  · exact h2 (hc _ _) (hni _ _)
  · exact h4 (hc _ _) (hc _ _) (hni _ _) (hni _ _)
  · exact h4 (hc _ _) (hi _ _) (hni _ _) (hc _ _)

/-- Every Gaussian coefficient has squared modulus at most sixteen. -/
theorem pairingPolynomial_coeff_bound {d : ℕ} (hd : 2 ≤ d) (α β : Idx d) (n : ℕ) :
    ((pairingPolynomial α β).coeff n).norm ≤ 16 := by
  have hc := pairing_coeff_complex_norm hd α β n
  have he : (((pairingPolynomial α β).coeff n).norm : ℝ) =
      ‖((pairingPolynomial α β).coeff n : ℂ)‖ ^ 2 := by
    rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]
  have hb : (((pairingPolynomial α β).coeff n).norm : ℝ) ≤ 16 := by
    rw [he]
    nlinarith [norm_nonneg (((pairingPolynomial α β).coeff n : ℂ))]
  exact_mod_cast hb

/-- In dimension at least four, the pairing polynomials do not vanish at q. -/
theorem pairingPolynomial_at_ratio_ne_zero {d : ℕ} (hd : 4 ≤ d) (α β : Idx d) :
    (pairingPolynomial α β).eval₂ GaussianInt.toComplex (ratio d) ≠ 0 := by
  apply polynomial_at_ratio_ne_zero d _ (pairingPolynomial_ne_zero α β)
  intro n
  have hb := pairingPolynomial_coeff_bound (by omega : 2 ≤ d) α β n
  have hd' : (4 : ℤ) ≤ d := by exact_mod_cast hd
  nlinarith

private theorem entry_eval_ratio {d : ℕ} (hd : 2 ≤ d) (j k : Fin d) :
    (entryPolynomial j k).eval₂ GaussianInt.toComplex (ratio d) =
      ((1 - ratio d) * ratio d ^ ((d : ℤ) - 2) / upperConstant d) * candidate d j k := by
  have hq := ratio_ne_zero d
  have hu := upperConstant_ne_zero (show 0 < d by omega)
  have h1 : 1 - ratio d ≠ 0 := sub_ne_zero.mpr (Ne.symm (ratio_ne_one d))
  have hpow (a b : ℤ) : ratio d ^ a * ratio d ^ b = ratio d ^ (a + b) :=
    (zpow_add₀ hq a b).symm
  dsimp only [entryPolynomial, candidate, Matrix.of_apply]
  split_ifs with heq hlt
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, gaussianI_toComplex]
    have he : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    rw [← zpow_natCast, he]
    rw [show ((1 - ratio d) * ratio d ^ ((d : ℤ) - 2) / upperConstant d) *
        diagonalConstant d = (1 - ratio d) * ratio d ^ ((d : ℤ) - 2) *
          (diagonalConstant d / upperConstant d) by ring,
      diagonal_div_upperConstant (show 0 < d by omega)]
    have he' : (1 - ratio d) * ratio d ^ ((d : ℤ) - 2) *
        ((ratio d - I * ratio d ^ ((2 : ℤ) - (d : ℤ))) / (1 - ratio d)) =
        ratio d ^ ((d : ℤ) - 2) *
          (ratio d - I * ratio d ^ ((2 : ℤ) - (d : ℤ))) := by field_simp
    rw [he', mul_sub, mul_left_comm _ I, hpow]
    have hz : (d : ℤ) - 2 + (2 - (d : ℤ)) = 0 := by ring
    rw [hz, zpow_zero, mul_one]
    have hn : ratio d ^ ((d : ℤ) - 2) * ratio d = ratio d ^ ((d : ℤ) - 1) := by
      calc
        _ = ratio d ^ ((d : ℤ) - 2) * ratio d ^ (1 : ℤ) := by rw [zpow_one]
        _ = ratio d ^ (((d : ℤ) - 2) + 1) := hpow _ _
        _ = _ := by congr 1; ring
    rw [hn]
  · simp only [eval₂_mul, eval₂_sub, eval₂_one, eval₂_X, eval₂_pow]
    have he : ((d + j.val - k.val - 1 : ℕ) : ℤ) =
        ((d : ℤ) - 2) + ((j.val : ℤ) - (k.val : ℤ) + 1) := by omega
    rw [← zpow_natCast, he]
    rw [zpow_add₀ hq]
    field_simp
    <;> ring
  · simp only [eval₂_mul, eval₂_sub, eval₂_one, eval₂_X, eval₂_pow, eval₂_C,
      gaussianI_toComplex, star_mul, star_zpow₀, star_ratio,
      _root_.inv_zpow, ← _root_.zpow_neg, upperConstant_phase]
    have he : ((j.val - k.val - 1 : ℕ) : ℤ) = (j.val : ℤ) - (k.val : ℤ) - 1 := by
      have hne : j.val ≠ k.val := fun h => heq (Fin.ext h)
      have hnot : ¬j.val < k.val := hlt
      omega
    rw [← zpow_natCast, he]
    have he' : ((d : ℤ) - 2) + ((2 : ℤ) - d) = 0 := by ring
    have hp : ratio d ^ ((d : ℤ) - 2) * ratio d ^ ((2 : ℤ) - d) = 1 := by
      rw [hpow, he', zpow_zero]
    have hn : -((k.val : ℤ) - (j.val : ℤ) + 1) =
        (j.val : ℤ) - (k.val : ℤ) - 1 := by ring
    rw [hn]
    field_simp
    exact hp.symm

/-- Evaluation at q is a nonzero scalar times the inverse-candidate pairing. -/
theorem pairingPolynomial_eval_ratio {d : ℕ} (hd : 2 ≤ d) (α β : Idx d) :
    (pairingPolynomial α β).eval₂ GaussianInt.toComplex (ratio d) =
      ((1 - ratio d) * ratio d ^ ((d : ℤ) - 2) / upperConstant d) *
        (star (vec α) ⬝ᵥ (candidate d *ᵥ vec β)) := by
  rcases α with j | p | p <;> rcases β with k | r | r
  all_goals
    dsimp only [pairingPolynomial]
    simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
      gaussianI_toComplex, entry_eval_ratio hd, OrthocrossGramHalfInteger.vec, star_add, Pi.star_single,
      star_one, Complex.star_def, Complex.conj_I, Matrix.mulVec_add, Matrix.mulVec_single,
      add_dotProduct, dotProduct_add, single_dotProduct, Pi.add_apply, Pi.smul_apply,
      op_smul_eq_smul, smul_eq_mul, Matrix.col_apply, one_mul, mul_one] <;>
      ring_nf <;> simp only [I_sq] <;> ring

/-- The pairing polynomial does not vanish at q in any dimension at least two. -/
theorem pairingPolynomial_eval_ne_zero {d : ℕ} (hd : 2 ≤ d) (α β : Idx d) :
    (pairingPolynomial α β).eval₂ GaussianInt.toComplex (ratio d) ≠ 0 := by
  by_cases hlarge : 4 ≤ d
  · exact pairingPolynomial_at_ratio_ne_zero hlarge α β
  · interval_cases d
    · have hq : ratio 2 = (4 / 5 : ℂ) - (3 / 5 : ℂ) * I := by
        apply Complex.ext <;> norm_num [ratio, scale, upperEntry, lowerEntry,
          Complex.div_re, Complex.div_im, Complex.normSq_apply]
      rw [hq]
      fin_cases α <;> fin_cases β <;>
        dsimp only [pairingPolynomial] <;>
        norm_num [entryPolynomial, gaussianI, GaussianInt.toComplex_def,
          Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    · have hq : ratio 3 = (12 / 13 : ℂ) - (5 / 13 : ℂ) * I := by
        apply Complex.ext <;> norm_num [ratio, scale, upperEntry, lowerEntry,
          Complex.div_re, Complex.div_im, Complex.normSq_apply]
      have he (j k : Fin 3) :
          (entryPolynomial j k).eval₂ GaussianInt.toComplex (ratio 3) =
            (if j = k then (119 : ℂ) - 289 * I else
              if j < k then
                if k.val - j.val = 1 then 37 + 55 * I else 13 + 65 * I
              else if j.val - k.val = 1 then -65 + 13 * I else -55 + 37 * I) / 169 := by
        fin_cases j <;> fin_cases k <;>
          norm_num [entryPolynomial, hq, gaussianI, GaussianInt.toComplex_def, pow_two, Fin.lt_def,
            Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
      fin_cases α <;> fin_cases β <;>
        dsimp only [pairingPolynomial] <;>
        norm_num [eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
          gaussianI_toComplex, he, Fin.lt_def, Complex.ext_iff, Complex.div_re,
          Complex.div_im, Complex.normSq_apply]

/-- Every pairing of orthocross vectors through the inverse frame is nonzero. -/
theorem inverse_frame_pairing_ne_zero {d : ℕ} (α β : Idx d) :
    star (vec α) ⬝ᵥ ((frame (1 : Matrix (Fin d) (Fin d) ℂ))⁻¹ *ᵥ vec β) ≠ 0 := by
  by_cases hd : 2 ≤ d
  · rw [inverse_frame_eq (show 0 < d by omega)]
    intro hz
    have he := pairingPolynomial_eval_ratio hd α β
    rw [hz, mul_zero] at he
    exact pairingPolynomial_eval_ne_zero hd α β he
  · interval_cases d
    · rcases α with j | p | p
      · exact Fin.elim0 j
      · exact Fin.elim0 p.1.1
      · exact Fin.elim0 p.1.1
    · fin_cases α <;> fin_cases β
      rw [inverse_frame_eq (by decide : 0 < 1)]
      simpa [OrthocrossGramHalfInteger.vec, candidate, Pi.star_single,
        Matrix.mulVec_single, single_dotProduct, Matrix.col_apply] using
        ne_of_gt (diagonalConstant_pos (by decide : 0 < 1))

#print axioms pairingPolynomial_eval_ne_zero
#print axioms inverse_frame_pairing_ne_zero

#print axioms pairingPolynomial_eval_ratio

#print axioms pairingPolynomial_ne_zero
#print axioms pairingPolynomial_coeff_bound
#print axioms pairingPolynomial_at_ratio_ne_zero

end D5.S3.Quantum.Measurement.OrthocrossPairingPolynomial
