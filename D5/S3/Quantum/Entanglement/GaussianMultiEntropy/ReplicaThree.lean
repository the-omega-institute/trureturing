/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact integral-defined Gaussian genuine multi-entropy at replica order three. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ResidualLimit
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
import Mathlib.Tactic.FinCases

/-!
The order-three Fourier spectrum has one zero weight, two occurrences of each
of the three labelled cut weights, and two occurrences of the full pair sum.
The actual integral bridge is the existing `ResidualLimit.GM3_eq_fourierGM`;
the all-replica integral/Fourier result is prior work, not a new replica-three
theorem. Its Gaussian integration supplier retains Mario Brcic's Apache-2.0
transplant credit (upstream 254b6275b753efb609cd38ef4c85eef29b4a13b4).

The finite order-three formula and balancing package are from the released
2026-11-04 note by Haobo Ma and Wenlin Zhang (CC BY 4.0), for the fully
symmetric pure Gaussian family of Camargo and Nishida. This module concerns
positive integer physical mode counts, the real `eMinus` branch and `a ≥ 1`.
Real party sizes in the scalar supplier do not assert fractional physical modes.
Higher replicas, other branches, replica-one continuation and large-N/Page
claims are separate questions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree

open GaussianMultiEntropyAsymptotic GaussianMultiEntropy.ResidualLimit
open ReplicaThreeScalar

/-- The order-three parameter is three quarters of the library's squeezing. -/
def kappa (N a : ℝ) : ℝ := 3 * (a ^ 2 - 1) / (4 * (N - 1))

private lemma kappa_eq (N a : ℝ) : kappa N a = 3 * squeezing N a / 4 := by
  by_cases h : N - 1 = 0
  · simp [kappa, squeezing, h]
  · unfold kappa squeezing
    field_simp

private lemma sin_two_thirds : Real.sin (Real.pi * 2 / 3) ^ 2 = 3 / 4 := by
  rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
  exact Real.sq_sin_pi_div_three

private lemma sin_neg_third : Real.sin (Real.pi * (-1) / 3) ^ 2 = 3 / 4 := by
  rw [show Real.pi * (-1) / 3 = -(Real.pi / 3) by ring, Real.sin_neg, neg_sq]
  exact Real.sq_sin_pi_div_three

private lemma sin_neg_two_thirds : Real.sin (Real.pi * (-2) / 3) ^ 2 = 3 / 4 := by
  rw [show Real.pi * (-2) / 3 = -(Real.pi * 2 / 3) by ring, Real.sin_neg, neg_sq]
  exact sin_two_thirds

private lemma weight_table (A B C : ℝ) :
    tripartiteWeight 3 A B C 0 0 = 0 ∧
    tripartiteWeight 3 A B C 1 0 = 3 * A * (B + C) / 4 ∧
    tripartiteWeight 3 A B C 2 0 = 3 * A * (B + C) / 4 ∧
    tripartiteWeight 3 A B C 0 1 = 3 * B * (A + C) / 4 ∧
    tripartiteWeight 3 A B C 0 2 = 3 * B * (A + C) / 4 ∧
    tripartiteWeight 3 A B C 1 1 = 3 * C * (A + B) / 4 ∧
    tripartiteWeight 3 A B C 2 2 = 3 * C * (A + B) / 4 ∧
    tripartiteWeight 3 A B C 1 2 = 3 * pairSum A B C / 4 ∧
    tripartiteWeight 3 A B C 2 1 = 3 * pairSum A B C / 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num only [tripartiteWeight, pairSum, Nat.cast_ofNat,
      sub_self, sub_zero, zero_sub, mul_zero, mul_one, zero_div, Real.sin_zero, zero_pow,
      Real.sq_sin_pi_div_three,
      sin_two_thirds, sin_neg_third, sin_neg_two_thirds] <;> ring

private lemma cutProduct_three (u t : ℝ) :
    cutProduct 3 u t = (1 + 3 * t * u / 4) ^ 2 := by
  rw [cutProduct, Fin.prod_univ_three]
  simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl,
    show ((1 : Fin 3) : ℕ) = 1 from rfl, show ((2 : Fin 3) : ℕ) = 2 from rfl]
  norm_num only [cutWeight, Nat.cast_ofNat, mul_zero, mul_one, zero_div,
    Real.sin_zero, zero_pow, Real.sq_sin_pi_div_three, sin_two_thirds]
  ring

private lemma tripartiteProduct_three (A B C t : ℝ) :
    tripartiteProduct 3 A B C t =
      cut (3 * t / 4) A B C ^ 2 * cut (3 * t / 4) B A C ^ 2 *
        cut (3 * t / 4) C A B ^ 2 * (1 + (3 * t / 4) * pairSum A B C) ^ 2 := by
  obtain ⟨w00, w10, w20, w01, w02, w11, w22, w12, w21⟩ := weight_table A B C
  rw [tripartiteProduct, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_three, show ((0 : Fin 3) : ℕ) = 0 from rfl,
    show ((1 : Fin 3) : ℕ) = 1 from rfl, show ((2 : Fin 3) : ℕ) = 2 from rfl,
    w00, w10, w20, w01, w02, w11, w22, w12, w21, mul_zero, add_zero, one_mul]
  unfold cut
  ring

private lemma fourierGM_three_value (A B C a : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hN : 1 < A + B + C) (ha : 1 ≤ a) :
    fourierGM 3 A B C a = value (kappa (A + B + C) a) A B C := by
  set t := squeezing (A + B + C) a with ht
  have ht0 : 0 ≤ t := div_nonneg (by nlinarith) (by linarith)
  have hA0 : 0 < cut (3 * t / 4) A B C := by unfold cut; positivity
  have hB0 : 0 < cut (3 * t / 4) B A C := by unfold cut; positivity
  have hC0 : 0 < cut (3 * t / 4) C A B := by unfold cut; positivity
  have hS0 : 0 < 1 + (3 * t / 4) * pairSum A B C := by unfold pairSum; positivity
  have hAB := mul_ne_zero (pow_ne_zero 2 hA0.ne') (pow_ne_zero 2 hB0.ne')
  have hABC := mul_ne_zero hAB (pow_ne_zero 2 hC0.ne')
  have hcut (u v w : ℝ) : 1 + 3 * t * (u * (v + w)) / 4 = cut (3 * t / 4) u v w := by
    unfold cut
    ring
  rw [fourierGM, ← ht, tripartiteProduct_three, cutProduct_three, cutProduct_three,
    cutProduct_three, hcut, hcut, hcut,
    Real.log_mul hABC (pow_ne_zero 2 hS0.ne'),
    Real.log_mul hAB (pow_ne_zero 2 hC0.ne'),
    Real.log_mul (pow_ne_zero 2 hA0.ne') (pow_ne_zero 2 hB0.ne')]
  simp only [Real.log_pow, value, kappa_eq, ← ht]
  norm_num
  ring

/-- The actual real integral-defined Gaussian value, for every positive integer
tripartition, including vacuum. All three labelled cuts occur with multiplicity. -/
theorem GM3_three_closed (A B C : ℕ) (a : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (ha : 1 ≤ a) :
    GM3 3 A B C a =
      Real.log ((1 + kappa (A + B + C) a * pairSum A B C) ^ 2 /
        (cut (kappa (A + B + C) a) A B C *
          cut (kappa (A + B + C) a) B A C *
          cut (kappa (A + B + C) a) C A B)) / 12 := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hN : (1 : ℝ) < (A : ℝ) + B + C := by
    have h : (3 : ℝ) ≤ (A : ℝ) + B + C := by exact_mod_cast (show 3 ≤ A + B + C by omega)
    linarith
  rw [GM3_eq_fourierGM 3 A B C (by norm_num) a ha hA hB hC,
    fourierGM_three_value A B C a hAr.le hBr.le hCr.le hN ha,
    value_eq_log_ratio]
  · unfold kappa
    exact div_nonneg (by nlinarith) (by linarith)
  all_goals positivity

/-- Vacuum, strict squeezing decrease and strict negativity for the actual
integral-defined family. In particular all positive integer triples tie at vacuum. -/
theorem GM3_three_behavior (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    GM3 3 A B C 1 = 0 ∧
      StrictAntiOn (fun a => GM3 3 A B C a) (Set.Ici 1) ∧
        ∀ a : ℝ, 1 < a → GM3 3 A B C a < 0 := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hN : (1 : ℝ) < (A : ℝ) + B + C := by
    exact_mod_cast (show 1 < A + B + C by omega)
  have hk (a : ℝ) (ha : 1 ≤ a) : 0 ≤ kappa ((A : ℝ) + B + C) a := by
    unfold kappa
    exact div_nonneg (by nlinarith) (by linarith)
  have hrepr (a : ℝ) (ha : 1 ≤ a) :
      GM3 3 A B C a = value (kappa ((A : ℝ) + B + C) a) A B C := by
    rw [GM3_three_closed A B C a hA hB hC ha]
    exact (value_eq_log_ratio _ _ _ _ (hk a ha) hAr.le hBr.le hCr.le).symm
  obtain ⟨hzero, hanti⟩ := parameter_behavior A B C hAr hBr hCr
  refine ⟨?_, ?_, ?_⟩
  · rw [hrepr 1 (by norm_num)]
    simpa [kappa] using hzero
  · intro a ha b hb hab
    have hkab : kappa ((A : ℝ) + B + C) a < kappa ((A : ℝ) + B + C) b := by
      unfold kappa
      apply (div_lt_div_iff_of_pos_right (by linarith : 0 < 4 * ((A : ℝ) + B + C - 1))).2
      have ha' : 1 ≤ a := ha
      nlinarith
    dsimp only
    rw [hrepr a ha, hrepr b hb]
    exact hanti (hk a ha) (hk b hb) hkab
  · intro a ha
    rw [hrepr a ha.le]
    apply value_neg _ _ _ _ _ hAr hBr hCr
    unfold kappa
    exact div_pos (by nlinarith) (by linarith)

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
