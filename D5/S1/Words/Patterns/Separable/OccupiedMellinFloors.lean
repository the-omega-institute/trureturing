/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinFloors
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinFloors
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Floor.Semiring]
   utility: none
   digest: Integer floor cutoffs give a uniform algebraic Mellin mesh rate. -/

import D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh
import Mathlib.Algebra.Order.Floor.Semiring

/-! Natural floor rounding at the two scales yields an explicit error bound
for the same shifted positive mesh and the unshifted half-line integral. -/

open Set MeasureTheory
namespace D5.S1.Words.Patterns.Separable.OccupiedMellinFloors

open OccupiedMellinInterior OccupiedMellinGlobalMesh

private theorem cutoff_choice (n : ℕ) (hn : 4 ^ 20 ≤ n) :
    ∃ K M : ℕ, 0 < K ∧ 2 * n < M ∧
      (M : ℝ) / n ≤ (((K : ℝ) / n)⁻¹) ∧
      (n : ℝ) ^ (-(1 / 20 : ℝ)) / 2 ≤ (K : ℝ) / n ∧
      (K : ℝ) / n ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) ∧
      ((n : ℝ) ^ (-(1 / 20 : ℝ)))⁻¹ / 2 ≤ ((M - 1 : ℕ) : ℝ) / n := by
  let N := (n : ℝ)
  let x := N ^ (-(1 / 20 : ℝ))
  let K : ℕ := ⌊N * x⌋₊
  let M : ℕ := ⌊N / x⌋₊
  have hn16 : 16 ≤ n := (by norm_num : (16 : ℕ) ≤ 4 ^ 20).trans hn
  have hN16 : 16 ≤ N := by dsimp only [N]; exact_mod_cast hn16
  have hN : 0 < N := by linarith
  have hx : 0 < x := Real.rpow_pos_of_pos hN _
  have hNu : (4 : ℝ) ^ 20 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hp : 4 ≤ N ^ (1 / 20 : ℝ) := by
    have hb := Real.rpow_le_rpow (show 0 ≤ (4 : ℝ) ^ 20 by positivity) hNu
      (by norm_num : (0 : ℝ) ≤ 1 / 20)
    have hb' : ((4 : ℝ) ^ 20) ^ (1 / 20 : ℝ) = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    exact hb' ▸ hb
  have hxsmall : x ≤ 1 / 4 := by
    dsimp only [x]
    rw [Real.rpow_neg hN.le]
    calc
      _ ≤ (4 : ℝ)⁻¹ := (inv_le_inv₀ (Real.rpow_pos_of_pos hN _) (by norm_num)).2 hp
      _ = _ := by ring
  have hlargeU : 2 ≤ N * x := by
    have hpow : N ^ (-(1 / 2 : ℝ)) ≤ x :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hpAux : N * N ^ (-(1 / 2 : ℝ)) = N ^ (1 / 2 : ℝ) := by
      calc
        _ = N ^ (1 : ℝ) * N ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    have hlow : 4 ≤ N ^ (1 / 2 : ℝ) := by
      have hs : Real.sqrt (16 : ℝ) = 4 := by
        rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← Real.sqrt_eq_rpow, ← hs]
      exact Real.sqrt_le_sqrt hN16
    exact (by linarith : (2 : ℝ) ≤ N ^ (1 / 2 : ℝ)).trans
      (hpAux ▸ mul_le_mul_of_nonneg_left hpow hN.le)
  have hlargeV : 4 * N ≤ N / x := by
    apply (le_div_iff₀ hx).2
    nlinarith only [mul_le_mul_of_nonneg_left hxsmall hN.le]
  have hKlo : N * x < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hKhi : (K : ℝ) ≤ N * x := Nat.floor_le (mul_nonneg hN.le hx.le)
  have hMlo : N / x < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMhi : (M : ℝ) ≤ N / x := Nat.floor_le (div_nonneg hN.le hx.le)
  have hK : 0 < K := by
    have : 0 < (K : ℝ) := by linarith
    exact_mod_cast this
  have hMr : 2 * N < (M : ℝ) := by linarith
  have hM : 2 * n < M := by dsimp only [N] at hMr; exact_mod_cast hMr
  have hdpos : 0 < (K : ℝ) / N := div_pos (by exact_mod_cast hK) hN
  have hdhi : (K : ℝ) / N ≤ x := by
    apply (div_le_iff₀ hN).2
    linarith only [hKhi, mul_comm N x]
  have hdlo : x / 2 ≤ (K : ℝ) / N := by
    apply (le_div_iff₀ hN).2
    linarith only [hKlo, hlargeU, show x / 2 * N = (N * x) / 2 by ring]
  have hV : (M : ℝ) / N ≤ x⁻¹ := by
    apply (div_le_iff₀ hN).2
    rwa [div_eq_mul_inv, mul_comm] at hMhi
  have hsize := hV.trans ((inv_le_inv₀ hx hdpos).2 hdhi)
  have hM1 : 1 ≤ M := by omega
  have hR : x⁻¹ / 2 ≤ ((M - 1 : ℕ) : ℝ) / N := by
    apply (le_div_iff₀ hN).2
    rw [Nat.cast_sub hM1, Nat.cast_one]
    have he : x⁻¹ / 2 * N = (N / x) / 2 := by ring
    rw [he]
    linarith
  exact ⟨K, M, hK, hM, hsize, hdlo, hdhi, hR⟩

/-- Uniform algebraic mesh error after choosing integer cutoffs. The threshold
is deliberately conservative; the series and integral have their exact
original shift, normalization, and half-line. -/
theorem global_mesh_rate {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (n : ℕ) (hn : 4 ^ 20 ≤ n) :
    Summable (fun i : ℕ => |sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)|) ∧
    IntegrableOn (sample β 0) (Ioi 0) ∧
    |(∫ t in Ioi (0 : ℝ), sample β 0 t) -
        (∑' i : ℕ, sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)) / n| ≤
      1232 * (n : ℝ) ^ (-(1 / 80 : ℝ)) := by
  obtain ⟨K,M,hK,hM,hsz,hlo,hhi,hR⟩ := cutoff_choice n hn
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 4 ^ 20) hn
  have hn0 : 0 < n := by omega
  obtain ⟨hs,hI,h⟩ := global_mesh_error hβ hβ' n K M hn0 hK hM hsz
  refine ⟨hs,hI,h.trans ?_⟩
  let X := (n : ℝ)
  let q := X ^ (-(1 / 20 : ℝ))
  let δ := (K : ℝ) / X
  let R := ((M - 1 : ℕ) : ℝ) / X
  let t := X ^ (-(1 / 80 : ℝ))
  change 64 * δ ^ (3 / 2 : ℝ) + 112 * δ ^ (1 / 4 : ℝ) + 16 * X ^ (-(1 / 4 : ℝ)) +
    (32 * δ ^ (-(17 / 4 : ℝ))) / X + 8 * R ^ (-(1 / 2 : ℝ)) ≤ 1232 * t
  have hX1 : 1 ≤ X := by dsimp only [X]; exact_mod_cast hn1
  have hX : 0 < X := by linarith
  have hq : 0 < q := Real.rpow_pos_of_pos hX _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
  have hd : 0 < δ := (show 0 < q / 2 by positivity).trans_le hlo
  have hd1 : δ ≤ 1 := hhi.trans hq1
  have ht₀ : 0 ≤ t := Real.rpow_nonneg hX.le _
  have hq4 : q ^ (1 / 4 : ℝ) = t := by
    dsimp only [q, t]
    rw [← Real.rpow_mul hX.le]
    norm_num
  have h4 : δ ^ (1 / 4 : ℝ) ≤ t := by
    rw [← hq4]
    exact Real.rpow_le_rpow hd.le hhi (by norm_num)
  have hA : δ ^ (3 / 2 : ℝ) ≤ t :=
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by norm_num)).trans h4
  have hC : X ^ (-(1 / 4 : ℝ)) ≤ t :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hab : (2 : ℝ) ^ (17 / 4 : ℝ) ≤ 32 := by
    calc
      _ ≤ (2 : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num [← Real.rpow_natCast]
  have hB : δ ^ (-(17 / 4 : ℝ)) ≤ 32 * q ^ (-(17 / 4 : ℝ)) := by
    have hB₀ := Real.rpow_le_rpow_of_nonpos (show 0 < q / 2 by positivity) hlo
      (show -(17 / 4 : ℝ) ≤ 0 by norm_num)
    refine hB₀.trans ?_
    rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hq.le _)
  have hD : (32 * δ ^ (-(17 / 4 : ℝ))) / X ≤ 1024 * t := by
    have hP : q ^ (-(17 / 4 : ℝ)) = X ^ (17 / 80 : ℝ) := by
      dsimp only [q]
      rw [← Real.rpow_mul hX.le]
      norm_num
    have hE : (32 * (32 * q ^ (-(17 / 4 : ℝ)))) / X = 1024 * X ^ (-(63 / 80 : ℝ)) := by
      rw [hP, div_eq_mul_inv, ← Real.rpow_neg_one X]
      calc
        _ = 1024 * (X ^ (17 / 80 : ℝ) * X ^ (-(1 : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hX]; norm_num
    calc
      _ ≤ (32 * (32 * q ^ (-(17 / 4 : ℝ)))) / X :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num)) hX.le
      _ = _ := hE
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by norm_num)
  have hF : R ^ (-(1 / 2 : ℝ)) ≤ 2 * t := by
    have hF₀ := Real.rpow_le_rpow_of_nonpos (show 0 < q⁻¹ / 2 by positivity) hR
      (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    have hpow : (q⁻¹ / 2) ^ (-(1 / 2 : ℝ)) = (2 : ℝ) ^ (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ) := by
      rw [Real.div_rpow (inv_nonneg.mpr hq.le) (by norm_num : (0 : ℝ) ≤ 2),
        Real.inv_rpow hq.le, Real.rpow_neg hq.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, div_inv_eq_mul, mul_comm]
    have hq2 : q ^ (1 / 2 : ℝ) ≤ t := by
      dsimp only [q, t]
      rw [← Real.rpow_mul hX.le]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      norm_num
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    rw [hpow] at hF₀
    exact hF₀.trans (mul_le_mul h2 hq2 (Real.rpow_nonneg hq.le _) (by norm_num))
  have hA' := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ 64 by norm_num)
  have h4' := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ 112 by norm_num)
  have hC' := mul_le_mul_of_nonneg_left hC (show (0 : ℝ) ≤ 16 by norm_num)
  have hF' := mul_le_mul_of_nonneg_left hF (show (0 : ℝ) ≤ 8 by norm_num)
  exact (add_le_add (add_le_add (add_le_add (add_le_add hA' h4') hC') hD) hF').trans_eq (by ring)

end D5.S1.Words.Patterns.Separable.OccupiedMellinFloors
