/- GID: D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail
   mirror-E: none(waiver:analytic-dual-tail-with-separate-interval-realization)
   anchors: []
   digest: Absolutely convergent arithmetic dual Fourier tails with a quadratic truncation rate, from the actual prime-pole-Gamma symbol. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-!
# The arithmetic high-to-low Fourier readout is effectively summable

For m=M+j+1 the actual even arithmetic coupling has coefficient proportional
  (n*s_c(n)-m*s_c(m))/(m^2-n^2),
and its complex Fourier observation contributes 1/(m^2-w^2).
This file uses exactly `arithmeticBoundarySymbol`, whose independent uniform
bound is proved in `WeilArithmeticCouplingJet`. It proves convergence of the
complete dual series and an explicit M^-2 tail bound. The positive energy
weights are independently supplied scalars, not an assumed bound on the dual
series or on an unknown operator. Piecewise rational Neumann weights in the
executed checker are a concrete consumer of these hypotheses.

The physical Fourier prefactor, even-basis identification, full form/domain
bridge and constrained Schur readout are given in the existing RH theory
volume. This declaration does not assume or prove Xi convergence or a spectral
gap. The checker separately counts a zero of the actual fixed-window ground
transform; its interval computation is not a Lean kernel replay.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.WeilArithmeticFourierDualTail

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

private def tailIndex (M j : ℕ) : ℕ := M + j + 1
private def inverseCube (M j : ℕ) : ℝ := 1 / ((tailIndex M j : ℕ) : ℝ) ^ 3

/-- The actual arithmetic part of one even Fourier dual-tail column.
Physical frequency w=L*z/(2*pi). Its Fourier normalization is a single
explicit prefactor, kept outside this dimensionless series. -/
def arithmeticEvenDualTerm (c n M : ℕ) (energy : ℕ → ℝ) (w : ℂ) (j : ℕ) : ℂ :=
  let m := tailIndex M j
  ((((n : ℝ) * arithmeticBoundarySymbol c (n : ℤ) -
      (m : ℝ) * arithmeticBoundarySymbol c (m : ℤ)) /
      ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) : ℝ) : ℂ) /
    (energy j : ℂ) / ((m : ℂ) ^ 2 - w ^ 2)

private theorem inverse_cube_step {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 3 ≤ 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) := by
  have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
  have hid : (1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2)) - 1 / (x + 1) ^ 3 =
      (3 * x + 1) / (2 * x ^ 2 * (x + 1) ^ 3) := by
    field_simp [hx.ne', hx1]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  positivity

private theorem inverse_cube_partial {M : ℕ} (hM : 0 < M) (K : ℕ) :
    (∑ j ∈ Finset.range K, inverseCube M j) ≤
      1 / (2 * (M : ℝ) ^ 2) - 1 / (2 * ((M : ℝ) + (K : ℝ)) ^ 2) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have ht := inverse_cube_step (show 0 < (M : ℝ) + (K : ℝ) by positivity)
      dsimp [inverseCube, tailIndex] at ih ⊢
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, ← add_assoc] at ih ⊢
      linarith

private theorem inverse_cube_partial_bound {M : ℕ} (hM : 0 < M) (K : ℕ) :
    (∑ j ∈ Finset.range K, inverseCube M j) ≤ 1 / (2 * (M : ℝ) ^ 2) := by
  have ht := inverse_cube_partial hM K
  have hp : 0 ≤ 1 / (2 * ((M : ℝ) + (K : ℝ)) ^ 2) := by positivity
  linarith

private theorem coefficient_bound {n m sn sm B : ℝ}
    (hn : 0 ≤ n) (hm : n < m) (hsn : |sn| ≤ B) (hsm : |sm| ≤ B) :
    |(n * sn - m * sm) / (m ^ 2 - n ^ 2)| ≤ B / (m - n) := by
  have hm0 : 0 < m := lt_of_le_of_lt hn hm
  have hmn : 0 < m - n := sub_pos.mpr hm
  have hsum : 0 < m + n := by linarith
  have hden : 0 < m ^ 2 - n ^ 2 := by nlinarith [mul_pos hmn hsum]
  have hb : 0 ≤ B := (abs_nonneg sn).trans hsn
  have hnum : |n * sn - m * sm| ≤ (m + n) * B := by
    calc
      _ ≤ |n * sn| + |m * sm| := abs_sub _ _
      _ = n * |sn| + m * |sm| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn, abs_of_pos hm0]
      _ ≤ n * B + m * B := add_le_add
        (mul_le_mul_of_nonneg_left hsn hn) (mul_le_mul_of_nonneg_left hsm hm0.le)
      _ = _ := by ring
  rw [abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ (m + n) * B := hnum
    _ = (B / (m - n)) * (m ^ 2 - n ^ 2) := by
      field_simp [hmn.ne']
      <;> ring

private theorem fourier_inverse_bound {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : ‖w‖ ≤ m / 2) :
    ‖((m : ℂ) ^ 2 - w ^ 2)⁻¹‖ ≤ 4 / (3 * m ^ 2) := by
  have hw2 : ‖w‖ ^ 2 ≤ m ^ 2 / 4 := by
    have ht := pow_le_pow_left₀ (norm_nonneg w) hw 2
    nlinarith
  have hr := norm_sub_norm_le ((m : ℂ) ^ 2) (w ^ 2)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm] at hr
  have hd : (3 / 4 : ℝ) * m ^ 2 ≤ ‖(m : ℂ) ^ 2 - w ^ 2‖ := by linarith
  calc
    _ = 1 / ‖(m : ℂ) ^ 2 - w ^ 2‖ := by rw [norm_inv, one_div]
    _ ≤ 1 / ((3 / 4 : ℝ) * m ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hd
    _ = _ := by field_simp [hm.ne']; ring

private theorem dual_term_bound {c : ℕ} (hc : 2 ≤ c)
    {n M : ℕ} (hnM : n < M) {β : ℝ} (hβ : 0 < β)
    (energy : ℕ → ℝ) (he : ∀ j, β ≤ energy j)
    {w : ℂ} (hw : ‖w‖ ≤ (M : ℝ) / 2) (j : ℕ) :
    ‖arithmeticEvenDualTerm c n M energy w j‖ ≤
      (4 * arithmeticBoundaryBudget c * (M : ℝ) /
        (3 * β * ((M : ℝ) - (n : ℝ)))) * inverseCube M j := by
  let m : ℝ := (tailIndex M j : ℝ)
  let B : ℝ := arithmeticBoundaryBudget c
  let q : ℝ := ((n : ℝ) * arithmeticBoundarySymbol c (n : ℤ) -
    m * arithmeticBoundarySymbol c ((tailIndex M j : ℕ) : ℤ)) / (m ^ 2 - (n : ℝ) ^ 2)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnMr : (n : ℝ) < (M : ℝ) := by exact_mod_cast hnM
  have hM0 : 0 < (M : ℝ) := lt_of_le_of_lt hn0 hnMr
  have hMm : (M : ℝ) ≤ m := by
    dsimp [m, tailIndex]
    push_cast
    linarith [Nat.cast_nonneg j]
  have hnm : (n : ℝ) < m := lt_of_lt_of_le hnMr hMm
  have hm0 : 0 < m := lt_of_lt_of_le hM0 hMm
  have hb : 0 ≤ B := (abs_nonneg _).trans (arithmetic_boundary_symbol_bound hc (n : ℤ)).2
  have hq : |q| ≤ B / (m - (n : ℝ)) := coefficient_bound hn0 hnm
    (arithmetic_boundary_symbol_bound hc (n : ℤ)).2
    (arithmetic_boundary_symbol_bound hc ((tailIndex M j : ℕ) : ℤ)).2
  have hei : |(energy j)⁻¹| ≤ 1 / β := by
    rw [abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hβ (he j))), ← one_div]
    exact one_div_le_one_div_of_le hβ (he j)
  have hfi := fourier_inverse_bound hm0 (hw.trans (by linarith : (M : ℝ) / 2 ≤ m / 2))
  have hsep : B / (m - (n : ℝ)) ≤ B * (M : ℝ) / (((M : ℝ) - (n : ℝ)) * m) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hnm)
      (mul_pos (sub_pos.mpr hnMr) hm0)).mpr
    have hh : ((M : ℝ) - (n : ℝ)) * m ≤ (M : ℝ) * (m - (n : ℝ)) := by
      nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hMm)]
    nlinarith [mul_le_mul_of_nonneg_left hh hb]
  have hprod : |q| * |(energy j)⁻¹| * ‖((m : ℂ) ^ 2 - w ^ 2)⁻¹‖ ≤
      (B / (m - (n : ℝ))) * (1 / β) * (4 / (3 * m ^ 2)) := by
    apply mul_le_mul
      (mul_le_mul hq hei (abs_nonneg _) (by positivity)) hfi
      (norm_nonneg _) (by positivity)
  change ‖(q : ℂ) / (energy j : ℂ) / ((m : ℂ) ^ 2 - w ^ 2)‖ ≤ _
  simp only [div_eq_mul_inv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hid : |energy j|⁻¹ = |(energy j)⁻¹| := (abs_inv _).symm
  rw [hid]
  calc
    _ ≤ (B / (m - (n : ℝ))) * (1 / β) * (4 / (3 * m ^ 2)) := by
      simpa only [norm_inv] using hprod
    _ ≤ (B * (M : ℝ) / (((M : ℝ) - (n : ℝ)) * m)) * (1 / β) *
        (4 / (3 * m ^ 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsep (by positivity)) (by positivity)
    _ = _ := by
      change _ = (4 * B * (M : ℝ) / (3 * β * ((M : ℝ) - (n : ℝ)))) * (1 / m ^ 3)
      field_simp [hβ.ne', hm0.ne', (sub_pos.mpr hnMr).ne']
      <;> ring

/-- The complete arithmetic dual tail is absolutely convergent with an explicit
quadratic cutoff rate. The only energy hypothesis is a positive scalar floor
for the chosen diagonal weights. The actual arithmetic symbol is bounded by
its independently proved prime-pole-Gamma budget inside the proof. -/
theorem arithmetic_even_fourier_dual_tail_bound {c : ℕ} (hc : 2 ≤ c)
    {n M : ℕ} (hnM : n < M) {β : ℝ} (hβ : 0 < β)
    (energy : ℕ → ℝ) (he : ∀ j, β ≤ energy j)
    (w : ℂ) (hw : ‖w‖ ≤ (M : ℝ) / 2) :
    Summable (fun j => ‖arithmeticEvenDualTerm c n M energy w j‖) ∧
    ‖∑' j : ℕ, arithmeticEvenDualTerm c n M energy w j‖ ≤
      2 * arithmeticBoundaryBudget c /
        (3 * β * (M : ℝ) * ((M : ℝ) - (n : ℝ))) := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le n) hnM
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsep : 0 < (M : ℝ) - (n : ℝ) := sub_pos.mpr (by exact_mod_cast hnM)
  have hb : 0 ≤ arithmeticBoundaryBudget c :=
    (abs_nonneg _).trans (arithmetic_boundary_symbol_bound hc (n : ℤ)).2
  let K : ℝ := 4 * arithmeticBoundaryBudget c * (M : ℝ) /
    (3 * β * ((M : ℝ) - (n : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnon (j : ℕ) : 0 ≤ inverseCube M j := by dsimp [inverseCube]; positivity
  have hs : Summable (inverseCube M) :=
    summable_of_sum_range_le hnon (inverse_cube_partial_bound hM)
  have hsum : (∑' j : ℕ, inverseCube M j) ≤ 1 / (2 * (M : ℝ) ^ 2) :=
    Real.tsum_le_of_sum_range_le hnon (inverse_cube_partial_bound hM)
  have ht (j : ℕ) : ‖arithmeticEvenDualTerm c n M energy w j‖ ≤ K * inverseCube M j :=
    dual_term_bound hc hnM hβ energy he hw j
  have hsabs : Summable (fun j => ‖arithmeticEvenDualTerm c n M energy w j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ht (hs.mul_left K)
  refine ⟨hsabs, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, ‖arithmeticEvenDualTerm c n M energy w j‖ := norm_tsum_le_tsum_norm hsabs
    _ ≤ ∑' j : ℕ, K * inverseCube M j := hsabs.tsum_le_tsum ht (hs.mul_left K)
    _ = K * ∑' j : ℕ, inverseCube M j := by rw [tsum_mul_left]
    _ ≤ K * (1 / (2 * (M : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hsum hK
    _ = _ := by
      dsimp [K]
      field_simp [hβ.ne', hMr.ne', hsep.ne']
      <;> ring

#print axioms arithmetic_even_fourier_dual_tail_bound

end D5.S3.Weil.ZetaBridge.WeilArithmeticFourierDualTail
