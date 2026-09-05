/- GID: D5/S3/Weil/ZetaBridge/WeilArchimedeanTailJet
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArchimedeanTailJet
   mirror-E: none(waiver:analytic-bound-without-floating-point-certificate)
   anchors: []
   digest: Bound every even Galerkin direction of the canonical Gamma tail by a finite boundary-moment jet. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite boundary-moment jet for the arithmetic Gamma tail

The frequency density is the even-sector Cauchy density in Theorem 3.2 of
A. Groskin, arXiv:2607.02828. Its Archimedean factor is exactly the existing
`Zeta23.EF.gammaBracket`, not a surrogate symbol. The finite matrix has support
length `L`, prime cutoff `exp L`, and frequency spacing `2*pi/L`.

The two definitions below are respectively the exact Cauchy density and its
finite geometric jet. In physical coordinates the compatible orthonormal
basis on `[-L/2,L/2]` is `1/sqrt(L)` and
`(-1)^k * sqrt(2/L) * cos(2*pi*k*x/L)` for `k>0`, zero extended.
The diagonal phase `(-1)^k` is essential to this Cauchy-coordinate convention.
The main theorem bounds their difference for every
complex coefficient vector, every order, and every frequency past the band.
It does not assume the sign of Gamma or of the complete Weil form.

After integration the bound decays like `log(T)/T^(2*m+1)` for a fixed band.
The jet preserves boundary moments instead of imposing that they vanish.
It does not establish a complement gap, certify an infinite-dimensional
window from a finite matrix, or identify true ground modes with Xi.

The Cauchy-density identification with the original trigonometric Galerkin
assembly is cited from the paper; that identification is not a theorem of
this file. No numerical eigenvalue or Gamma sign assertion is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.WeilArchimedeanTailJet

open scoped BigOperators

noncomputable section

private def evenWeight {N : ℕ} (k : Fin (N + 1)) : ℝ :=
  if k.val = 0 then 1 else Real.sqrt 2

private def frequencyRatio {N : ℕ} (L t : ℝ) (k : Fin (N + 1)) : ℝ :=
  ((2 * Real.pi / L) * (k.val : ℝ) / t) ^ 2

private def cauchyResponse {N : ℕ} (L t : ℝ) (v : Fin (N + 1) → ℂ) : ℂ :=
  ∑ k, ((evenWeight k : ℝ) : ℂ) * v k *
    (((1 - frequencyRatio L t k)⁻¹ : ℝ) : ℂ)

private def jetResponse {N : ℕ} (m : ℕ) (L t : ℝ)
    (v : Fin (N + 1) → ℂ) : ℂ :=
  ∑ k, ((evenWeight k : ℝ) : ℂ) * v k *
    ((∑ j ∈ Finset.range m, frequencyRatio L t k ^ j : ℝ) : ℂ)

private def gammaTailWeight (L t : ℝ) : ℝ :=
  (2 * (2 * Real.pi / L) / Real.pi ^ 2) *
    Zeta23.EF.gammaBracket t * Real.sin (L * t / 2) ^ 2 / t ^ 2

/-- Exact even-sector density of the omitted Archimedean Galerkin tail.
The index-zero weight is one and the positive-index weights are sqrt(2),
so the coefficient norm is the ordinary Euclidean norm. -/
def evenArchimedeanTailDensity {N : ℕ} (L t : ℝ)
    (v : Fin (N + 1) → ℂ) : ℝ :=
  gammaTailWeight L t * ‖cauchyResponse L t v‖ ^ 2

/-- A finite boundary-moment jet of the same Gamma density. Expanding the
finite sums uses only moments of orders 0,2,...,2*(m-1). No boundary moment
is required to be zero, and the Gamma weight is not truncated or changed. -/
def evenArchimedeanJetDensity {N : ℕ} (m : ℕ) (L t : ℝ)
    (v : Fin (N + 1) → ℂ) : ℝ :=
  gammaTailWeight L t * ‖jetResponse m L t v‖ ^ 2

private theorem geometric_remainder (x : ℝ) (m : ℕ) (hx : x < 1) :
    (1 - x)⁻¹ - (∑ j ∈ Finset.range m, x ^ j) = x ^ m * (1 - x)⁻¹ := by
  have hn : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  apply (mul_right_cancel₀ hn)
  rw [sub_mul, inv_mul_cancel₀ hn, geom_sum_mul_neg]
  rw [mul_assoc, inv_mul_cancel₀ hn]
  ring

private theorem geometric_bounds {x q : ℝ}
    (hx : 0 ≤ x) (hxq : x ≤ q) (hq : q < 1) (m : ℕ) :
    0 ≤ (1 - x)⁻¹ ∧ (1 - x)⁻¹ ≤ (1 - q)⁻¹ ∧
    0 ≤ (∑ j ∈ Finset.range m, x ^ j) ∧
    (∑ j ∈ Finset.range m, x ^ j) ≤ (1 - q)⁻¹ ∧
    0 ≤ (1 - x)⁻¹ - (∑ j ∈ Finset.range m, x ^ j) ∧
    (1 - x)⁻¹ - (∑ j ∈ Finset.range m, x ^ j) ≤
      q ^ m * (1 - q)⁻¹ := by
  have hxp : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_lt hxq hq)
  have hqp : 0 < 1 - q := sub_pos.mpr hq
  have hi : (1 - x)⁻¹ ≤ (1 - q)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hqp (sub_le_sub_left hxq 1)
  have hs : 0 ≤ (∑ j ∈ Finset.range m, x ^ j) :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg hx _)
  have hr := geometric_remainder x m (lt_of_le_of_lt hxq hq)
  have hr0 : 0 ≤ (1 - x)⁻¹ - (∑ j ∈ Finset.range m, x ^ j) := by
    rw [hr]
    exact mul_nonneg (pow_nonneg hx _) (inv_nonneg.mpr hxp.le)
  have hrle : (1 - x)⁻¹ - (∑ j ∈ Finset.range m, x ^ j) ≤
      q ^ m * (1 - q)⁻¹ := by
    rw [hr]
    exact mul_le_mul (pow_le_pow_left₀ hx hxq m) hi
      (inv_nonneg.mpr hxp.le) (pow_nonneg (le_trans hx hxq) _)
  exact ⟨inv_nonneg.mpr hxp.le, hi, hs, by linarith, hr0, hrle⟩

private theorem amplitude_bound {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ)
    (R : ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ R) :
    ‖∑ i, c i * (a i : ℂ)‖ ≤ (∑ i, ‖c i‖) * R := by
  calc
    _ ≤ ∑ i, ‖c i * (a i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i, ‖c i‖ * a i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i).1]
    _ ≤ ∑ i, ‖c i‖ * R := by
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (ha i).2 (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

private theorem squared_amplitude_difference {u v : ℂ} {C e : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e)
    (hu : ‖u‖ ≤ C) (hv : ‖v‖ ≤ C) (huv : ‖u - v‖ ≤ e * C) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * e * C ^ 2 := by
  calc
    _ = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v)), ← abs_mul]
      congr 1
      ring
    _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (e * C) * (2 * C) :=
      mul_le_mul huv (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg he hC)
    _ = _ := by ring

private theorem cauchy_jet_bound {n : ℕ} (c : Fin n → ℂ) (x : Fin n → ℝ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ q) (m : ℕ) :
    |‖∑ i, c i * (((1 - x i)⁻¹ : ℝ) : ℂ)‖ ^ 2 -
      ‖∑ i, c i * ((∑ j ∈ Finset.range m, x i ^ j : ℝ) : ℂ)‖ ^ 2| ≤
      2 * q ^ m * ((∑ i, ‖c i‖) * (1 - q)⁻¹) ^ 2 := by
  have hb (i : Fin n) := geometric_bounds (hx i).1 (hx i).2 hq1 m
  have hu := amplitude_bound c (fun i => (1 - x i)⁻¹) ((1 - q)⁻¹)
    (fun i => ⟨(hb i).1, (hb i).2.1⟩)
  have hv := amplitude_bound c (fun i => ∑ j ∈ Finset.range m, x i ^ j)
    ((1 - q)⁻¹) (fun i => ⟨(hb i).2.2.1, (hb i).2.2.2.1⟩)
  have he := amplitude_bound c
    (fun i => (1 - x i)⁻¹ - ∑ j ∈ Finset.range m, x i ^ j)
    (q ^ m * (1 - q)⁻¹)
    (fun i => ⟨(hb i).2.2.2.2.1, (hb i).2.2.2.2.2⟩)
  have hsub :
      (∑ i, c i * (((1 - x i)⁻¹ : ℝ) : ℂ)) -
        (∑ i, c i * ((∑ j ∈ Finset.range m, x i ^ j : ℝ) : ℂ)) =
      ∑ i, c i * (((1 - x i)⁻¹ - ∑ j ∈ Finset.range m, x i ^ j : ℝ) : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  apply squared_amplitude_difference
    (mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (inv_nonneg.mpr (sub_pos.mpr hq1).le)) (pow_nonneg hq0 _) hu hv
  rw [hsub]
  simpa only [mul_left_comm, mul_assoc] using he

private theorem evenWeight_nonneg {N : ℕ} (k : Fin (N + 1)) : 0 ≤ evenWeight k := by
  unfold evenWeight
  split_ifs <;> positivity

private theorem evenWeight_sum_sq (N : ℕ) :
    (∑ k : Fin (N + 1), evenWeight k ^ 2) = 2 * (N : ℝ) + 1 := by
  rw [Fin.sum_univ_succ]
  simp only [evenWeight, Fin.val_zero, ite_true, one_pow, Fin.val_succ,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem even_coefficient_mass (N : ℕ) (v : Fin (N + 1) → ℂ) :
    (∑ k, ‖((evenWeight k : ℝ) : ℂ) * v k‖) ^ 2 ≤
      (2 * (N : ℝ) + 1) * ∑ k, ‖v k‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin (N + 1) => evenWeight k) (fun k => ‖v k‖)
  rw [evenWeight_sum_sq] at h
  have hn (k : Fin (N + 1)) : ‖((evenWeight k : ℝ) : ℂ) * v k‖ =
      evenWeight k * ‖v k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (evenWeight_nonneg k)]
  simpa only [hn] using h

private theorem band_bounds {N : ℕ} {L t : ℝ}
    (hL : 0 < L) (ht : (2 * Real.pi / L) * (N : ℝ) < t) :
    0 ≤ (((2 * Real.pi / L) * (N : ℝ) / t) ^ 2) ∧
    (((2 * Real.pi / L) * (N : ℝ) / t) ^ 2) < 1 ∧
    ∀ k : Fin (N + 1), 0 ≤ frequencyRatio L t k ∧
      frequencyRatio L t k ≤ (((2 * Real.pi / L) * (N : ℝ) / t) ^ 2) := by
  have hrho : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have htn : 0 < t := lt_of_le_of_lt (mul_nonneg hrho.le hN) ht
  have hR0 : 0 ≤ (2 * Real.pi / L) * (N : ℝ) / t :=
    div_nonneg (mul_nonneg hrho.le hN) htn.le
  have hR1 : (2 * Real.pi / L) * (N : ℝ) / t < 1 :=
    (div_lt_one htn).mpr ht
  refine ⟨sq_nonneg _, ?_, ?_⟩
  · have hsq := mul_le_mul_of_nonneg_left hR1.le hR0
    nlinarith
  · intro k
    have hk : (k.val : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.le_of_lt_succ k.isLt)
    have hk0 : 0 ≤ (2 * Real.pi / L) * (k.val : ℝ) / t := by positivity
    have hkle : (2 * Real.pi / L) * (k.val : ℝ) / t ≤
        (2 * Real.pi / L) * (N : ℝ) / t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk hrho.le) htn.le
    refine ⟨sq_nonneg _, ?_⟩
    unfold frequencyRatio
    nlinarith [mul_nonneg (sub_nonneg.mpr hkle) (add_nonneg hR0 hk0)]

/-- Uniform, parameterized error for the concrete canonical Gamma tail.
Writing `q=((2*pi/L)*N/t)^2`, the bound is
`|w(t)| * 2*q^m/(1-q)^2 * (2*N+1) * ||v||_2^2`.
It holds for every complex even-sector coefficient vector, including vectors
with nonzero boundary values. The Gamma sign is not assumed. In particular,
the difference of the two positive Gram densities must not be assumed positive.
The conclusion is a two-sided quadratic-form error, not a ground-state gap. -/
theorem even_archimedean_tail_density_jet_error {N : ℕ} (m : ℕ)
    {L t : ℝ} (hL : 0 < L) (ht : (2 * Real.pi / L) * (N : ℝ) < t)
    (v : Fin (N + 1) → ℂ) :
    |evenArchimedeanTailDensity L t v - evenArchimedeanJetDensity m L t v| ≤
      |(2 * (2 * Real.pi / L) / Real.pi ^ 2) *
        Zeta23.EF.gammaBracket t * Real.sin (L * t / 2) ^ 2 / t ^ 2| *
        (2 * ((((2 * Real.pi / L) * (N : ℝ) / t) ^ 2) ^ m) *
          (1 - (((2 * Real.pi / L) * (N : ℝ) / t) ^ 2))⁻¹ ^ 2) *
        ((2 * (N : ℝ) + 1) * ∑ k, ‖v k‖ ^ 2) := by
  let q : ℝ := ((2 * Real.pi / L) * (N : ℝ) / t) ^ 2
  have hb := band_bounds hL ht
  have h := cauchy_jet_bound
    (fun k => ((evenWeight k : ℝ) : ℂ) * v k) (frequencyRatio L t)
    hb.1 hb.2.1 hb.2.2 m
  have hc := even_coefficient_mass N v
  have hp : 0 ≤ 2 * q ^ m * (1 - q)⁻¹ ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb.1 _)) (sq_nonneg _)
  have hcore : |‖cauchyResponse L t v‖ ^ 2 - ‖jetResponse m L t v‖ ^ 2| ≤
      (2 * q ^ m * (1 - q)⁻¹ ^ 2) *
        ((2 * (N : ℝ) + 1) * ∑ k, ‖v k‖ ^ 2) := by
    calc
      _ ≤ 2 * q ^ m *
          ((∑ k, ‖((evenWeight k : ℝ) : ℂ) * v k‖) * (1 - q)⁻¹) ^ 2 := h
      _ = (2 * q ^ m * (1 - q)⁻¹ ^ 2) *
          (∑ k, ‖((evenWeight k : ℝ) : ℂ) * v k‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hp
  unfold evenArchimedeanTailDensity evenArchimedeanJetDensity
  rw [← mul_sub, abs_mul]
  calc
    _ ≤ |gammaTailWeight L t| *
        ((2 * q ^ m * (1 - q)⁻¹ ^ 2) *
          ((2 * (N : ℝ) + 1) * ∑ k, ‖v k‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hcore (abs_nonneg _)
    _ = _ := by dsimp [q, gammaTailWeight]; ring

#print axioms even_archimedean_tail_density_jet_error

end
end D5.S3.Weil.ZetaBridge.WeilArchimedeanTailJet
