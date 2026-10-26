/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianInfiniteJacobi
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian infinite Jacobi energy and complete boundary payment. -/
/-
SPDX-License-Identifier: Apache-2.0
Finite-source Gaussian Jacobi development, 2026-10-26.

Actual infinite Jacobi energy and complete boundary payment for the SAME
finite real reflection-invariant Gaussian source. Coefficients, expansion,
orthogonality, graph convergence and summability are derived in imported
proofs, not hypotheses of the public actual-source theorems below.
The tail charge consumes the existing complete_tail_charge_bound and weight.
All imported supplier attribution and license notices remain applicable.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianJacobiSummability

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace FiniteGaussianCap4
open LaguerreSevenHalf

private theorem sum_range_two_blocks (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), f n) =
      ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

private theorem normalized_mode_eq {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (n : ℕ) (x : ℝ) :
    finiteGaussianNormalizedCoefficient c site n * centralPsi x n =
      finiteGaussianCoefficient c site n * phi x n := by
  dsimp only [finiteGaussianNormalizedCoefficient, centralPsi]
  field_simp [(centralNormalization_pos n).ne']
  <;> ring

/-- The literal finite even polynomial is the supplied atom prefix at 2N. -/
theorem finiteGaussian_evenPolynomial_eq {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (N : ℕ) (x : ℝ) :
    physicalPolynomial (evenPolynomial
      (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) N) x =
      finiteGaussianPartialSum c site (2 * N) x := by
  rw [physical_evenPolynomial, finiteGaussianPartialSum_eq_modes, sum_range_two_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  rw [finite_gaussian_odd_coefficient_zero c site reflection hc hs (2 * k + 1)
    (by exact ⟨k, by omega⟩), zero_mul, add_zero, normalized_mode_eq]

/-- Actual graph convergence for the reflected even polynomial prefixes. -/
theorem finiteGaussian_even_graph_convergence {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    Tendsto (fun N => ∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) *
      |physicalPolynomial (evenPolynomial
        (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) N) x -
          gaussianFeature c site x| ^ 2) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N ≤ 2 * N; omega) tendsto_id
  simpa only [finiteGaussian_evenPolynomial_eq c site reflection hc hs, Function.comp_def] using
    ((finiteGaussian_weighted_square_error_convergence c site (11 / 2) (by norm_num)).2.comp ht)

theorem finiteGaussian_even_energy_convergence {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    Tendsto (fun N => evenJacobiEnergy
      (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) N) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2)) := by
  have ht : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N ≤ 2 * N; omega) tendsto_id
  simpa only [evenJacobiEnergy_integral,
    finiteGaussian_evenPolynomial_eq c site reflection hc hs, Function.comp_def] using
    ((finiteGaussian_weighted_energy_convergence c site (11 / 2) (by norm_num)).2.2.comp ht)

/-- The actual infinite quadratic form. Every edge is present; both scalar
series are genuinely summable by finiteGaussian_actual_jacobi_summability. -/
theorem finiteGaussian_actual_infinite_jacobi {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    (∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2) =
      (∑' k : ℕ, jacobiD k * finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) +
        2 * ∑' k : ℕ, jacobiB k * finiteGaussianNormalizedCoefficient c site (2 * k) *
          finiteGaussianNormalizedCoefficient c site (2 * (k + 1)) := by
  let d : ℕ → ℝ := fun k => finiteGaussianNormalizedCoefficient c site (2 * k)
  obtain ⟨hD, hB, _hpositive, _hH⟩ := finiteGaussian_actual_jacobi_summability c site
  have ht : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N ≤ N + 1; omega) tendsto_id
  have he := (finiteGaussian_even_energy_convergence c site reflection hc hs).comp ht
  have hq : Tendsto (fun N => evenJacobiEnergy d (N + 1)) atTop
      (𝓝 ((∑' k : ℕ, jacobiD k * d k ^ 2) +
        2 * ∑' k : ℕ, jacobiB k * d k * d (k + 1))) := by
    simpa only [evenJacobiEnergy_finite, Nat.add_sub_cancel, Function.comp_apply, d] using
      (hD.hasSum.tendsto_sum_nat.comp ht).add
        (tendsto_const_nhds.mul hB.hasSum.tendsto_sum_nat)
  exact tendsto_nhds_unique he hq

/-- Exact head 0..15 and edges 0..14; EVERY edge from k=15 onwards is
paid by a square. The lower bound retains the complete positive tail. -/
theorem finiteGaussian_actual_boundary_payment {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    jacobiPaidHead (fun k => finiteGaussianNormalizedCoefficient c site (2 * k)) +
      (∑' i : ℕ, (2 * (16 + i : ℕ) + 9 / 4 : ℝ) ^ 2 *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + i)) ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) * gaussianFeature c site x ^ 2 := by
  let d : ℕ → ℝ := fun k => finiteGaussianNormalizedCoefficient c site (2 * k)
  have hpositive := (finiteGaussian_actual_jacobi_summability c site).2.2.1
  have hi : Function.Injective (fun i : ℕ => 16 + i) := by
    intro a b h
    change 16 + a = 16 + b at h
    omega
  have ht := hpositive.comp_injective hi
  have hleft := (tendsto_const_nhds (x := jacobiPaidHead d)).add ht.hasSum.tendsto_sum_nat
  have hindex : Tendsto (fun m : ℕ => 16 + m) atTop atTop :=
    tendsto_atTop_mono (fun m => by change m ≤ 16 + m; omega) tendsto_id
  have hright := (finiteGaussian_even_energy_convergence c site reflection hc hs).comp hindex
  apply le_of_tendsto_of_tendsto' hleft hright
  intro m
  change jacobiPaidHead d + (∑ i ∈ Finset.range m,
    (2 * (16 + i : ℕ) + 9 / 4 : ℝ) ^ 2 * d (16 + i) ^ 2) ≤
      evenJacobiEnergy d (16 + m)
  have h := jacobi_paid_prefix_with_endpoint d m
  have hr : 0 ≤ jacobiR (15 + m) * d (15 + m) ^ 2 :=
    mul_nonneg (jacobiR_nonneg _) (sq_nonneg _)
  exact le_trans (le_add_of_nonneg_right hr) h

/-- The actual tail's H energy is summable and nonnegative, with the existing H. -/
theorem finiteGaussian_actual_positive_tailH {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    Summable (fun n : ℕ => tailH (16 + n : ℕ) *
      finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2) ∧
    ∀ n : ℕ, 0 ≤ tailH (16 + n : ℕ) *
      finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2 := by
  refine ⟨(finiteGaussian_actual_jacobi_summability c site).2.2.2.comp_injective
    (fun a b h => by omega), ?_⟩
  intro n
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hh : 0 ≤ tailH (16 + n : ℕ) := by
    unfold tailH
    push_cast
    nlinarith [sq_nonneg (n : ℝ)]
  exact mul_nonneg hh (sq_nonneg _)

/-- Feed the existing complete-tail charge theorem with ACTUAL summable
energy. z_k is the already supplied normalized actual central integral.
No physical expansion, recurrence or graph hypothesis is introduced. -/
theorem finiteGaussian_actual_complete_tail_charge {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    rho * (∑' n : ℕ,
      (normalizedCentralMellin (2 * (16 + n)) / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n))) ^ 2 ≤
      ∑' n : ℕ, tailH (16 + n : ℕ) *
        finiteGaussianNormalizedCoefficient c site (2 * (16 + n)) ^ 2 := by
  let z (n : ℕ) : ℝ := normalizedCentralMellin (2 * (16 + n)) / normalizedCentralMellin 0
  let d (n : ℕ) : ℝ := finiteGaussianNormalizedCoefficient c site (2 * (16 + n))
  let u (n : ℕ) : ℝ := d n / z n
  have hz (n : ℕ) : z n ≠ 0 := (div_pos
    (normalizedCentralMellin_even_pos _) (normalizedCentralMellin_even_pos 0)).ne'
  have hw (n : ℕ) : weight (16 + n) = z n ^ 2 :=
    (normalizedCentralMellin_weight (16 + n)).2.symm
  have henergy (n : ℕ) : tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2 =
      tailH (16 + n : ℕ) * d n ^ 2 := by
    rw [hw]
    dsimp only [u]
    field_simp [hz n]
    <;> ring
  have hcharge (n : ℕ) : weight (16 + n) * u n = z n * d n := by
    rw [hw]
    dsimp only [u]
    field_simp [hz n]
    <;> ring
  have he : Summable (fun n : ℕ => tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2) := by
    simpa only [henergy] using (finiteGaussian_actual_positive_tailH c site).1
  simpa only [hcharge, henergy] using (complete_tail_charge_bound u he).2

end FiniteGaussianCap4
