/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCentralMass
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual central Mellin modes and normalized finite Gaussian charge. -/
/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No Lean/kernel or acceptance claim.

Actual finite-source central charge. The imported actual weighted signed
convergence comes from weighted L1/DCT, NOT from an assumed interchange.
After mode integration, each single-atom scalar term is nonnegative: even
powers of the real q have positive J, and odd J is zero. The real nonnegative
partial-sum criterion therefore gives a genuine unconditional HasSum.
Only then are finite real linear combinations and normalized charges formed.
No Mellin functional on all H or basis completeness is needed.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfCentralNormalization
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGaussianWeightedConvergence
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianEvenExpansion
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Ring.Parity

/-! Actual central Mellin modes and normalized finite Gaussian charge. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace FiniteGaussianCap4
open LaguerreSevenHalf

private theorem actual_atom_mellin_value (a : ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) *
      LaguerreSevenHalf.gaussianAtom a x) = Real.Gamma (9 / 4) := by
  have he : LaguerreSevenHalf.gaussianAtom a = FiniteGaussianCap4.gaussianAtom a := by
    funext x
    unfold LaguerreSevenHalf.gaussianAtom FiniteGaussianCap4.gaussianAtom
    congr 1
    ring
  rw [he]
  simpa [gaussianFeature] using
    (finite_gaussian_mellin (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => a)).2

/-- Integral of each actual finite Gaussian prefix. Only a finite sum is
moved across the integral, with every summand's L1 domain proved explicitly. -/
theorem gaussianPartialSum_central_integral (a : ℝ) (N : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * gaussianPartialSum a N x) =
      ∑ n ∈ Finset.range N,
        (gaussianSiteAmplitude a * gaussianSiteQ a ^ n) * centralMellinIntegral n := by
  have hfun : (fun x : ℝ => x ^ (5 / 4 : ℝ) * gaussianPartialSum a N x) =
      (fun x : ℝ => ∑ n ∈ Finset.range N,
        (gaussianSiteAmplitude a * gaussianSiteQ a ^ n) *
          (x ^ (5 / 4 : ℝ) * phi x n)) := by
    funext x
    simp only [gaussianPartialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hfun, integral_finsetSum (Finset.range N)
    (fun n _ => (integrable_central_phi n).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

private theorem integrated_atom_term_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ (gaussianSiteAmplitude a * gaussianSiteQ a ^ n) * centralMellinIntegral n := by
  have hA : 0 < gaussianSiteAmplitude a := by
    unfold gaussianSiteAmplitude
    exact mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos (gaussianSiteQ_one_sub_pos a) _)
  obtain ⟨k, he | ho⟩ := Nat.even_or_odd' n
  · rw [he]
    have hq : 0 ≤ gaussianSiteQ a ^ (2 * k) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    exact mul_nonneg (mul_nonneg hA.le hq) (centralMellinIntegral_even_pos k).le
  · rw [ho, centralMellinIntegral_odd, mul_zero]

/-- This is the justified integral/series passage for the actual atom.
The weighted convergence supplier is genuinely consumed, then the proved
nonnegative scalar terms upgrade prefix convergence to unconditional HasSum. -/
theorem gaussian_atom_central_hasSum (a : ℝ) :
    HasSum (fun n : ℕ =>
      (gaussianSiteAmplitude a * gaussianSiteQ a ^ n) * centralMellinIntegral n)
      (Real.Gamma (9 / 4)) := by
  have h := gaussian_Mellin_signed_integral_tendsto a
  simp_rw [gaussianPartialSum_central_integral] at h
  rw [actual_atom_mellin_value] at h
  exact (hasSum_iff_tendsto_nat_of_nonneg (integrated_atom_term_nonneg a) _).2 h

/-- The actual finite coefficients, integrated mode by mode, have an absolute
real sum equal to the actual finite-source integral supplied by Gamma(9/4). -/
theorem finite_gaussian_central_hasSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    HasSum (fun n : ℕ => finiteGaussianCoefficient c site n * centralMellinIntegral n)
      (Real.Gamma (9 / 4) * ∑ i, c i) := by
  classical
  have hi (i : ι) := (gaussian_atom_central_hasSum (site i)).mul_left (c i)
  have h := hasSum_sum (s := Finset.univ) (fun i _ => hi i)
  convert h using 1
  · funext n
    simp only [finiteGaussianCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [← Finset.sum_mul]
    ring

/-- Actual normalized coefficients d_n = a_n/N_n. No expansion premise. -/
def finiteGaussianNormalizedCoefficient {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (n : ℕ) : ℝ :=
  finiteGaussianCoefficient c site n / centralNormalization n

theorem finite_gaussian_normalized_hasSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (x : ℝ) :
    HasSum (fun n : ℕ => finiteGaussianNormalizedCoefficient c site n * centralPsi x n)
      (gaussianFeature c site x) := by
  have h := finite_gaussian_hasSum c site x
  convert h using 1
  funext n
  dsimp only [finiteGaussianNormalizedCoefficient, centralPsi]
  field_simp [(centralNormalization_pos n).ne']
  <;> ring

/-- Normalized central charge, initially indexed by all modes. -/
theorem finite_gaussian_normalized_central_hasSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    HasSum (fun n : ℕ =>
      (normalizedCentralMellin n / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site n)
      ((Real.Gamma (9 / 4) / normalizedCentralMellin 0) * ∑ i, c i) := by
  have h0 : normalizedCentralMellin 0 ≠ 0 :=
    (normalizedCentralMellin_even_pos 0).ne'
  have h := (finite_gaussian_central_hasSum c site).mul_left
    (1 / normalizedCentralMellin 0)
  convert h using 1
  · funext n
    rw [normalizedCentralMellin_eq n]
    dsimp only [finiteGaussianNormalizedCoefficient]
    field_simp [h0, (centralNormalization_pos n).ne']
    <;> ring
  · ring

/-- The exact even-mode central charge. Odd integrated modes vanish by the
new actual integral theorem, so reindexing loses no contribution. -/
theorem finite_gaussian_even_central_hasSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    HasSum (fun k : ℕ =>
      (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site (2 * k))
      ((Real.Gamma (9 / 4) / normalizedCentralMellin 0) * ∑ i, c i) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b hab
    change 2 * a = 2 * b at hab
    omega
  have hout : ∀ n : ℕ, n ∉ Set.range (fun k : ℕ => 2 * k) →
      (normalizedCentralMellin n / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site n = 0 := by
    intro n hn
    obtain ⟨k, he | ho⟩ := Nat.even_or_odd' n
    · exact (hn ⟨k, he.symm⟩).elim
    · rw [ho, normalizedCentralMellin_odd, zero_div, zero_mul]
  simpa only [Function.comp_def] using
    (hinj.hasSum_iff hout).2 (finite_gaussian_normalized_central_hasSum c site)

/-- Actual sum z_k d_k=0, with absolute convergence, for finite real
mass-zero sources. This holds in particular for the SAME even source; no
evenness assumption is needed for its central integral. z_k is positive and
z_k^2 is precisely the existing weight, by normalizedCentralMellin_weight. -/
theorem finite_gaussian_central_mass_zero {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (hmass : ∑ i, c i = 0) :
    HasSum (fun k : ℕ =>
      (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
        finiteGaussianNormalizedCoefficient c site (2 * k)) 0 ∧
    Summable (fun k : ℕ => |(normalizedCentralMellin (2 * k) /
      normalizedCentralMellin 0) * finiteGaussianNormalizedCoefficient c site (2 * k)|) ∧
    (∑' k : ℕ, (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
      finiteGaussianNormalizedCoefficient c site (2 * k)) = 0 := by
  have h := finite_gaussian_even_central_hasSum c site
  rw [hmass, mul_zero] at h
  refine ⟨h, ?_, h.tsum_eq⟩
  simpa only [Real.norm_eq_abs] using h.summable.norm

/-- Parity of the actual normalized coefficients is inherited from the
supplied finite-source reflection proof; it is not asserted by symmetry alone. -/
theorem finite_gaussian_normalized_odd_zero {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (k : ℕ) :
    finiteGaussianNormalizedCoefficient c site (2 * k + 1) = 0 := by
  unfold finiteGaussianNormalizedCoefficient
  rw [finite_gaussian_odd_coefficient_zero c site reflection hc hs
    (2 * k + 1) (by exact ⟨k, by omega⟩), zero_div]

end FiniteGaussianCap4
