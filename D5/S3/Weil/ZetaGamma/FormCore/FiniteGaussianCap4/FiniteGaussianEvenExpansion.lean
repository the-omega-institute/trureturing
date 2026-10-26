/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianEvenExpansion
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian expansion and odd coefficient cancellation. -/
/-
UNCOMPILED SOURCE PROPOSAL. No Lean/kernel or official acceptance.
The actual finite Gaussian feature inherits its expansion and odd-mode
cancellation from the explicitly generated atom series. No basis-completeness
or physical-target inequality is assumed. This source supplies only this
finite-source bridge, not the complete M>19/4 theorem.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianMellin
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGaussianBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! Actual finite Gaussian expansion and odd coefficient cancellation. -/

set_option autoImplicit false
noncomputable section
namespace FiniteGaussianCap4
open scoped BigOperators
open LaguerreSevenHalf

theorem site_q_neg (a : ℝ) : gaussianSiteQ (-a) = -gaussianSiteQ a := by
  have he : Real.exp (2 * a) ≠ 0 := (Real.exp_pos _).ne'
  have hd : Real.exp (2 * a) + 1 ≠ 0 := by positivity
  have hneg : Real.exp (2 * -a) = (Real.exp (2 * a))⁻¹ := by
    rw [show 2 * -a = -(2 * a) by ring, Real.exp_neg]
  unfold gaussianSiteQ
  rw [hneg]
  field_simp [he, hd]
  <;> ring

theorem site_amplitude_neg (a : ℝ) :
    gaussianSiteAmplitude (-a) = gaussianSiteAmplitude a := by
  have hp : 0 < 1 - gaussianSiteQ a := gaussianSiteQ_one_sub_pos a
  have hm : 1 + gaussianSiteQ a = Real.exp (2 * a) * (1 - gaussianSiteQ a) := by
    exact (div_eq_iff hp.ne').mp (gaussianSiteQ_mobius a)
  unfold gaussianSiteAmplitude
  rw [site_q_neg, sub_neg_eq_add, hm,
    Real.mul_rpow (Real.exp_pos _).le hp.le, ← Real.exp_mul]
  calc
    Real.exp (9 * -a / 2) *
        (Real.exp (2 * a * (9 / 2 : ℝ)) * (1 - gaussianSiteQ a) ^ (9 / 2 : ℝ)) =
        (Real.exp (9 * -a / 2) * Real.exp (2 * a * (9 / 2 : ℝ))) *
          (1 - gaussianSiteQ a) ^ (9 / 2 : ℝ) := by ring
    _ = Real.exp (9 * a / 2) * (1 - gaussianSiteQ a) ^ (9 / 2 : ℝ) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Actual unnormalized Laguerre coefficients of the finite physical feature. -/
def finiteGaussianCoefficient {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, c i * gaussianSiteAmplitude (site i) * gaussianSiteQ (site i) ^ n

/-- The atom expansion is consumed in a literal finite-source HasSum.
There is no expansion or completeness premise. -/
theorem finite_gaussian_hasSum {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (x : ℝ) :
    HasSum (fun n : ℕ => finiteGaussianCoefficient c site n * phi x n)
      (gaussianFeature c site x) := by
  classical
  have hatom (i : ι) :
      HasSum (fun n : ℕ =>
        c i * ((gaussianSiteAmplitude (site i) * phi x n) * gaussianSiteQ (site i) ^ n))
        (c i * FiniteGaussianCap4.gaussianAtom (site i) x) := by
    have hs := (gaussian_atom_hasSum (site i) x).mul_left (c i)
    convert hs using 1 <;> simp only [FiniteGaussianCap4.gaussianAtom] <;> congr 2 <;> ring
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => hatom i)
  convert hs using 1
  · funext n
    simp only [finiteGaussianCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rfl

private theorem finite_coefficient_parity {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (n : ℕ) :
    finiteGaussianCoefficient c site n =
      (-1 : ℝ) ^ n * finiteGaussianCoefficient c site n := by
  classical
  unfold finiteGaussianCoefficient
  calc
    (∑ i, c i * gaussianSiteAmplitude (site i) * gaussianSiteQ (site i) ^ n) =
        ∑ i, c (reflection i) * gaussianSiteAmplitude (site (reflection i)) *
          gaussianSiteQ (site (reflection i)) ^ n :=
      (Equiv.sum_comp reflection _).symm
    _ = ∑ i, (-1 : ℝ) ^ n *
        (c i * gaussianSiteAmplitude (site i) * gaussianSiteQ (site i) ^ n) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i, hs i, site_amplitude_neg, site_q_neg,
        neg_eq_neg_one_mul, mul_pow]
      ring
    _ = (-1 : ℝ) ^ n *
        ∑ i, c i * gaussianSiteAmplitude (site i) * gaussianSiteQ (site i) ^ n := by
      rw [Finset.mul_sum]

/-- An even finite source has literally zero odd coefficients. The reflection
is a permutation of the finite source sites preserving coefficients and
negating their real locations; no conclusion is assumed as input. -/
theorem finite_gaussian_odd_coefficient_zero {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) (n : ℕ) (hn : Odd n) :
    finiteGaussianCoefficient c site n = 0 := by
  have h := finite_coefficient_parity c site reflection hc hs n
  rw [hn.neg_one_pow, neg_one_mul] at h
  linarith

end FiniteGaussianCap4
