/- GID: D5/S3/Weil/FourierReadout/PaperFTWindowLimit
   generality: G
   mirror-B: D5/B/S3/Weil/FourierReadout/PaperFTWindowLimit
   mirror-E: none(waiver:analytic-uniform-limit)
   anchors: []
   digest: Transfer genuine window L2 and Rayleigh error rates into uniform limits of the existing paperFT. -/

import D5.S3.Weil.FourierReadout.ProjectivePaperFTCertificate
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
No decay rate for the arithmetic Weil family or convergence to Xi is assumed
silently. These theorems make the required rate and the candidate limit
explicit. The actual Fourier/L2 identification is a proved dependency.
`TendstoUniformlyOn` is Mathlib's standard predicate. The strip is unbounded
in the real direction; the kernel estimate depends only on its height.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.FourierReadout.PaperFTWindowLimit

open Filter MeasureTheory Set
open D5.S3.Weil.FourierReadout.WindowPaperFTReadout
open D5.S3.Weil.FourierReadout.ProjectivePaperFTCertificate
open D5.S3.Observer.Hankel.ProjectiveRayleighReadout
open scoped Topology ComplexInnerProductSpace

/-- The previously derived actual Fourier error tends uniformly to zero on
the full strip whenever the scaled L2 rate pays the window-growth factor. -/
theorem paperFT_window_uniform_error
    {J : Type*} (l : Filter J) (a : J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (f g : ∀ j, WindowL2 (a j)) (c : J → ℂ) (b : ℝ)
    (hsmall : Tendsto (fun j => ‖c j‖ *
      (Real.sqrt (2 * a j) * Real.exp (b * a j)) * ‖f j - g j‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun j z => c j *
      (Zeta23.paperFT ((Icc (-a j) (a j)).indicator (f j : ℝ → ℂ)) z -
        Zeta23.paperFT ((Icc (-a j) (a j)).indicator (g j : ℝ → ℂ)) z))
      (fun _ => 0) l {z : ℂ | |z.im| ≤ b} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [(tendsto_order.mp hsmall).2 eps heps] with j hj z hz
  simp only [dist_zero_left, norm_mul]
  have h := mul_le_mul_of_nonneg_left (paperFT_window_sub_le (ha j) (f j) (g j) z hz)
    (norm_nonneg (c j))
  calc
    _ ≤ _ := h
    _ < eps := by simpa only [mul_assoc] using hj

/-- A squared projective error budget gives the explicit sufficient rate
||c_j|| sqrt(2a_j) exp(b*a_j) sqrt(delta_j) -> 0 for actual Fourier integrals. -/
theorem paperFT_projective_uniform_error
    {J : Type*} (l : Filter J) (a : J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (k w : ∀ j, WindowL2 (a j)) (delta : J → ℝ) (c : J → ℂ) (b : ℝ)
    (he : ∀ j, ‖w j‖ ^ 2 ≤ delta j)
    (hsmall : Tendsto (fun j => ‖c j‖ *
      (Real.sqrt (2 * a j) * Real.exp (b * a j)) * Real.sqrt (delta j)) l (𝓝 0)) :
    TendstoUniformlyOn (fun j z => c j *
      (Zeta23.paperFT ((Icc (-a j) (a j)).indicator ((k j + w j) : ℝ → ℂ)) z -
        Zeta23.paperFT ((Icc (-a j) (a j)).indicator (k j : ℝ → ℂ)) z))
      (fun _ => 0) l {z : ℂ | |z.im| ≤ b} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [(tendsto_order.mp hsmall).2 eps heps] with j hj z hz
  simp only [dist_zero_left, norm_mul]
  have h := mul_le_mul_of_nonneg_left
    (paperFT_projective_strip_bound (ha j) (k j) (w j) (delta j) (he j) z hz)
    (norm_nonneg (c j))
  calc
    _ ≤ _ := h
    _ < eps := by simpa only [mul_assoc] using hj

/-- Actual operator-domain Rayleigh certificates plus the correct scaled
rate transfer a candidate Fourier limit to the projectively normalized
actual eigenvectors. Domains and window Hilbert spaces may vary with j.
The candidate convergence is explicit, so scaling c_j toward zero cannot
be substituted for a separately prescribed nonzero target limit. -/
theorem rayleigh_paperFT_uniform_limit
    {J : Type*} (l : Filter J) (a : J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (D : J → Type*) [∀ j, AddCommGroup (D j)] [∀ j, Module ℂ (D j)]
    (ι A : ∀ j, D j →ₗ[ℂ] WindowL2 (a j)) (k u : ∀ j, D j)
    (lower upper threshold lam : J → ℝ) (c : J → ℂ) (b : ℝ) (F : ℂ → ℂ)
    (hsym : ∀ j (x y : D j), ⟪ι j x, A j y⟫_ℂ = ⟪A j x, ι j y⟫_ℂ)
    (hk : ∀ j, ‖ι j (k j)‖ = 1) (hu : ∀ j, ι j (u j) ≠ 0)
    (hAu : ∀ j, A j (u j) = (lam j : ℂ) • ι j (u j))
    (hlower : ∀ j, lower j ≤ lam j) (hlam : ∀ j, lam j < threshold j)
    (hupper : ∀ j, (⟪ι j (k j), A j (k j)⟫_ℂ).re ≤ upper j)
    (hthreshold : ∀ j, upper j < threshold j)
    (hcoercive : ∀ j (v : D j), ⟪ι j (k j), ι j v⟫_ℂ = 0 →
      threshold j * ‖ι j v‖ ^ 2 ≤ (⟪ι j v, A j v⟫_ℂ).re)
    (hsmall : Tendsto (fun j => ‖c j‖ *
      (Real.sqrt (2 * a j) * Real.exp (b * a j)) *
        Real.sqrt ((upper j - lower j) / (threshold j - lower j))) l (𝓝 0))
    (hcandidate : TendstoUniformlyOn (fun j z => c j *
      Zeta23.paperFT ((Icc (-a j) (a j)).indicator (ι j (k j) : ℝ → ℂ)) z)
      F l {z : ℂ | |z.im| ≤ b}) :
    TendstoUniformlyOn (fun j z => c j * Zeta23.paperFT
      ((Icc (-a j) (a j)).indicator
        (((⟪ι j (k j), ι j (u j)⟫_ℂ)⁻¹ • ι j (u j)) : ℝ → ℂ)) z)
      F l {z : ℂ | |z.im| ≤ b} := by
  let w : ∀ j, WindowL2 (a j) := fun j =>
    ι j ((⟪ι j (k j), ι j (u j)⟫_ℂ)⁻¹ • u j - k j)
  have he (j : J) : ‖w j‖ ^ 2 ≤ (upper j - lower j) / (threshold j - lower j) := by
    exact (rayleigh_projective_enclosure (ι j) (A j) (k j) (u j)
      (lower j) (upper j) (threshold j) (lam j) (hsym j) (hk j) (hu j) (hAu j)
      (hlower j) (hlam j) (hupper j) (hthreshold j) (hcoercive j)).2.2.1
  have hsum (j : J) : ι j (k j) + w j =
      (⟪ι j (k j), ι j (u j)⟫_ℂ)⁻¹ • ι j (u j) := by
    dsimp only [w]
    rw [map_sub, map_smul]
    abel
  have herror := paperFT_projective_uniform_error l a ha (fun j => ι j (k j)) w
    (fun j => (upper j - lower j) / (threshold j - lower j)) c b he hsmall
  have hlimit := herror.add hcandidate
  simpa only [Pi.add_apply, hsum, mul_sub, sub_add_cancel, zero_add] using hlimit

#print axioms rayleigh_paperFT_uniform_limit

end D5.S3.Weil.FourierReadout.PaperFTWindowLimit
