/- GID: D5/S3/Quantum/Tomography/CayleyHadamardDifferential
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/CayleyHadamardDifferential
   mirror-E: none(waiver:analytic-certificate-bridge)
   anchors: []
   digest: Derive the actual signed-Cayley Hadamard residual differential and its balanced scalar enclosure, without a supplied Jacobian-correctness premise. -/

import D5.S3.Quantum.Tomography.HadamardResidualConservation
import Mathlib.Analysis.Calculus.Deriv.Inv

/- Reuse audit: HadamardResidualConservation owns the actual zero-sum residual
   identity and balanced box dual. CayleyCoverAnalysis owns compact signed
   charts; SublevelRowEnclosure owns the scalar mean-value estimate. We use
   Mathlib's derivative rules and that same scalar mean-value theorem. All
   chart abbreviations below are private spelling aids. No second public
   phase, interval, root, Hadamard, or context carrier is introduced.

   The six-coordinate path includes the verifier's five-coordinate chart by
   taking s(0)=1 and m(0)=v(0)=0. The statements do not claim that finite
   interval endpoints or a traversal tree have already been kernel checked.
-/

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.CayleyHadamardDifferential

open Matrix
open D5.S3.Quantum.Tomography.HadamardResidualConservation

private abbrev phase (s x : ℝ) : ℂ :=
  ⟨s * ((1 - x ^ 2) / (1 + x ^ 2)), s * (2 * x / (1 + x ^ 2))⟩

private abbrev velocity (s x v : ℝ) : ℂ :=
  ⟨(-4 * s * x * v) / (1 + x ^ 2) ^ 2,
    (2 * s * (1 - x ^ 2) * v) / (1 + x ^ 2) ^ 2⟩

private theorem phase_component_derivatives (s m v t : ℝ) :
    HasDerivAt (fun q ↦ (phase s (m + q * v)).re)
        (velocity s (m + t * v) v).re t ∧
      HasDerivAt (fun q ↦ (phase s (m + q * v)).im)
        (velocity s (m + t * v) v).im t := by
  let x : ℝ → ℝ := fun q ↦ m + q * v
  have hx : HasDerivAt x v t := by
    simpa [x] using ((hasDerivAt_id t).mul_const v).const_add m
  have hx2 := hx.mul hx
  have hden := hx2.const_add 1
  have hden0 : 1 + x t * x t ≠ 0 := by
    nlinarith [sq_nonneg (x t)]
  have hre := (((hasDerivAt_const t (1 : ℝ)).sub hx2).div hden hden0).const_mul s
  have him := ((hx.const_mul 2).div hden hden0).const_mul s
  constructor
  · convert! hre using 1 <;> (try funext q) <;>
      simp only [phase, velocity, x, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply] <;> ring
  · convert! him using 1 <;> (try funext q) <;>
      simp only [phase, velocity, x, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.div_apply] <;> ring

private theorem phase_normSq (s x : ℝ) (hs : s ^ 2 = 1) :
    Complex.normSq (phase s x) = 1 := by
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  calc
    Complex.normSq (phase s x) = s ^ 2 := by
      simp only [phase, Complex.normSq_apply]
      field_simp [hd]
      <;> ring
    _ = 1 := hs

/-- Exact directional derivative of the actual six-outcome residual along a
signed-Cayley segment. There is no Jacobian oracle in the hypotheses.

The sign parameters may be arbitrary real numbers for differentiability;
squared signs equal to one are imposed only by the enclosure consumer. -/
theorem signed_cayley_hadamard_residual_hasDerivAt
    (H : Matrix (Fin 6) (Fin 6) ℂ)
    (s m v : Fin 6 → ℝ) (a : Fin 6) (t : ℝ) :
    let u : ℝ → Fin 6 → ℂ := fun q i ↦
      ⟨s i * ((1 - (m i + q * v i) ^ 2) / (1 + (m i + q * v i) ^ 2)),
        s i * (2 * (m i + q * v i) / (1 + (m i + q * v i) ^ 2))⟩
    let du : Fin 6 → ℂ := fun i ↦
      ⟨(-4 * s i * (m i + t * v i) * v i) / (1 + (m i + t * v i) ^ 2) ^ 2,
        (2 * s i * (1 - (m i + t * v i) ^ 2) * v i) /
          (1 + (m i + t * v i) ^ 2) ^ 2⟩
    HasDerivAt (fun q ↦ Complex.normSq ((Hᴴ *ᵥ u q) a) - 6)
      (2 * (((Hᴴ *ᵥ u t) a).re * ((Hᴴ *ᵥ du) a).re +
        ((Hᴴ *ᵥ u t) a).im * ((Hᴴ *ᵥ du) a).im)) t := by
  let u : ℝ → Fin 6 → ℂ := fun q i ↦ phase (s i) (m i + q * v i)
  let du : Fin 6 → ℂ := fun i ↦ velocity (s i) (m i + t * v i) (v i)
  have hr : HasDerivAt (fun q ↦ ((Hᴴ *ᵥ u q) a).re) ((Hᴴ *ᵥ du) a).re t := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      (((phase_component_derivatives (s i) (m i) (v i) t).1).const_mul (H i a).re).add
        (((phase_component_derivatives (s i) (m i) (v i) t).2).const_mul (H i a).im))
    simpa [u, du, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.star_def, sub_eq_add_neg] using h
  have hi : HasDerivAt (fun q ↦ ((Hᴴ *ᵥ u q) a).im) ((Hᴴ *ᵥ du) a).im t := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      (((phase_component_derivatives (s i) (m i) (v i) t).2).const_mul (H i a).re).sub
        (((phase_component_derivatives (s i) (m i) (v i) t).1).const_mul (H i a).im))
    simpa [u, du, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Complex.mul_im, Complex.star_def, sub_eq_add_neg] using h
  change HasDerivAt (fun q ↦ Complex.normSq ((Hᴴ *ᵥ u q) a) - 6)
    (2 * (((Hᴴ *ᵥ u t) a).re * ((Hᴴ *ᵥ du) a).re +
      ((Hᴴ *ᵥ u t) a).im * ((Hᴴ *ᵥ du) a).im)) t
  convert! ((hr.mul hr).add (hi.mul hi)).sub_const 6 using 1
  ring

/-- Actual balanced sublevel row enclosure for a signed-Cayley path. The
explicit derivative formula is proved above, rather than required as input.
Only the local numerical enclosure of that formula remains to be supplied.
Both endpoints and the entire connecting segment are included.

This matches the real part of the verifier's complex products before squaring.
The full six residuals satisfy conservation because H H*=6I and the signed
Cayley coordinates have unit modulus. -/
theorem signed_cayley_balanced_sublevel_row_enclosure
    (H : Matrix (Fin 6) (Fin 6) ℂ)
    (s m v c lo hi : Fin 6 → ℝ) (k : Fin 6)
    (radius lambdalo lambdahi : ℝ)
    (hGram : H * Hᴴ = (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ))
    (hs : ∀ i, s i ^ 2 = 1) :
    let u : ℝ → Fin 6 → ℂ := fun q i ↦
      ⟨s i * ((1 - (m i + q * v i) ^ 2) / (1 + (m i + q * v i) ^ 2)),
        s i * (2 * (m i + q * v i) / (1 + (m i + q * v i) ^ 2))⟩
    let du : ℝ → Fin 6 → ℂ := fun q i ↦
      ⟨(-4 * s i * (m i + q * v i) * v i) / (1 + (m i + q * v i) ^ 2) ^ 2,
        (2 * s i * (1 - (m i + q * v i) ^ 2) * v i) /
          (1 + (m i + q * v i) ^ 2) ^ 2⟩
    let f : ℝ → Fin 6 → ℝ := fun q a ↦ Complex.normSq ((Hᴴ *ᵥ u q) a) - 6
    let df : ℝ → Fin 6 → ℝ := fun q a ↦
      2 * (((Hᴴ *ᵥ u q) a).re * ((Hᴴ *ᵥ du q) a).re +
        ((Hᴴ *ᵥ u q) a).im * ((Hᴴ *ᵥ du q) a).im)
    (∀ q ∈ Set.Icc (0 : ℝ) 1, |v k - ∑ a, c a * df q a| ≤ radius) →
    (∀ a, lo a ≤ f 1 a) → (∀ a, f 1 a ≤ hi a) →
    m k - (∑ a, c a * f 0 a) - radius +
        (∑ a, min ((c a - lambdalo) * lo a) ((c a - lambdalo) * hi a)) ≤ m k + v k ∧
      m k + v k ≤ m k - (∑ a, c a * f 0 a) + radius +
        (∑ a, max ((c a - lambdahi) * lo a) ((c a - lambdahi) * hi a)) := by
  dsimp only
  intro hdirectional hlo hhi
  let u : ℝ → Fin 6 → ℂ := fun q i ↦ phase (s i) (m i + q * v i)
  let du : ℝ → Fin 6 → ℂ := fun q i ↦ velocity (s i) (m i + q * v i) (v i)
  let f : ℝ → Fin 6 → ℝ := fun q a ↦ Complex.normSq ((Hᴴ *ᵥ u q) a) - 6
  let df : ℝ → Fin 6 → ℝ := fun q a ↦
    2 * (((Hᴴ *ᵥ u q) a).re * ((Hᴴ *ᵥ du q) a).re +
      ((Hᴴ *ᵥ u q) a).im * ((Hᴴ *ᵥ du q) a).im)
  let g : ℝ → ℝ := fun q ↦ m k + q * v k - ∑ a, c a * f q a
  have hg (q : ℝ) : HasDerivAt g (v k - ∑ a, c a * df q a) q := by
    have hp : HasDerivAt (fun t : ℝ ↦ m k + t * v k) (v k) q := by
      simpa using ((hasDerivAt_id q).mul_const (v k)).const_add (m k)
    have hf := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ ↦
      (signed_cayley_hadamard_residual_hasDerivAt H s m v a q).const_mul (c a))
    exact hp.sub hf
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q _ ↦ (hg q).hasDerivWithinAt)
    (fun q hq ↦ (show ‖v k - ∑ a, c a * df q a‖ ≤ radius from
      by simpa only [Real.norm_eq_abs] using hdirectional q hq))
    (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  have hrem : |g 1 - g 0| ≤ radius := by
    simpa only [sub_zero, norm_one, mul_one, Real.norm_eq_abs] using hmv
  have hread := hadamard_residual_box_dual H (u 1) hGram
    (fun i ↦ phase_normSq (s i) (m i + 1 * v i) (hs i))
    c lo hi lambdalo lambdahi hlo hhi
  have hrlo := (abs_le.mp hrem).1
  have hrhi := (abs_le.mp hrem).2
  change (∑ a, min ((c a - lambdalo) * lo a) ((c a - lambdalo) * hi a)) ≤
      (∑ a, c a * f 1 a) ∧
      (∑ a, c a * f 1 a) ≤
        (∑ a, max ((c a - lambdahi) * lo a) ((c a - lambdahi) * hi a)) at hread
  change m k - (∑ a, c a * f 0 a) - radius + _ ≤ m k + v k ∧
    m k + v k ≤ m k - (∑ a, c a * f 0 a) + radius + _
  dsimp [g] at hrlo hrhi
  simp only [one_mul, zero_mul, add_zero] at hrlo hrhi
  constructor <;> linarith [hread.1, hread.2]

#print axioms signed_cayley_hadamard_residual_hasDerivAt
#print axioms signed_cayley_balanced_sublevel_row_enclosure

end D5.S3.Quantum.Tomography.CayleyHadamardDifferential
