/- GID: D5/S3/Quantum/CotfasDVGS
   generality: I
   mirror-B: D5/B/S3/Quantum/CotfasDVGS
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The covariance uncertainty condition makes the mixed discrete Gaussian a density. -/
/-
proof_shape: result: content
escape_witness: none
admission_basis: open-problem-resolution (#18946; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19812
Direct frozen dependencies:
D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.thermalCov._proof_1
  sha256:83f1ceeb429672fc69ed7b05221717bed36bfc3d20bfbfaf29d42aff28260770
D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.physical_data
  sha256:5cca2636075e308d2c7601cbf4eec201deeff36ae84f87cba8d1efbc1a1c4ec9
D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
  sha256:410391e348afb0d9876bdf2548ca1782f14191e2ac259dd3c3d81d1876de06a4
D5/S3/Weil/Probability/FiniteGaussianSchoenberg.gram_gaussian_posSemidef
  sha256:e83ee5619019d4fc81d7390a8b36152737f3dda0b497486e0e5fc9c97d9a1c91
D5/S3/Quantum/Information/SLDSpectralEnergy.IsDensity
  sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
The centered index type and density conjunction occur literally; centered reduction uses ZMod.valMinAbs.
The proof uses the existing density and covariance predicates; the source uncertainty matrix occurs literally in claim.
No finite computational certificate is introduced; utility is none.
kernelLatticeEquiv | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity
strongWave | proof_shape: bind-only | escape_witness: none | consumers: kernel_residual_posSemidef, strongWave_factorization, periodized_kernel_zero_diagonal_pos, strongWave_summable, strongWave_zero_sum_ne_zero, strongWave_norm
parityLatticeMap | proof_shape: bind-only | escape_witness: none | consumers: parityLatticeMap_injective, theta_duplication
halfLatticeEquiv | proof_shape: bind-only | escape_witness: none | consumers: entry_half_lattice
halfLatticeMap | proof_shape: bind-only | escape_witness: none | consumers: halfLatticeMap_injective, halfLatticeMap_surjective, halfLatticeEquiv, midpoint_exists
wave | proof_shape: bind-only | escape_witness: none | consumers: kernel_residual_posSemidef, strongWave_factorization, kernel_posSemidef, kernel_factorization
kernel | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity, kernel_residual_posSemidef, kernel_norm_bound, finite_periodization_posSemidef, periodization_posSemidef, periodized_kernel_zero_diagonal_pos, result, kernel_posSemidef, kernel_lattice_summable, kernel_fourier_slice, kernel_factorization
claim | proof_shape: bind-only | escape_witness: none | consumers: result
rhoTilde | proof_shape: bind-only | escape_witness: none | consumers: result, claim, rhoTilde_scaling
unnormalized | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity, unnormalized_entry_midpoint, unnormalized_scaling, entry_half_lattice, rhoTilde, result, rhoTilde_scaling
wSum | proof_shape: bind-only | escape_witness: none | consumers: unnormalized, wSum_scaling, unnormalized_entry_midpoint, unnormalized_scaling, entry_half_lattice
parity | proof_shape: bind-only | escape_witness: none | consumers: unnormalized, unnormalized_entry_midpoint, unnormalized_scaling
W | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity, signed_W_lattice_summable, W_nonnegative, wSum_scaling, W_gaussian_bound, wSum, entry_half_lattice, W_scaling, W_coordinates, kernel_fourier_slice
W_scaling | proof_shape: bind-only | escape_witness: none | consumers: wSum_scaling
wSum_scaling | proof_shape: bind-only | escape_witness: none | consumers: unnormalized_scaling
unnormalized_scaling | proof_shape: bind-only | escape_witness: none | consumers: rhoTilde_scaling
rhoTilde_scaling | proof_shape: bind-only | escape_witness: none | consumers: result
uncertainty_det_bound | proof_shape: bind-only | escape_witness: none | consumers: result
normalization_isDensity | proof_shape: bind-only | escape_witness: none | consumers: result
kernel_factorization | proof_shape: bind-only | escape_witness: none | consumers: kernel_residual_posSemidef, kernel_posSemidef
lambda_nonnegative | proof_shape: bind-only | escape_witness: none | consumers: kernel_residual_posSemidef, kernel_posSemidef
finite_gaussian_posSemidef | proof_shape: bind-only | escape_witness: none | consumers: kernel_posSemidef, finite_gaussian_residual_posSemidef
kernel_posSemidef | proof_shape: bind-only | escape_witness: none | consumers: finite_periodization_posSemidef
sum_subtype_pair | proof_shape: bind-only | escape_witness: none | consumers: finite_periodization_posSemidef, lattice_sum_nonnegative
finite_periodization_posSemidef | proof_shape: bind-only | escape_witness: none | consumers: periodization_posSemidef
periodization_posSemidef | proof_shape: bind-only | escape_witness: none | consumers: result
gaussian_shifted_summable | proof_shape: bind-only | escape_witness: none | consumers: signed_W_lattice_summable, strongWave_summable, kernel_lattice_summable
kernel_norm_bound | proof_shape: bind-only | escape_witness: none | consumers: kernel_lattice_summable
kernel_lattice_summable | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity, periodized_kernel_zero_diagonal_pos, result
centered_eq_of_dvd | proof_shape: bind-only | escape_witness: none | consumers: halfLatticeMap_injective, midpoint_unique
halfLatticeMap_injective | proof_shape: bind-only | escape_witness: none | consumers: halfLatticeEquiv
halfLatticeMap_surjective | proof_shape: bind-only | escape_witness: none | consumers: halfLatticeEquiv, midpoint_exists
inverse_quadratic_coordinates | proof_shape: bind-only | escape_witness: none | consumers: W_coordinates, inverse_quadratic_lower_bound
W_coordinates | proof_shape: bind-only | escape_witness: none | consumers: kernel_fourier_slice
inverse_quadratic_lower_bound | proof_shape: bind-only | escape_witness: none | consumers: W_gaussian_bound
half_lattice_poisson | proof_shape: bind-only | escape_witness: none | consumers: kernel_fourier_slice
theta_series_summable | proof_shape: bind-only | escape_witness: none | consumers: theta_duplication
exp_pi_int | proof_shape: bind-only | escape_witness: none | consumers: theta_term_shift, phase_half_lattice
neg_one_int_square | proof_shape: bind-only | escape_witness: none | consumers: theta_term_shift
theta_term_shift | proof_shape: bind-only | escape_witness: none | consumers: theta_duplication
parityLatticeMap_injective | proof_shape: bind-only | escape_witness: none | consumers: theta_duplication
theta_duplication | proof_shape: bind-only | escape_witness: none | consumers: theta_nonzero
theta_nonzero_small | proof_shape: bind-only | escape_witness: none | consumers: theta_nonzero
theta_nonzero | proof_shape: content | escape_witness: none | consumers: strongWave_zero_sum_ne_zero
W_nonnegative | proof_shape: bind-only | escape_witness: none | consumers: signed_W_lattice_summable
W_gaussian_bound | proof_shape: bind-only | escape_witness: none | consumers: signed_W_lattice_summable
signed_W_lattice_summable | proof_shape: bind-only | escape_witness: none | consumers: entry_half_lattice
midpoint_exists | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity
valMinAbs_sub_dvd | proof_shape: bind-only | escape_witness: none | consumers: halfLatticeMap_surjective, midpoint_unique
parity_support | proof_shape: bind-only | escape_witness: none | consumers: unnormalized_entry_midpoint
midpoint_unique | proof_shape: bind-only | escape_witness: none | consumers: unnormalized_entry_midpoint
gaussian_fourier_term | proof_shape: bind-only | escape_witness: none | consumers: kernel_fourier_slice
kernel_fourier_slice | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity
finite_gaussian_residual_posSemidef | proof_shape: bind-only | escape_witness: none | consumers: kernel_residual_posSemidef
strongWave_factorization | proof_shape: bind-only | escape_witness: none | consumers: kernel_residual_posSemidef
kernel_residual_posSemidef | proof_shape: bind-only | escape_witness: none | consumers: periodized_kernel_zero_diagonal_pos
strongWave_norm | proof_shape: bind-only | escape_witness: none | consumers: strongWave_summable
strongWave_summable | proof_shape: bind-only | escape_witness: none | consumers: periodized_kernel_zero_diagonal_pos
strongWave_zero_sum_ne_zero | proof_shape: content | escape_witness: none | consumers: periodized_kernel_zero_diagonal_pos
lattice_sum_nonnegative | proof_shape: bind-only | escape_witness: none | consumers: periodized_kernel_zero_diagonal_pos
periodized_kernel_zero_diagonal_pos | proof_shape: content | escape_witness: none | consumers: result
phase_half_lattice | proof_shape: bind-only | escape_witness: none | consumers: entry_half_lattice
unnormalized_entry_midpoint | proof_shape: bind-only | escape_witness: none | consumers: entry_half_lattice
entry_half_lattice | proof_shape: bind-only | escape_witness: none | consumers: kernel_identity
kernel_identity | proof_shape: bind-only | escape_witness: none | consumers: result
-/
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation
import D5.S3.Weil.Probability.FiniteGaussianSchoenberg
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
set_option autoImplicit false
namespace D5.S3.Quantum.CotfasDVGS
open Matrix
open scoped ComplexOrder
noncomputable def W (h : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℝ) (q p : ℝ) : ℝ :=
  2 / (h * Real.sqrt σ.det) * Real.exp (-(2 * Real.pi / h) * (![q, p] ⬝ᵥ (σ⁻¹ *ᵥ ![q, p])))
noncomputable def parity (s : ℕ) (n k : (Finset.Icc (-(s : ℤ)) (s : ℤ))) : Matrix ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ℂ :=
  fun m j => if (j : ℤ) = ((2 * (n : ℤ) - m : ℤ) : ZMod (2*s+1)).valMinAbs then
    Complex.exp (4 * Real.pi * Complex.I * (k : ℤ) * ((m : ℤ) - n) / (2 * s + 1)) else 0
noncomputable def wSum (s : ℕ) (h : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℝ) (n k : (Finset.Icc (-(s : ℤ)) (s : ℤ))) : ℝ :=
  ∑' αβ : ℤ × ℤ, (-1 : ℝ) ^ (αβ.1 * αβ.2) *
    W h σ (((n : ℤ) + αβ.1 * (2 * s + 1) / 2) * Real.sqrt (h / (2 * s + 1)))
      (((k : ℤ) + αβ.2 * (2 * s + 1) / 2) * Real.sqrt (h / (2 * s + 1)))
noncomputable def unnormalized (s : ℕ) (h : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ℂ :=
  ∑ n : (Finset.Icc (-(s : ℤ)) (s : ℤ)), ∑ k : (Finset.Icc (-(s : ℤ)) (s : ℤ)), (wSum s h σ n k : ℂ) • parity s n k
noncomputable def rhoTilde (s : ℕ) (h : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ℂ :=
  ((unnormalized s h σ).trace)⁻¹ • unnormalized s h σ
def claim : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ h : ℝ, 0 < h → ∀ σ : Matrix (Fin 2) (Fin 2) ℝ,
    σ.PosDef → (σ.map (fun x : ℝ => (x : ℂ)) + Complex.I • !![(0 : ℂ), 1; -1, 0]).PosSemidef → ((rhoTilde s h σ).PosSemidef ∧ (rhoTilde s h σ).trace = 1)
end D5.S3.Quantum.CotfasDVGS
namespace D5.S3.Quantum.CotfasDVGS
open Matrix Filter Topology
open scoped ComplexOrder
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
private theorem W_scaling (h d : ℝ) (hh : 0 < h) (hd : 0 < d) (σ : Matrix (Fin 2) (Fin 2) ℝ) (q p : ℝ) : W h σ (q * Real.sqrt (h / d)) (p * Real.sqrt (h / d)) = (d / h) * W d σ q p := by
  have ht : (Real.sqrt (h / d)) ^ 2 = h / d := Real.sq_sqrt (le_of_lt (div_pos hh hd))
  have hv : ![q * Real.sqrt (h / d), p * Real.sqrt (h / d)] =
      Real.sqrt (h / d) • ![q, p] := by
    ext i
    fin_cases i <;> simp [mul_comm]
  have hQ : (![q * Real.sqrt (h / d), p * Real.sqrt (h / d)] ⬝ᵥ
      (σ⁻¹ *ᵥ ![q * Real.sqrt (h / d), p * Real.sqrt (h / d)])) =
      (h / d) * (![q, p] ⬝ᵥ (σ⁻¹ *ᵥ ![q, p])) := by
    rw [hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← pow_two, ht]
  unfold W
  rw [hQ]
  have he : -(2 * Real.pi / h) * (h / d * (![q, p] ⬝ᵥ (σ⁻¹ *ᵥ ![q, p]))) =
      -(2 * Real.pi / d) * (![q, p] ⬝ᵥ (σ⁻¹ *ᵥ ![q, p])) := by
    field_simp
  rw [he]
  by_cases hD : Real.sqrt σ.det = 0
  · simp [hD]
  · field_simp
private theorem wSum_scaling (s : ℕ) (h : ℝ) (hh : 0 < h) (σ : Matrix (Fin 2) (Fin 2) ℝ) (n k : (Finset.Icc (-(s : ℤ)) (s : ℤ))) : wSum s h σ n k = ((2 * s + 1 : ℝ) / h) * wSum s (2 * s + 1) σ n k := by
  have hd : (0 : ℝ) < 2 * s + 1 := by positivity
  simp only [wSum, div_self (ne_of_gt hd), Real.sqrt_one, mul_one]
  simp_rw [W_scaling h (2 * s + 1) hh hd]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  ring
private theorem unnormalized_scaling (s : ℕ) (h : ℝ) (hh : 0 < h) (σ : Matrix (Fin 2) (Fin 2) ℝ) : unnormalized s h σ = (((2 * s + 1 : ℝ) / h : ℝ) : ℂ) • unnormalized s (2 * s + 1) σ := by
  unfold unnormalized
  simp_rw [wSum_scaling s h hh, Complex.ofReal_mul, mul_smul]
  simp only [Finset.smul_sum]
private theorem rhoTilde_scaling (s : ℕ) (h : ℝ) (hh : 0 < h) (σ : Matrix (Fin 2) (Fin 2) ℝ) : rhoTilde s h σ = rhoTilde s (2*s+1) σ := by
  have hd : (0 : ℝ) < 2*s+1 := by positivity
  have hc : (((2*s+1:ℝ)/h : ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero hd.ne' hh.ne')
  unfold rhoTilde
  rw [unnormalized_scaling s h hh, Matrix.trace_smul]
  simp only [smul_eq_mul, smul_smul, _root_.mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
private theorem uncertainty_det_bound (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (hU : (σ.map (fun x : ℝ => (x : ℂ)) + Complex.I • !![(0 : ℂ), 1; -1, 0]).PosSemidef) : 1 ≤ σ.det := by
  have hm : D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
      (m := 1) σ := by
    constructor
    · exact hσ.isHermitian.isSymm
    · convert hU using 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.J, Matrix.fromBlocks, Matrix.submatrix, Fin.divNat,
          Matrix.one_apply, sub_eq_add_neg]
  exact (D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.physical_data σ hm).2
theorem normalization_isDensity {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (ht : A.trace ≠ 0) : D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity (A.trace⁻¹ • A) := by
  constructor
  · exact hA.smul (inv_nonneg.mpr hA.trace_nonneg)
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ ht]
private noncomputable def kernel (d a c D x y : ℝ) : ℂ :=
  (Real.sqrt (2 / (d * a)) : ℂ) * Complex.exp
    ((-Real.pi * ((x + y)^2 + D * (x - y)^2) / (2 * d * a) : ℝ) +
      Complex.I * (Real.pi * c * (x^2 - y^2) / (d * a) : ℝ))
private noncomputable def wave (d a c x : ℝ) : ℂ :=
  (Real.sqrt (Real.sqrt (2 / (d * a))) : ℂ) *
    Complex.exp ((-Real.pi * x^2 / (d * a) : ℝ) +
      Complex.I * (Real.pi * c * x^2 / (d * a) : ℝ))
private theorem kernel_factorization (d a c D x y : ℝ) : kernel d a c D x y = wave d a c x * star (wave d a c y) * (Real.exp (-(Real.pi * (D - 1) / (2 * d * a)) * (x-y)^2) : ℂ) := by
  have hroot : (Real.sqrt (Real.sqrt (2 / (d * a)))) ^ 2 =
      Real.sqrt (2 / (d * a)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hE : ((-Real.pi * ((x+y)^2+D*(x-y)^2)/(2*d*a) : ℝ) : ℂ) +
      Complex.I * (Real.pi*c*(x^2-y^2)/(d*a) : ℝ) =
      (((-Real.pi*x^2/(d*a) : ℝ) : ℂ) + Complex.I*(Real.pi*c*x^2/(d*a) : ℝ)) +
      (((-Real.pi*y^2/(d*a) : ℝ) : ℂ) - Complex.I*(Real.pi*c*y^2/(d*a) : ℝ)) +
      ((-(Real.pi*(D-1)/(2*d*a))*(x-y)^2 : ℝ) : ℂ) := by
    push_cast
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  unfold kernel wave
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
    map_add, map_mul, Complex.conj_I, Complex.ofReal_exp]
  rw [hE, Complex.exp_add, Complex.exp_add]
  have hr : (Real.sqrt (2/(d*a)) : ℂ) =
      (Real.sqrt (Real.sqrt (2/(d*a))) : ℂ)^2 := by exact_mod_cast hroot.symm
  rw [hr]
  have he : ((-Real.pi * y^2 / (d*a) : ℝ) : ℂ) -
      Complex.I * (Real.pi*c*y^2/(d*a) : ℝ) =
      ((-Real.pi * y^2 / (d*a) : ℝ) : ℂ) +
      -Complex.I * (Real.pi*c*y^2/(d*a) : ℝ) := by ring
  rw [he]
  ring
private theorem lambda_nonnegative (d a D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : 0 ≤ Real.pi * (D - 1) / (2 * d * a) := by
  exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hD)) (by positivity)
private theorem finite_gaussian_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) : Matrix.PosSemidef (fun i j => (Real.exp (-t * (p i - p j)^2) : ℂ)) := by
  have hA : Matrix.PosSemidef (fun i j => p i * p j) := by
    exact Eq.mp (congrArg (fun A : Matrix ι ι ℝ => A.PosSemidef)
      (show Matrix.vecMulVec p (star p) = (fun i j => p i * p j) from
        Matrix.ext_col_iff.mpr (congrFun rfl)))
      (Matrix.posSemidef_vecMulVec_self_star p)
  have h := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.gram_gaussian_posSemidef
    (fun i j => p i * p j) hA t ht
  have he : (fun i j => (Real.exp (-t*(p i-p j)^2) : ℂ)) =
      (fun i j => (Real.exp (-t*(p i*p i+p j*p j-2*(p i*p j))) : ℂ)) := by
    ext i j
    congr 2
    ring
  rw [he]
  exact h
private theorem kernel_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (d a c D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : Matrix.PosSemidef (fun i j => kernel d a c D (p i) (p j)) := by
  have hG := finite_gaussian_posSemidef p (Real.pi * (D-1)/(2*d*a))
    (lambda_nonnegative d a D hd ha hD)
  have hW := Matrix.posSemidef_vecMulVec_self_star (fun i => wave d a c (p i))
  have h := hW.hadamard hG
  have he : (fun i j => kernel d a c D (p i) (p j)) =
      Matrix.vecMulVec (fun i => wave d a c (p i)) (star (fun i => wave d a c (p i))) ⊙
      (fun i j => (Real.exp (-(Real.pi*(D-1)/(2*d*a))*(p i-p j)^2) : ℂ)) := by
    ext i j
    change kernel d a c D (p i) (p j) = wave d a c (p i) * star (wave d a c (p j)) * _
    exact kernel_factorization d a c D (p i) (p j)
  rw [he]
  exact h
private theorem sum_subtype_pair (R : Finset ℤ) (f : ℤ → ℤ → ℂ) : (∑ r : R, ∑ l : R, f r l) = ∑ r ∈ R, ∑ l ∈ R, f r l := by
  calc
    _ = ∑ r ∈ R, ∑ l : R, f r l := Finset.sum_coe_sort R (fun r : ℤ => ∑ l : R, f r l)
    _ = _ := Finset.sum_congr rfl (fun r hr => Finset.sum_coe_sort R (f r))
private theorem finite_periodization_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (d a c D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) (R : Finset ℤ) : Matrix.PosSemidef (fun i j => ∑ r ∈ R, ∑ l ∈ R, kernel d a c D (p i + d * r) (p j + d * l)) := by
  let C : Matrix (ι × R) ι ℂ := fun z j => if z.1 = j then 1 else 0
  let B : Matrix (ι × R) (ι × R) ℂ := fun z w =>
    kernel d a c D (p z.1+d*z.2.1) (p w.1+d*w.2.1)
  have hK : B.PosSemidef := kernel_posSemidef (fun z : ι × R => p z.1 + d * z.2.1)
    d a c D hd ha hD
  have h := hK.conjTranspose_mul_mul_same C
  have he : (fun i j => ∑ r ∈ R, ∑ l ∈ R,
      kernel d a c D (p i+d*r) (p j+d*l)) =
      Cᴴ * B * C := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [C, B, Fintype.sum_prod_type, Finset.sum_attach]
    rw [Finset.sum_comm]
    exact (sum_subtype_pair R (fun l r : ℤ =>
      kernel d a c D (p i+d*r) (p j+d*l))).symm
  rw [he]
  exact h
private theorem periodization_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (d a c D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) (hs : ∀ i j, Summable (fun z : ℤ × ℤ => kernel d a c D (p i + d * z.1) (p j + d * z.2))) : Matrix.PosSemidef (fun i j => ∑' z : ℤ × ℤ,
      kernel d a c D (p i + d * z.1) (p j + d * z.2)) := by
  have hlim : Tendsto (fun R : Finset ℤ => fun i j => ∑ r ∈ R, ∑ l ∈ R,
      kernel d a c D (p i + d*r) (p j + d*l)) atTop
      (𝓝 (fun i j => ∑' z : ℤ × ℤ,
      kernel d a c D (p i + d*z.1) (p j + d*z.2))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (hs i j).hasSum.comp
      (Filter.tendsto_finsetProd_atTop.comp Filter.tendsto_atTop_diagonal)
    simpa only [Function.comp_def, Finset.sum_product] using h
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hlim
    (Filter.Eventually.of_forall (finite_periodization_posSemidef p d a c D hd ha hD))
private theorem gaussian_shifted_summable (t d x : ℝ) (ht : 0 < t) (hd : d ≠ 0) : Summable (fun n : ℤ => Real.exp (-t * (x + d * n)^2)) := by
  have hT : 0 < t * d^2 / Real.pi := div_pos (mul_pos ht (sq_pos_of_ne_zero hd)) Real.pi_pos
  convert HurwitzKernelBounds.summable_f_int 0 (x/d) hT using 1
  ext n
  dsimp only [HurwitzKernelBounds.f_int]
  simp only [pow_zero, one_mul]
  congr 1
  field_simp [Real.pi_ne_zero, hd]
  <;> ring
private theorem kernel_norm_bound (d a c D x y : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : ‖kernel d a c D x y‖ ≤ Real.sqrt (2/(d*a)) * (Real.exp (-(Real.pi/(d*a))*x^2) * Real.exp (-(Real.pi/(d*a))*y^2)) := by
  have hpoly : 2*(x^2+y^2) ≤ (x+y)^2+D*(x-y)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sq_nonneg (x-y))]
  have he : -Real.pi*((x+y)^2+D*(x-y)^2)/(2*d*a) ≤
      -(Real.pi/(d*a))*(x^2+y^2) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*d*a)).mpr
    have hc : -(Real.pi/(d*a))*(x^2+y^2)*(2*d*a) =
        -Real.pi*(2*(x^2+y^2)) := by field_simp <;> ring
    rw [hc]
    exact mul_le_mul_of_nonpos_left hpoly (by linarith [Real.pi_pos])
  unfold kernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert he using 1 <;> ring
private theorem kernel_lattice_summable (d a c D x y : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : Summable (fun z : ℤ × ℤ => kernel d a c D (x+d*z.1) (y+d*z.2)) := by
  have ht : 0 < Real.pi/(d*a) := div_pos Real.pi_pos (mul_pos hd ha)
  have hs := (gaussian_shifted_summable (Real.pi/(d*a)) d x ht hd.ne').mul_of_nonneg
    (gaussian_shifted_summable (Real.pi/(d*a)) d y ht hd.ne')
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  exact (hs.mul_left (Real.sqrt (2/(d*a)))).of_norm_bounded
    (fun z => kernel_norm_bound d a c D (x+d*z.1) (y+d*z.2) hd ha hD)
private theorem centered_eq_of_dvd (s : ℕ) (k l : (Finset.Icc (-(s : ℤ)) (s : ℤ))) (h : (2*(s:ℤ)+1) ∣ (l:ℤ)-(k:ℤ)) : k = l := by
  have hk := k.property
  have hl := l.property
  simp only [Finset.mem_Icc] at hk hl
  have hm := (Int.modEq_iff_dvd.mpr h).add_right (s:ℤ)
  change ((k:ℤ)+(s:ℤ)) % (2*(s:ℤ)+1) =
    ((l:ℤ)+(s:ℤ)) % (2*(s:ℤ)+1) at hm
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hm
  exact Subtype.ext (by omega)
private def halfLatticeMap (s : ℕ) (z : (Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ) : ℤ :=
  2*(z.1:ℤ)+(2*(s:ℤ)+1)*z.2
private theorem halfLatticeMap_injective (s : ℕ) : Function.Injective (halfLatticeMap s) := by
  intro z w h
  have hd : 2*(s:ℤ)+1 ≠ 0 := by omega
  have hc : IsCoprime (2*(s:ℤ)+1) 2 := ⟨1,-(s:ℤ),by ring⟩
  have hdiv : (2*(s:ℤ)+1) ∣ 2*((w.1:ℤ)-(z.1:ℤ)) := by
    refine ⟨z.2-w.2, ?_⟩
    unfold halfLatticeMap at h
    nlinarith only [h]
  have hk : z.1 = w.1 := centered_eq_of_dvd s z.1 w.1 (hc.dvd_of_dvd_mul_left hdiv)
  have hb : z.2 = w.2 := by
    unfold halfLatticeMap at h
    rw [hk] at h
    exact mul_left_cancel₀ hd (by linarith only [h])
  exact Prod.ext hk hb
private theorem valMinAbs_sub_dvd (s : ℕ) (x : ℤ) : (2*(s:ℤ)+1) ∣ (x : ZMod (2*s+1)).valMinAbs-x := by
  have hcast : (2*(s:ℤ)+1) = ((2*s+1:ℕ):ℤ) := by omega
  rw [hcast]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub, ZMod.coe_valMinAbs, sub_self]
private theorem halfLatticeMap_surjective (s : ℕ) : Function.Surjective (halfLatticeMap s) := by
  intro t
  letI : NeZero (2*s+1) := ⟨by omega⟩
  let n : (Finset.Icc (-(s : ℤ)) (s : ℤ)) :=
    ⟨((((s:ℤ)+1)*t : ℤ) : ZMod (2*s+1)).valMinAbs, by
      have hb := ZMod.valMinAbs_mem_Ioc (((((s:ℤ)+1)*t : ℤ) : ZMod (2*s+1)))
      simp only [Finset.mem_Icc]
      simp only [Set.mem_Ioc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hb
      constructor <;> omega⟩
  obtain ⟨β,hβ⟩ := valMinAbs_sub_dvd s (((s:ℤ)+1)*t)
  refine ⟨(n,-(2*β+t)), ?_⟩
  dsimp only [halfLatticeMap, n, Prod.fst, Prod.snd]
  nlinarith only [hβ]
private noncomputable def halfLatticeEquiv (s : ℕ) : ((Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ) ≃ ℤ :=
  Equiv.ofBijective (halfLatticeMap s)
    ⟨halfLatticeMap_injective s, halfLatticeMap_surjective s⟩
private theorem inverse_quadratic_coordinates (σ : Matrix (Fin 2) (Fin 2) ℝ) (hs : σ.IsSymm) (q p : ℝ) : (![q,p] ⬝ᵥ (σ⁻¹ *ᵥ ![q,p])) = (σ 1 1*q^2 - 2*σ 0 1*q*p + σ 0 0*p^2)/σ.det := by
  have hsym : σ 1 0 = σ 0 1 := hs.apply 0 1
  simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym, div_eq_mul_inv]
  ring
private theorem W_coordinates (h : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℝ) (hs : σ.IsSymm) (q p : ℝ) : W h σ q p = 2/(h*Real.sqrt σ.det) * Real.exp (-(2*Real.pi/h)*((σ 1 1*q^2-2*σ 0 1*q*p+σ 0 0*p^2)/σ.det)) := by
  rw [W, inverse_quadratic_coordinates σ hs]
private theorem inverse_quadratic_lower_bound (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (q p : ℝ) : (q^2+p^2)/(σ 0 0+σ 1 1) ≤ (![q,p] ⬝ᵥ (σ⁻¹ *ᵥ ![q,p])) := by
  have ha := hσ.diag_pos (i := 0)
  have hb := hσ.diag_pos (i := 1)
  have hs : σ 1 0 = σ 0 1 := hσ.isHermitian.isSymm.apply 0 1
  rw [inverse_quadratic_coordinates σ hσ.isHermitian.isSymm]
  apply (div_le_div_iff₀ (add_pos ha hb) hσ.det_pos).mpr
  simp only [Matrix.det_fin_two, hs]
  nlinarith [sq_nonneg (σ 1 1*q-σ 0 1*p), sq_nonneg (σ 0 1*q-σ 0 0*p)]
private theorem half_lattice_poisson (d a c D q w : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 0 < D) : (∑' t : ℤ, Complex.exp (((-2*Real.pi/(d*D)*(a*((t:ℝ)/2)^2-2*c*q*((t:ℝ)/2)) : ℝ) : ℂ) + Complex.I*(Real.pi*(t:ℝ)*w : ℝ))) = 1 / (((a/(2*d*D) : ℝ) : ℂ) ^ (1/2 : ℂ)) *
        ∑' m : ℤ, Complex.exp (-Real.pi / ((a/(2*d*D) : ℝ) : ℂ) * ((m:ℂ)+Complex.I*((c*q/(d*D):ℝ)+Complex.I*(w/2:ℝ)))^2) := by
  have hA : (0 : ℝ) < (((a/(2*d*D):ℝ):ℂ)).re := by
    change 0 < a/(2*d*D)
    exact div_pos ha (by positivity : 0 < 2*d*D)
  convert Complex.tsum_exp_neg_quadratic hA
    (((c*q/(d*D):ℝ):ℂ)+Complex.I*(w/2:ℝ)) using 1
  apply tsum_congr
  intro t
  congr 1
  push_cast
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring
private theorem theta_series_summable (τ : ℂ) (hτ : 0 < τ.im) : Summable (fun n : ℤ => jacobiTheta₂_term n 0 τ) :=
  (hasSum_jacobiTheta₂_term 0 hτ).summable
private theorem exp_pi_int (n : ℤ) : Complex.exp (Real.pi * Complex.I * (n:ℂ)) = (-1:ℂ)^n := by
  rw [mul_comm _ (n:ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]
private theorem neg_one_int_square (n : ℤ) : (-1:ℂ)^(n^2) = (-1:ℂ)^n := by
  simp [neg_one_zpow_eq_ite, Int.even_pow]
private theorem theta_term_shift (τ : ℂ) (n : ℤ) : (jacobiTheta₂_term n 0 (τ+1)) = (((-1 : ℂ) ^ n)) * (jacobiTheta₂_term n 0 τ) := by
  simp only [jacobiTheta₂_term, mul_zero, zero_add]
  rw [mul_add, mul_one, Complex.exp_add]
  have he : Real.pi * Complex.I * (n:ℂ)^2 = Real.pi * Complex.I * ((n^2:ℤ):ℂ) := by
    norm_cast
  rw [he, exp_pi_int, neg_one_int_square, mul_comm]
private def parityLatticeMap (z : ℤ × ℤ) : ℤ × ℤ := (z.1+z.2,z.1-z.2)
private theorem parityLatticeMap_injective : Function.Injective parityLatticeMap := by
  intro z w h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp [parityLatticeMap] at h1 h2
  apply Prod.ext <;> omega
set_option maxHeartbeats 6000000 in
private theorem theta_duplication (τ : ℂ) (hτ : 0 < τ.im) : jacobiTheta τ * jacobiTheta (τ+1) = jacobiTheta (2*τ+1)^2 := by
  have hτ1 : 0 < (τ+1).im := by simpa using hτ
  have hτ2 : 0 < (2*τ+1).im := by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hτ)
  let f : ℤ × ℤ → ℂ := fun z => (jacobiTheta₂_term z.1 0 τ) * (jacobiTheta₂_term z.2 0 (τ+1))
  let G : ℤ × ℤ → ℂ := fun z => (f z + f z.swap)/2
  have hf : Summable f := summable_mul_of_summable_norm
    (theta_series_summable τ hτ).norm (theta_series_summable (τ+1) hτ1).norm
  have hG : (∑' z, G z) = ∑' z, f z := by
    simp only [G, tsum_div_const, hf.tsum_add hf.prod_symm]
    have he : (∑' z : ℤ × ℤ, f z.swap) = ∑' z : ℤ × ℤ, f z :=
      (Equiv.prodComm ℤ ℤ).tsum_eq f
    rw [he]
    ring
  have hsupport : Function.support G ⊆ Set.range parityLatticeMap := by
    intro z hz
    have hp : Even z.1 ↔ Even z.2 := by
      by_cases hm : Even z.1 <;> by_cases hn : Even z.2 <;> try tauto
      all_goals
        exfalso
        apply hz
        simp [G, f, theta_term_shift, neg_one_zpow_eq_ite, hm, hn] <;> ring
    obtain ⟨r, hr⟩ := Int.even_add.mpr hp
    refine ⟨(r,z.1-r), ?_⟩
    apply Prod.ext <;> dsimp [parityLatticeMap] <;> omega
  have hchange : (∑' z, G (parityLatticeMap z)) = ∑' z, G z :=
    parityLatticeMap_injective.tsum_eq hsupport
  have hterm (z : ℤ × ℤ) : G (parityLatticeMap z) =
      (jacobiTheta₂_term z.1 0 (2*τ+1)) * (jacobiTheta₂_term z.2 0 (2*τ+1)) := by
    rcases z with ⟨r,l⟩
    have hs : (((-1 : ℂ) ^ (r-l))) = (((-1 : ℂ) ^ (r+l))) := by
      rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp [div_eq_mul_inv, ← _root_.inv_zpow]
    have hp : (((-1 : ℂ) ^ (r+l))) = (((-1 : ℂ) ^ r)) * (((-1 : ℂ) ^ l)) := by
      exact zpow_add₀ (by norm_num) r l
    have he : (jacobiTheta₂_term (r+l) 0 τ) * (jacobiTheta₂_term (r-l) 0 τ) =
        (jacobiTheta₂_term r 0 (2*τ)) * (jacobiTheta₂_term l 0 (2*τ)) := by
      simp only [jacobiTheta₂_term, mul_zero, zero_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [G, f, parityLatticeMap, Prod.fst, Prod.snd, Prod.swap]
    rw [theta_term_shift, theta_term_shift,
      theta_term_shift (2*τ) r, theta_term_shift (2*τ) l, hs]
    calc
      _ = (((-1 : ℂ) ^ (r+l))) * ((jacobiTheta₂_term (r+l) 0 τ) * (jacobiTheta₂_term (r-l) 0 τ)) := by ring
      _ = _ := by rw [hp, he]; ring
  calc
    jacobiTheta τ * jacobiTheta (τ+1) = ∑' z, f z := by
      simpa only [jacobiTheta, jacobiTheta₂_term, mul_zero, zero_add, f] using
        tsum_mul_tsum_of_summable_norm (theta_series_summable τ hτ).norm
          (theta_series_summable (τ+1) hτ1).norm
    _ = ∑' z, G z := hG.symm
    _ = ∑' z, G (parityLatticeMap z) := hchange.symm
    _ = ∑' z : ℤ × ℤ, (jacobiTheta₂_term z.1 0 (2*τ+1)) * (jacobiTheta₂_term z.2 0 (2*τ+1)) :=
      tsum_congr hterm
    _ = jacobiTheta (2*τ+1)^2 := by
      simpa only [jacobiTheta, jacobiTheta₂_term, mul_zero, zero_add, pow_two] using
        (tsum_mul_tsum_of_summable_norm (theta_series_summable (2*τ+1) hτ2).norm
          (theta_series_summable (2*τ+1) hτ2).norm).symm
private theorem theta_nonzero_small (τ : ℂ) (hτ : 0 < τ.im) (hs : Real.exp (-Real.pi*τ.im) < 1/3) : jacobiTheta τ ≠ 0 := by
  intro hz
  let r := Real.exp (-Real.pi*τ.im)
  have hr : r < 1 := by dsimp [r]; linarith
  have hb : (1:ℝ) ≤ 2/(1-r)*r := by
    simpa only [hz, zero_sub, norm_neg, norm_one] using norm_jacobiTheta_sub_one_le hτ
  have hl : 2/(1-r)*r < (1:ℝ) := by
    rw [div_mul_eq_mul_div, div_lt_one (sub_pos.mpr hr)]
    dsimp [r]
    linarith
  exact (not_lt_of_ge hb) hl
private theorem theta_nonzero (τ : ℂ) (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  intro hz
  let z : ℕ → ℂ := fun n => (2:ℂ)^n*(τ+1)-1
  have him (n : ℕ) : (z n).im = (2:ℝ)^n*τ.im := by
    have hp : (2:ℂ)^n = (((2:ℝ)^n : ℝ):ℂ) := by norm_cast
    dsimp only [z]
    rw [hp]
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_im, add_zero, zero_mul, sub_zero]
  have hpos (n : ℕ) : 0 < (z n).im := by rw [him]; positivity
  have hrec (n : ℕ) : z (n+1) = 2*z n+1 := by
    dsimp [z]
    rw [pow_succ]
    ring
  have hzero (n : ℕ) : jacobiTheta (z n) = 0 := by
    induction n with
    | zero => simpa [z] using hz
    | succ n ih =>
      rw [hrec]
      have hh := theta_duplication (z n) (hpos n)
      rw [ih, zero_mul] at hh
      exact sq_eq_zero_iff.mp hh.symm
  have htop : Tendsto (fun n => (z n).im) atTop atTop := by
    simp_rw [him]
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hτ
  have hlim : Tendsto (fun n => Real.exp (-Real.pi*(z n).im)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (htop.const_mul_atTop_of_neg (by linarith [Real.pi_pos]))
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/3)).exists
  exact theta_nonzero_small (z n) (hpos n) hn (hzero n)
private theorem W_nonnegative (d : ℝ) (hd : 0 < d) (σ : Matrix (Fin 2) (Fin 2) ℝ) (q p : ℝ) : 0 ≤ W d σ q p := by
  unfold W
  positivity
private theorem W_gaussian_bound (d : ℝ) (hd : 0 < d) (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (q p : ℝ) : W d σ q p ≤ 2/(d*Real.sqrt σ.det) * (Real.exp (-(2*Real.pi/(d*(σ 0 0+σ 1 1)))*q^2) * Real.exp (-(2*Real.pi/(d*(σ 0 0+σ 1 1)))*p^2)) := by
  have hlow := inverse_quadratic_lower_bound σ hσ q p
  have ht : 0 < σ 0 0+σ 1 1 := add_pos (hσ.diag_pos (i:=0)) (hσ.diag_pos (i:=1))
  unfold W
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ -(2*Real.pi/d)*((q^2+p^2)/(σ 0 0+σ 1 1)) :=
      mul_le_mul_of_nonpos_left hlow (neg_nonpos.mpr (div_nonneg (by positivity) hd.le))
    _ = _ := by field_simp; ring
private theorem signed_W_lattice_summable (d : ℝ) (hd : 0 < d) (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (n k : ℝ) : Summable (fun z : ℤ × ℤ => (-1:ℝ)^(z.1*z.2)* W d σ (n+z.1*d/2) (k+z.2*d/2)) := by
  let t := 2*Real.pi/(d*(σ 0 0+σ 1 1))
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by positivity) (mul_pos hd (add_pos (hσ.diag_pos (i:=0)) (hσ.diag_pos (i:=1))))
  have hn := gaussian_shifted_summable t (d/2) n ht (by positivity)
  have hk := gaussian_shifted_summable t (d/2) k ht (by positivity)
  have hs := (hn.mul_of_nonneg hk (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).mul_left (2/(d*Real.sqrt σ.det))
  apply hs.of_norm_bounded
  intro z
  rw [norm_mul, norm_zpow, norm_neg, norm_one, _root_.one_zpow, one_mul,
    Real.norm_of_nonneg (W_nonnegative d hd σ _ _)]
  have hnarg : n+(z.1:ℝ)*d/2 = n+d/2*z.1 := by ring
  have hkarg : k+(z.2:ℝ)*d/2 = k+d/2*z.2 := by ring
  rw [hnarg,hkarg]
  exact W_gaussian_bound d hd σ hσ _ _
private theorem midpoint_exists (s : ℕ) (i j : (Finset.Icc (-(s : ℤ)) (s : ℤ))) : ∃ n : (Finset.Icc (-(s : ℤ)) (s : ℤ)), ∃ δ : ℤ, 2*(n:ℤ) = (i:ℤ)+(j:ℤ)+(2*(s:ℤ)+1)*δ := by
  obtain ⟨⟨n,β⟩,h⟩ := halfLatticeMap_surjective s ((i:ℤ)+(j:ℤ))
  exact ⟨n,-β,by dsimp [halfLatticeMap] at h; linarith⟩
private theorem parity_support (s : ℕ) (i j n : (Finset.Icc (-(s : ℤ)) (s : ℤ))) (δ : ℤ) (hm : 2*(n:ℤ) = (i:ℤ)+(j:ℤ)+(2*(s:ℤ)+1)*δ) :
    (j : ℤ) = ((2*(n:ℤ)-i : ℤ) : ZMod (2*s+1)).valMinAbs := by
  letI : NeZero (2*s+1) := ⟨by omega⟩
  symm
  apply (ZMod.valMinAbs_spec _ _).2
  constructor
  · apply sub_eq_zero.mp
    rw [← Int.cast_sub]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    refine ⟨δ, ?_⟩
    push_cast
    omega
  · have hj := j.property
    simp only [Finset.mem_Icc] at hj
    simp only [Set.mem_Ioc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    constructor <;> omega
private theorem midpoint_unique (s : ℕ) (i j n m : (Finset.Icc (-(s : ℤ)) (s : ℤ)))
    (hn : (j : ℤ) = ((2*(n:ℤ)-i : ℤ) : ZMod (2*s+1)).valMinAbs)
    (hm : (j : ℤ) = ((2*(m:ℤ)-i : ℤ) : ZMod (2*s+1)).valMinAbs) : n = m := by
  have hdn := valMinAbs_sub_dvd s (2*(n:ℤ)-i)
  have hdm := valMinAbs_sub_dvd s (2*(m:ℤ)-i)
  rw [← hn] at hdn
  rw [← hm] at hdm
  have hd : (2*(s:ℤ)+1) ∣ 2*((m:ℤ)-(n:ℤ)) := by
    convert hdn.sub hdm using 1 <;> ring
  have hc : IsCoprime (2*(s:ℤ)+1) 2 := ⟨1,-(s:ℤ),by ring⟩
  exact centered_eq_of_dvd s n m (hc.dvd_of_dvd_mul_left hd)
private theorem gaussian_fourier_term (d a b c D q w : ℝ) (hd : d ≠ 0) (ha : a ≠ 0) (hD : D ≠ 0) (hdet : D = a*b-c^2) (m : ℤ) : ((-2*Real.pi*b*q^2/(d*D):ℝ):ℂ) + -Real.pi / ((a/(2*d*D):ℝ):ℂ) * ((m:ℂ)+Complex.I*((c*q/(d*D):ℝ)+Complex.I*(w/2:ℝ)))^2 =
    ((-Real.pi * (((q+d*(w/2-m))+(q-d*(w/2-m)))^2 + D*((q+d*(w/2-m))-(q-d*(w/2-m)))^2)/(2*d*a):ℝ):ℂ) + Complex.I * (Real.pi*c*((q+d*(w/2-m))^2-(q-d*(w/2-m))^2)/(d*a):ℝ) := by
  have hd' : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have ha' : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hD' : (D:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  have he : (D:ℂ) = (a:ℂ)*(b:ℂ)-(c:ℂ)^2 := by exact_mod_cast hdet
  push_cast
  field_simp
  rw [he]
  ring_nf
  norm_num [Complex.I_sq] <;> ring
private theorem kernel_fourier_slice (d : ℝ) (hd : 0 < d) (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (q w : ℝ) : (∑' t : ℤ, (W d σ q ((t:ℝ)/2):ℂ) * Complex.exp (Complex.I*(Real.pi*(t:ℝ)*w:ℝ))) = 2 * ∑' m : ℤ, kernel d (σ 0 0) (σ 0 1) σ.det (q+d*(w/2-m)) (q-d*(w/2-m)) := by
  let a := σ 0 0
  let b := σ 1 1
  let c := σ 0 1
  let D := σ.det
  have ha : 0 < a := hσ.diag_pos (i:=0)
  have hD : 0 < D := hσ.det_pos
  have hdet : D = a*b-c^2 := by
    have hs : σ 1 0 = σ 0 1 := hσ.isHermitian.isSymm.apply 0 1
    simp only [D,a,b,c,Matrix.det_fin_two,hs,pow_two]
  have hA : 0 < a/(2*d*D) := by positivity
  have hroot : (((a/(2*d*D):ℝ):ℂ) ^ (1/2:ℂ)) =
      (Real.sqrt (a/(2*d*D)):ℂ) := by
    have hh := Complex.ofReal_cpow hA.le ((1:ℝ)/2)
    have hh' : (((a/(2*d*D))^((1:ℝ)/2):ℝ):ℂ) =
        (((a/(2*d*D):ℝ):ℂ) ^ (1/2:ℂ)) := by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hh
    rw [← hh', Real.sqrt_eq_rpow]
  have hpref : (2/(d*Real.sqrt D):ℝ) / Real.sqrt (a/(2*d*D)) =
      2*Real.sqrt (2/(d*a)) := by
    apply (sq_eq_sq₀ (by positivity : (0:ℝ) ≤ 2/(d*Real.sqrt D)/Real.sqrt (a/(2*d*D)))
      (by positivity : (0:ℝ) ≤ 2*Real.sqrt (2/(d*a)))).mp
    rw [div_pow,div_pow,mul_pow,mul_pow,Real.sq_sqrt hD.le,Real.sq_sqrt hA.le,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2/(d*a))]
    field_simp
  have hterm (t : ℤ) : (W d σ q ((t:ℝ)/2):ℂ) *
      Complex.exp (Complex.I*(Real.pi*(t:ℝ)*w:ℝ)) =
      (2/(d*Real.sqrt D):ℝ) * Complex.exp ((-2*Real.pi*b*q^2/(d*D):ℝ):ℂ) *
        Complex.exp (((-2*Real.pi/(d*D)*(a*((t:ℝ)/2)^2-2*c*q*((t:ℝ)/2)):ℝ):ℂ) +
          Complex.I*(Real.pi*(t:ℝ)*w:ℝ)) := by
    rw [W_coordinates d σ hσ.isHermitian.isSymm]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, ← Complex.exp_add, mul_assoc]
    congr 2
    dsimp [a,b,c,D]
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, half_lattice_poisson d a c D q w hd ha hD, hroot]
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro m
  unfold kernel
  have hp : ((2/(d*Real.sqrt D):ℝ):ℂ) * (1/(Real.sqrt (a/(2*d*D)):ℂ)) =
      (2:ℂ)*(Real.sqrt (2/(d*a)):ℂ) := by
    simpa only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,Complex.ofReal_inv,one_mul] using
      congrArg Complex.ofReal hpref
  rw [mul_right_comm (((2/(d*Real.sqrt D):ℝ):ℂ))
    (Complex.exp ((-2*Real.pi*b*q^2/(d*D):ℝ):ℂ)) (1/(Real.sqrt (a/(2*d*D)):ℂ)),
    mul_assoc, ← Complex.exp_add,
    gaussian_fourier_term d a b c D q w hd.ne' ha.ne' hD.ne' hdet,hp]
  exact mul_assoc _ _ _
private theorem finite_gaussian_residual_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) : Matrix.PosSemidef (fun i j => (Real.exp (-t*(p i-p j)^2):ℂ) - (Real.exp (-t*(p i)^2):ℂ)*(Real.exp (-t*(p j)^2):ℂ)) := by
  let A : Matrix (Option ι) (Option ι) ℂ := fun o u =>
    (Real.exp (-t*((o.elim 0 p)-(u.elim 0 p))^2):ℂ)
  let C : Matrix (Option ι) ι ℂ := fun o j =>
    o.elim (-(Real.exp (-t*(p j)^2):ℂ)) (fun i => if i=j then 1 else 0)
  have hA : A.PosSemidef := finite_gaussian_posSemidef (fun o : Option ι => o.elim 0 p) t ht
  have he : Cᴴ*A*C = (fun i j => (Real.exp (-t*(p i-p j)^2):ℂ) -
      (Real.exp (-t*(p i)^2):ℂ)*(Real.exp (-t*(p j)^2):ℂ)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [Fintype.sum_option, A,C,neg_sq]
    ring
  rw [← he]
  exact hA.conjTranspose_mul_mul_same C
private noncomputable def strongWave (d a c D x : ℝ) : ℂ :=
  (Real.sqrt (Real.sqrt (2/(d*a))):ℂ)*Complex.exp
    ((-Real.pi*(D+1)*x^2/(2*d*a):ℝ)+Complex.I*(Real.pi*c*x^2/(d*a):ℝ))
private theorem strongWave_factorization (d a c D x : ℝ) : strongWave d a c D x = wave d a c x * (Real.exp (-(Real.pi*(D-1)/(2*d*a))*x^2):ℂ) := by
  unfold strongWave wave
  rw [Complex.ofReal_exp]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring
private theorem kernel_residual_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (d a c D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : Matrix.PosSemidef (fun i j => kernel d a c D (p i) (p j) - strongWave d a c D (p i)*star (strongWave d a c D (p j))) := by
  have hR := finite_gaussian_residual_posSemidef p (Real.pi*(D-1)/(2*d*a))
    (lambda_nonnegative d a D hd ha hD)
  have hW := Matrix.posSemidef_vecMulVec_self_star (fun i => wave d a c (p i))
  have he : (fun i j => kernel d a c D (p i) (p j) -
      strongWave d a c D (p i)*star (strongWave d a c D (p j))) =
      Matrix.vecMulVec (fun i => wave d a c (p i)) (star (fun i => wave d a c (p i))) ⊙
      (fun i j => (Real.exp (-(Real.pi*(D-1)/(2*d*a))*(p i-p j)^2):ℂ) -
        (Real.exp (-(Real.pi*(D-1)/(2*d*a))*(p i)^2):ℂ)*
        (Real.exp (-(Real.pi*(D-1)/(2*d*a))*(p j)^2):ℂ)) := by
    ext i j
    change _ = (wave d a c (p i)*star (wave d a c (p j)))*(_-_)
    rw [kernel_factorization, strongWave_factorization, strongWave_factorization]
    simp only [map_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [he]
  exact hW.hadamard hR
private theorem strongWave_norm (d a c D x : ℝ) : ‖strongWave d a c D x‖ = Real.sqrt (Real.sqrt (2/(d*a))) * Real.exp (-(Real.pi*(D+1)/(2*d*a))*x^2) := by
  unfold strongWave
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  congr 2
  ring
private theorem strongWave_summable (d a c D x : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : Summable (fun r : ℤ => strongWave d a c D (x+d*r)) := by
  have ht : 0 < Real.pi*(D+1)/(2*d*a) := by positivity
  apply ((gaussian_shifted_summable _ d x ht hd.ne').mul_left
    (Real.sqrt (Real.sqrt (2/(d*a))))).of_norm_bounded
  intro r
  exact (strongWave_norm d a c D (x+d*r)).le
private theorem strongWave_zero_sum_ne_zero (d a c D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : (∑' r : ℤ, strongWave d a c D (d*r)) ≠ 0 := by
  let τ : ℂ := (d*c/a:ℝ)+Complex.I*(d*(D+1)/(2*a):ℝ)
  have hτ : 0 < τ.im := by
    dsimp [τ]
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add]
    positivity
  have he : (∑' r : ℤ, strongWave d a c D (d*r)) =
      (Real.sqrt (Real.sqrt (2/(d*a))):ℂ)*jacobiTheta τ := by
    unfold strongWave jacobiTheta
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    congr 2
    dsimp [τ]
    push_cast
    have hi := Complex.I_sq
    field_simp
    ring_nf
    norm_num [Complex.I_sq] <;> ring
  rw [he]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (theta_nonzero τ hτ)
private theorem lattice_sum_nonnegative (L : ℝ → ℝ → ℂ) (d x : ℝ) (hL : ∀ (R : Finset ℤ), Matrix.PosSemidef (fun r l : R => L (x+d*r) (x+d*l))) (hs : Summable (fun z : ℤ × ℤ => L (x+d*z.1) (x+d*z.2))) : 0 ≤ ∑' z : ℤ × ℤ, L (x+d*z.1) (x+d*z.2) := by
  have hfinite (R : Finset ℤ) : 0 ≤ ∑ r ∈ R, ∑ l ∈ R, L (x+d*r) (x+d*l) := by
    have h := (hL R).dotProduct_mulVec_nonneg (fun _ => 1)
    have h' : 0 ≤ ∑ r : R, ∑ l : R, L (x+d*r) (x+d*l) := by
      simpa [dotProduct,Matrix.mulVec] using h
    rw [sum_subtype_pair R (fun r l => L (x+d*r) (x+d*l))] at h'
    exact h'
  have hlim := hs.hasSum.comp
    (Filter.tendsto_finsetProd_atTop.comp Filter.tendsto_atTop_diagonal)
  apply ge_of_tendsto (show Tendsto (fun R : Finset ℤ =>
      ∑ r ∈ R, ∑ l ∈ R, L (x+d*r) (x+d*l)) atTop
      (𝓝 (∑' z : ℤ × ℤ, L (x+d*z.1) (x+d*z.2))) from
    by simpa only [Function.comp_def,Finset.sum_product] using hlim)
  exact Filter.Eventually.of_forall hfinite
private theorem periodized_kernel_zero_diagonal_pos (d a c D : ℝ) (hd : 0 < d) (ha : 0 < a) (hD : 1 ≤ D) : 0 < (∑' z : ℤ × ℤ, kernel d a c D (d*z.1) (d*z.2)).re := by
  have hw : Summable (fun r : ℤ => strongWave d a c D (d*r)) := by
    simpa only [zero_add] using strongWave_summable d a c D 0 hd ha hD
  have hws := summable_mul_of_summable_norm hw.norm hw.star.norm
  have hk : Summable (fun z : ℤ × ℤ => kernel d a c D (d*z.1) (d*z.2)) := by
    simpa only [zero_add] using kernel_lattice_summable d a c D 0 0 hd ha hD
  have hs := hk.sub hws
  have hnn : 0 ≤ (∑' z : ℤ × ℤ, (kernel d a c D (d*z.1) (d*z.2) -
      strongWave d a c D (d*z.1)*star (strongWave d a c D (d*z.2)))) := by
    simpa only [zero_add] using lattice_sum_nonnegative
      (fun x y => kernel d a c D x y - strongWave d a c D x*star (strongWave d a c D y)) d 0
      (fun (R : Finset ℤ) => by
        simpa only [zero_add] using (kernel_residual_posSemidef
          (fun r : R => d*r) d a c D hd ha hD))
      (by simpa only [zero_add] using hs)
  rw [hk.tsum_sub hws] at hnn
  rw [← tsum_mul_tsum_of_summable_norm hw.norm hw.star.norm, ← tsum_star] at hnn
  have hr := Complex.nonneg_iff.mp hnn
  have hn := Complex.normSq_pos.mpr (strongWave_zero_sum_ne_zero d a c D hd ha hD)
  have hc : ((∑' r : ℤ, strongWave d a c D (d*r))*
      star (∑' r : ℤ, strongWave d a c D (d*r))).re =
      Complex.normSq (∑' r : ℤ, strongWave d a c D (d*r)) := by
    simp only [Complex.star_def,Complex.mul_conj,Complex.ofReal_re]
  rw [Complex.sub_re,hc] at hr
  linarith [hr.1]
private noncomputable def kernelLatticeEquiv (A B : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
  (Equiv.prodCongrLeft (fun l : ℤ => Equiv.addRight (A-l))).trans
    (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.addLeft B))
private theorem phase_half_lattice (s : ℕ) (i j n k α β δ : ℤ) (hm : 2*n = i+j+(2*(s:ℤ)+1)*δ) : (((-1:ℝ)^(α*β):ℝ):ℂ) * Complex.exp (4*Real.pi*Complex.I*k*((i:ℂ)-n)/(2*s+1)) = Complex.exp (Complex.I*(Real.pi*(2*k+(2*(s:ℝ)+1)*β)* (((i:ℝ)-j)/(2*s+1)+α+((i:ℝ)-j)):ℝ)) := by
  have hd : (2*(s:ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (2*(s:ℤ)+1) ≠ 0 by omega)
  have hmC : (2:ℂ)*(n:ℂ) = (i:ℂ)+(j:ℂ)+(2*(s:ℂ)+1)*(δ:ℂ) := by exact_mod_cast hm
  rw [Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one, ← exp_pi_int, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-k*δ-k*α-k*(i-j)-(s:ℤ)*α*β-((s:ℤ)+1)*β*(i-j), ?_⟩
  have hval : (n:ℂ) = ((i:ℂ)+(j:ℂ)+(2*(s:ℂ)+1)*(δ:ℂ))/2 := by
    linear_combination (1/2:ℂ)*hmC
  push_cast
  rw [hval]
  field_simp
  ring
private theorem unnormalized_entry_midpoint (s : ℕ) (σ : Matrix (Fin 2) (Fin 2) ℝ) (i j n : (Finset.Icc (-(s : ℤ)) (s : ℤ))) (δ : ℤ) (hm : 2*(n:ℤ) = (i:ℤ)+(j:ℤ)+(2*(s:ℤ)+1)*δ) : unnormalized s (2*s+1) σ i j = ∑ k : (Finset.Icc (-(s : ℤ)) (s : ℤ)), (wSum s (2*s+1) σ n k : ℂ)*
        Complex.exp (4*Real.pi*Complex.I*(k:ℤ)*((i:ℤ)-n)/(2*s+1)) := by
  unfold unnormalized
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single n]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [parity, if_pos (parity_support s i j n δ hm)]
  · intro m hm' hmn
    apply Finset.sum_eq_zero
    intro k hk
    have hne : (j : ℤ) ≠ ((2*(m:ℤ)-i : ℤ) : ZMod (2*s+1)).valMinAbs := by
      intro hh
      exact hmn (midpoint_unique s i j m n hh (parity_support s i j n δ hm))
    simp only [parity, if_neg hne,mul_zero]
  · simp
private theorem entry_half_lattice (s : ℕ) (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (i j n : (Finset.Icc (-(s : ℤ)) (s : ℤ))) (δ : ℤ) (hm : 2*(n:ℤ) = (i:ℤ)+(j:ℤ)+(2*(s:ℤ)+1)*δ) : unnormalized s (2*s+1) σ i j = ∑' α : ℤ, ∑' t : ℤ, (W (2*s+1) σ
        ((n:ℝ)+α*(2*s+1)/2) ((t:ℝ)/2):ℂ)* Complex.exp (Complex.I*(Real.pi*(t:ℝ)* (((i:ℝ)-j)/(2*s+1)+α+((i:ℝ)-j)):ℝ)) := by
  let d : ℝ := 2*s+1
  have hd : 0 < d := by dsimp [d]; positivity
  let f : (Finset.Icc (-(s : ℤ)) (s : ℤ)) × (ℤ × ℤ) → ℂ := fun z =>
    (((-1:ℝ)^(z.2.1*z.2.2)*W d σ ((n:ℝ)+z.2.1*d/2)
      ((z.1:ℝ)+z.2.2*d/2):ℝ):ℂ)*
      Complex.exp (4*Real.pi*Complex.I*(z.1:ℤ)*((i:ℤ)-n)/(2*s+1))
  have hfk (k : (Finset.Icc (-(s : ℤ)) (s : ℤ))) : Summable (fun z : ℤ × ℤ => f (k,z)) := by
    have hr : Summable (fun z : ℤ × ℤ =>
        (((-1:ℝ)^(z.1*z.2)*W d σ ((n:ℝ)+z.1*d/2) ((k:ℝ)+z.2*d/2):ℝ):ℂ)) :=
      Complex.summable_ofReal.mpr (signed_W_lattice_summable d hd σ hσ (n:ℝ) (k:ℝ))
    exact hr.mul_right (Complex.exp (4*Real.pi*Complex.I*(k:ℤ)*((i:ℤ)-n)/(2*s+1)))
  have hf : Summable f := by
    apply Summable.of_norm
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨fun k => (hfk k).norm, (hasSum_fintype _).summable⟩
  let e : ((Finset.Icc (-(s : ℤ)) (s : ℤ)) × (ℤ × ℤ)) ≃ (ℤ × ((Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ)) :=
    {toFun := fun z => (z.2.1,(z.1,z.2.2)),
     invFun := fun z => (z.2.1,(z.1,z.2.2)), left_inv := fun _ => rfl, right_inv := fun _ => rfl}
  have hre : Summable (fun z : ℤ × ((Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ) => f (e.symm z)) := e.symm.summable_iff.mpr hf
  calc
    unnormalized s (2*s+1) σ i j = ∑' k : (Finset.Icc (-(s : ℤ)) (s : ℤ)), ∑' z : ℤ × ℤ, f (k,z) := by
      rw [unnormalized_entry_midpoint s σ i j n δ hm]
      simp only [tsum_fintype]
      apply Finset.sum_congr rfl
      intro k hk
      have hd' : (2*(s:ℝ)+1) ≠ 0 := hd.ne'
      simp only [wSum,div_self hd',Real.sqrt_one,mul_one]
      rw [Complex.ofReal_tsum,← tsum_mul_right]
    _ = ∑' z : (Finset.Icc (-(s : ℤ)) (s : ℤ)) × (ℤ × ℤ), f z := hf.tsum_prod.symm
    _ = ∑' z : ℤ × ((Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ), f (e.symm z) := (e.symm.tsum_eq f).symm
    _ = ∑' α : ℤ, ∑' z : (Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ, f (e.symm (α,z)) := hre.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro α
      have ht : (∑' z : (Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ, f (e.symm (α,z))) =
          ∑' z : (Finset.Icc (-(s : ℤ)) (s : ℤ)) × ℤ, (W d σ ((n:ℝ)+α*d/2)
            (((halfLatticeEquiv s z:ℤ):ℝ)/2):ℂ)*
            Complex.exp (Complex.I*(Real.pi*((halfLatticeEquiv s z:ℤ):ℝ)*
              (((i:ℝ)-j)/d+α+((i:ℝ)-j)):ℝ)) := by
        apply tsum_congr
        rintro ⟨k,β⟩
        change (((-1:ℝ)^(α*β)*W d σ ((n:ℝ)+α*d/2) ((k:ℝ)+β*d/2):ℝ):ℂ)*
          Complex.exp (4*Real.pi*Complex.I*(k:ℤ)*((i:ℤ)-n)/(2*s+1)) = _
        rw [Complex.ofReal_mul]
        rw [mul_right_comm]
        rw [phase_half_lattice s i j n k α β δ hm]
        have hp : (k:ℝ)+(β:ℝ)*d/2 = ((halfLatticeEquiv s (k,β):ℤ):ℝ)/2 := by
          change (k:ℝ)+(β:ℝ)*d/2 = ((2*(k:ℤ)+(2*(s:ℤ)+1)*β:ℤ):ℝ)/2
          push_cast
          dsimp [d]
          ring
        have htval : ((halfLatticeEquiv s (k,β):ℤ):ℝ) =
            2*(k:ℝ)+(2*(s:ℝ)+1)*β := by
          change ((2*(k:ℤ)+(2*(s:ℤ)+1)*β:ℤ):ℝ) = _
          push_cast
          rfl
        rw [hp,htval]
        exact mul_comm _ _
      rw [ht]
      exact (halfLatticeEquiv s).tsum_eq (fun t : ℤ =>
        (W d σ ((n:ℝ)+α*d/2) ((t:ℝ)/2):ℂ)*Complex.exp
          (Complex.I*(Real.pi*(t:ℝ)*(((i:ℝ)-j)/d+α+((i:ℝ)-j)):ℝ)))
private theorem kernel_identity (s : ℕ) (σ : Matrix (Fin 2) (Fin 2) ℝ) (hσ : σ.PosDef) (hD : 1 ≤ σ.det) (i j : (Finset.Icc (-(s : ℤ)) (s : ℤ))) : unnormalized s (2*s+1) σ i j = 2*∑' z : ℤ × ℤ, kernel (2*s+1) (σ 0 0) (σ 0 1) σ.det ((i:ℝ)+(2*s+1)*z.1) ((j:ℝ)+(2*s+1)*z.2) := by
  let d : ℝ := 2*s+1
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨n,δ,hm⟩ := midpoint_exists s i j
  let A : ℤ := n-j-(s:ℤ)*δ
  let B : ℤ := n-i-(s:ℤ)*δ
  let e := kernelLatticeEquiv A B
  let q : ℤ → ℝ := fun α => (n:ℝ)+α*d/2
  let w : ℤ → ℝ := fun α => ((i:ℝ)-j)/d+α+((i:ℝ)-j)
  have hn : (n:ℝ) = ((i:ℝ)+(j:ℝ)+d*δ)/2 := by
    have hh : 2*(n:ℝ) = (i:ℝ)+(j:ℝ)+(2*(s:ℝ)+1)*δ := by exact_mod_cast hm
    dsimp [d]
    linarith
  let f : ℤ × ℤ → ℂ := fun z => kernel d (σ 0 0) (σ 0 1) σ.det
    ((i:ℝ)+d*z.1) ((j:ℝ)+d*z.2)
  have hpoint (z : ℤ × ℤ) :
      kernel d (σ 0 0) (σ 0 1) σ.det
        (q z.1+d*(w z.1/2-z.2)) (q z.1-d*(w z.1/2-z.2)) = f (e z) := by
    change kernel d (σ 0 0) (σ 0 1) σ.det
        (q z.1+d*(w z.1/2-z.2)) (q z.1-d*(w z.1/2-z.2)) =
      kernel d (σ 0 0) (σ 0 1) σ.det
        ((i:ℝ)+d*((z.1+(A-z.2):ℤ):ℝ)) ((j:ℝ)+d*((B+z.2:ℤ):ℝ))
    congr 1
    all_goals
      dsimp only [q,w,A,B]
      push_cast
      rw [hn]
      dsimp [d]
      field_simp
      ring
  have hf : Summable f := kernel_lattice_summable d (σ 0 0) (σ 0 1) σ.det i j
    hd (hσ.diag_pos (i:=0)) hD
  have hfe : Summable (fun z => f (e z)) := e.summable_iff.mpr hf
  calc
    unnormalized s (2*s+1) σ i j =
      ∑' α : ℤ, ∑' t : ℤ, (W d σ (q α) ((t:ℝ)/2):ℂ)*
        Complex.exp (Complex.I*(Real.pi*(t:ℝ)*w α:ℝ)) :=
      entry_half_lattice s σ hσ i j n δ hm
    _ = ∑' α : ℤ, 2*∑' m : ℤ, kernel d (σ 0 0) (σ 0 1) σ.det
        (q α+d*(w α/2-m)) (q α-d*(w α/2-m)) := by
      apply tsum_congr
      intro α
      exact kernel_fourier_slice d hd σ hσ (q α) (w α)
    _ = 2*∑' α : ℤ, ∑' m : ℤ, f (e (α,m)) := by
      rw [tsum_mul_left]
      apply congrArg (fun x : ℂ => 2*x)
      apply tsum_congr
      intro α
      apply tsum_congr
      intro m
      exact hpoint (α,m)
    _ = 2*∑' z : ℤ × ℤ, f (e z) := congrArg (fun x : ℂ => 2*x) hfe.tsum_prod.symm
    _ = _ := congrArg (fun x : ℂ => 2*x) (e.tsum_eq f)
theorem result : claim := by
  intro s hs h hh σ hσ hU
  rw [rhoTilde_scaling s h hh σ]
  have hd : (0:ℝ) < 2*s+1 := by positivity
  have ha : 0 < σ 0 0 := hσ.diag_pos (i:=0)
  have hD := uncertainty_det_bound σ hσ hU
  let P : Matrix ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ((Finset.Icc (-(s : ℤ)) (s : ℤ))) ℂ := fun i j => ∑' z : ℤ × ℤ,
    kernel (2*s+1) (σ 0 0) (σ 0 1) σ.det
      ((i:ℝ)+(2*s+1)*z.1) ((j:ℝ)+(2*s+1)*z.2)
  have hP : P.PosSemidef := periodization_posSemidef (fun i : (Finset.Icc (-(s : ℤ)) (s : ℤ)) => (i:ℝ))
    (2*s+1) (σ 0 0) (σ 0 1) σ.det hd ha hD
    (fun i j => kernel_lattice_summable _ _ _ _ i j hd ha hD)
  have he : unnormalized s (2*s+1) σ = (2:ℂ) • P := by
    ext i j
    exact kernel_identity s σ hσ hD i j
  have hM : (unnormalized s (2*s+1) σ).PosSemidef := by
    rw [he]
    exact hP.smul (by norm_num : (0:ℂ) ≤ 2)
  apply normalization_isDensity _ hM
  intro ht
  have hz := hM.trace_eq_zero_iff.mp ht
  let i0 : (Finset.Icc (-(s : ℤ)) (s : ℤ)) := ⟨0, by simp only [Finset.mem_Icc]; omega⟩
  have hdiag := periodized_kernel_zero_diagonal_pos (2*s+1) (σ 0 0) (σ 0 1) σ.det hd ha hD
  have hpos : 0 < (unnormalized s (2*s+1) σ i0 i0).re := by
    rw [kernel_identity s σ hσ hD]
    simpa [i0,Complex.mul_re] using mul_pos (by norm_num : (0:ℝ)<2) hdiag
  rw [hz] at hpos
  simpa using hpos
end D5.S3.Quantum.CotfasDVGS
