import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.GNSMatrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Physical upper-boundary amplitude for partial-trace Petz recovery

The powers use the Hermitian spectral theorem and the scalar complex power on
positive eigenvalues. The lift is the Kronecker product with the identity on
the erased factor. At the upper boundary the right factor of the amplitude
is unitary, and the two powers of the input marginal combine to that marginal.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight
  trace_partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef
  partialTraceRight_embed_mul)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)

namespace PetzPhysicalAmplitude

universe u

section SpectralPower

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}

/-- The complex power of a faithful positive matrix, in its Hermitian eigenbasis. -/
def spectralCPow (hX : X.PosDef) (z : ℂ) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary
    (diagonal fun i => (hX.isHermitian.eigenvalues i : ℂ) ^ z)

@[simp] theorem spectralCPow_zero (hX : X.PosDef) : spectralCPow hX 0 = 1 := by
  simp only [spectralCPow, Complex.cpow_zero, Matrix.diagonal_one, map_one]

@[simp] theorem spectralCPow_one (hX : X.PosDef) : spectralCPow hX 1 = X := by
  simp only [spectralCPow, Complex.cpow_one]
  simpa only [Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] using hX.isHermitian.spectral_theorem.symm

theorem spectralCPow_mul (hX : X.PosDef) (z w : ℂ) :
    spectralCPow hX z * spectralCPow hX w = spectralCPow hX (z + w) := by
  unfold spectralCPow
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  apply congrArg (fun d : n → ℂ =>
    Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary (diagonal d))
  funext i
  exact (Complex.cpow_add z w (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (hX.eigenvalues_pos i)))).symm

private theorem star_cpow_ofReal {x : ℝ} (hx : 0 ≤ x) (z : ℂ) :
    star ((x : ℂ) ^ z) = (x : ℂ) ^ (star z) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact ne_of_lt Real.pi_pos
  simpa only [Complex.star_def, Complex.conj_ofReal] using
    (Complex.cpow_conj (x : ℂ) z harg).symm

theorem spectralCPow_conjTranspose (hX : X.PosDef) (z : ℂ) :
    (spectralCPow hX z)ᴴ = spectralCPow hX (star z) := by
  unfold spectralCPow
  rw [← Matrix.star_eq_conjTranspose, ← map_star, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]
  apply congrArg (fun d : n → ℂ =>
    Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary (diagonal d))
  funext i
  exact star_cpow_ofReal (le_of_lt (hX.eigenvalues_pos i)) z

private theorem star_real_mul_I (s : ℝ) :
    star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

/-- Both unitary identities for a purely imaginary power. -/
theorem spectralCPow_imaginary_unitary (hX : X.PosDef) (s : ℝ) :
    spectralCPow hX ((s : ℂ) * Complex.I) * (spectralCPow hX ((s : ℂ) * Complex.I))ᴴ = 1 ∧
    (spectralCPow hX ((s : ℂ) * Complex.I))ᴴ * spectralCPow hX ((s : ℂ) * Complex.I) = 1 := by
  constructor
  · rw [spectralCPow_conjTranspose, star_real_mul_I, spectralCPow_mul, add_neg_cancel,
      spectralCPow_zero]
  · rw [spectralCPow_conjTranspose, star_real_mul_I, spectralCPow_mul, neg_add_cancel,
      spectralCPow_zero]

theorem spectralCPow_real (hX : X.PosDef) (r : ℝ) :
    spectralCPow hX (r : ℂ) = cfc (fun x : ℝ => x ^ r) X := by
  rw [hX.isHermitian.cfc_eq, Matrix.IsHermitian.cfc]
  unfold spectralCPow
  apply congrArg (fun d : n → ℂ =>
    Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary (diagonal d))
  funext i
  change (hX.isHermitian.eigenvalues i : ℂ) ^ (r : ℂ) =
    ((hX.isHermitian.eigenvalues i ^ r : ℝ) : ℂ)
  exact (Complex.ofReal_cpow (le_of_lt (hX.eigenvalues_pos i)) r).symm

theorem spectralCPow_half (hX : X.PosDef) :
    spectralCPow hX ((1 / 2 : ℝ) : ℂ) = cfc Real.sqrt X := by
  simpa only [← Real.sqrt_eq_rpow] using spectralCPow_real hX (1 / 2)

theorem spectralCPow_neg_half (hX : X.PosDef) :
    spectralCPow hX (-((1 / 2 : ℝ) : ℂ)) = spectralInverseSqrt X := by
  rw [spectralInverseSqrt, hX.isHermitian.cfc_eq, Matrix.IsHermitian.cfc]
  unfold spectralCPow
  apply congrArg (fun d : n → ℂ =>
    Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary (diagonal d))
  funext i
  change (hX.isHermitian.eigenvalues i : ℂ) ^ (-((1 / 2 : ℝ) : ℂ)) =
    (((Real.sqrt (hX.isHermitian.eigenvalues i))⁻¹ : ℝ) : ℂ)
  rw [Complex.cpow_neg, ← Complex.ofReal_cpow (le_of_lt (hX.eigenvalues_pos i)),
    ← Real.sqrt_eq_rpow, Complex.ofReal_inv]

private theorem star_half : star (((1 / 2 : ℝ) : ℂ)) = ((1 / 2 : ℝ) : ℂ) :=
  Complex.conj_ofReal _

private theorem half_add_half : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Complex.ofReal_one]

theorem sqrt_gram (hX : X.PosDef) : cfc Real.sqrt X * (cfc Real.sqrt X)ᴴ = X := by
  simp only [← spectralCPow_half hX, spectralCPow_conjTranspose, star_half,
    spectralCPow_mul, half_add_half, spectralCPow_one]

end SpectralPower

section Lift

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Embed a retained operator by tensoring with the identity on the erased factor. -/
def lift (X : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  X ⊗ₖ (1 : Matrix B B ℂ)

theorem lift_mul (X Y : Matrix A A ℂ) : lift (B := B) (X * Y) = lift X * lift Y := by
  simpa only [lift, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul X Y (1 : Matrix B B ℂ) (1 : Matrix B B ℂ))

theorem lift_conjTranspose (X : Matrix A A ℂ) : (lift (B := B) X)ᴴ = lift (Xᴴ) := by
  simpa only [lift, Matrix.conjTranspose_one] using
    (Matrix.conjTranspose_kronecker X (1 : Matrix B B ℂ))

/-- Trace duality for the actual right partial trace. -/
theorem trace_lift_mul (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    (lift X * Y).trace = (X * partialTraceRight Y).trace := by
  calc
    _ = (partialTraceRight (lift X * Y)).trace := (trace_partialTraceRight _).symm
    _ = _ := by
      rw [lift, partialTraceRight_embed_mul (R := A) (a := B) Y X]

end Lift

/-- The upper strip boundary with the positive outside rotation convention. -/
def upperExponent (s : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I

private theorem upperExponent_zero : upperExponent 0 = ((1 / 2 : ℝ) : ℂ) := by
  simp only [upperExponent, Complex.ofReal_zero, zero_mul, add_zero]

private theorem star_upperExponent (s : ℝ) :
    star (upperExponent s) = ((1 / 2 : ℝ) : ℂ) - (s : ℂ) * Complex.I := by
  simp only [upperExponent, star_add, star_half, star_real_mul_I, sub_eq_add_neg]

private theorem upperExponent_add_star (s : ℝ) : upperExponent s + star (upperExponent s) = 1 := by
  rw [star_upperExponent, upperExponent]
  calc
    _ = ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) := by ring
    _ = 1 := half_add_half

section PartialTrace

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
variable {ρ σ : Matrix (A × B) (A × B) ℂ}

/-- `σ^z lift(q^(-z) p^z) ρ^(1/2-z)`, with the two marginals formed by partial trace. -/
def gamma (hρ : ρ.PosDef) (hσ : σ.PosDef) (z : ℂ) : Matrix (A × B) (A × B) ℂ :=
  spectralCPow hσ z *
    lift (spectralCPow (partialTraceRight_posDef (R := A) (a := B) σ hσ) (-z) *
      spectralCPow (partialTraceRight_posDef (R := A) (a := B) ρ hρ) z) *
    spectralCPow hρ (((1 / 2 : ℝ) : ℂ) - z)

/-- The rotated Petz output on the actual input marginal. -/
def rotatedPetz (ρ : Matrix (A × B) (A × B) ℂ) (hσ : σ.PosDef) (s : ℝ) :
    Matrix (A × B) (A × B) ℂ :=
  let z := upperExponent s
  let hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  spectralCPow hσ z *
    lift (spectralCPow hq (-z) * partialTraceRight ρ * spectralCPow hq (-(star z))) *
    spectralCPow hσ (star z)

/-- The ordinary partial-trace Petz formula, using the existing real spectral operators. -/
def ordinaryPetz (σ : Matrix (A × B) (A × B) ℂ) (p : Matrix A A ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  let Q := spectralInverseSqrt (partialTraceRight σ)
  cfc Real.sqrt σ * lift (Q * p * Q) * cfc Real.sqrt σ

/-- The upper-boundary Gram matrix is exactly the rotated physical Petz output. -/
theorem gamma_upper_gram (hρ : ρ.PosDef) (hσ : σ.PosDef) (s : ℝ) :
    gamma hρ hσ (upperExponent s) * (gamma hρ hσ (upperExponent s))ᴴ =
      rotatedPetz ρ hσ s := by
  let z := upperExponent s
  let hp := partialTraceRight_posDef (R := A) (a := B) ρ hρ
  let hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  let S := spectralCPow hσ z
  let Q := spectralCPow hq (-z)
  let P := spectralCPow hp z
  let W := spectralCPow hρ (((1 / 2 : ℝ) : ℂ) - z)
  have hρExp : ((1 / 2 : ℝ) : ℂ) - z = ((-s : ℝ) : ℂ) * Complex.I := by
    dsimp only [z, upperExponent]
    rw [Complex.ofReal_neg]
    ring
  have hW : W * Wᴴ = 1 := by
    dsimp only [W]
    rw [hρExp]
    exact (spectralCPow_imaginary_unitary hρ (-s)).1
  have hP : P * Pᴴ = partialTraceRight ρ := by
    dsimp only [P]
    rw [spectralCPow_conjTranspose, spectralCPow_mul, upperExponent_add_star s,
      spectralCPow_one]
  have hRetained : (Q * P) * (Q * P)ᴴ = Q * partialTraceRight ρ * Qᴴ := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = Q * (P * Pᴴ) * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  change (S * lift (Q * P) * W) * (S * lift (Q * P) * W)ᴴ = _
  calc
    _ = S * (lift (Q * P) * ((W * Wᴴ) * (lift (B := B) (Q * P))ᴴ)) * Sᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = S * lift (Q * partialTraceRight ρ * Qᴴ) * Sᴴ := by
      rw [hW, Matrix.one_mul, lift_conjTranspose, ← lift_mul, hRetained]
    _ = rotatedPetz ρ hσ s := by
      simp only [rotatedPetz, S, Q, z, hq, spectralCPow_conjTranspose, star_neg]

theorem rotatedPetz_zero (hσ : σ.PosDef) :
    rotatedPetz ρ hσ 0 = ordinaryPetz σ (partialTraceRight ρ) := by
  have hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  simp only [rotatedPetz, ordinaryPetz, upperExponent_zero, star_half,
    spectralCPow_half hσ, spectralCPow_neg_half hq]

theorem gamma_half_gram (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    gamma hρ hσ ((1 / 2 : ℝ) : ℂ) * (gamma hρ hσ ((1 / 2 : ℝ) : ℂ))ᴴ =
      ordinaryPetz σ (partialTraceRight ρ) := by
  simpa only [upperExponent_zero, rotatedPetz_zero] using gamma_upper_gram hρ hσ 0

/-- Cyclicity and partial-trace duality give trace preservation for this input. -/
theorem rotatedPetz_trace (hσ : σ.PosDef) (s : ℝ) :
    (rotatedPetz ρ hσ s).trace = ρ.trace := by
  let z := upperExponent s
  let p := partialTraceRight ρ
  let q := partialTraceRight σ
  let hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  let S := spectralCPow hσ z
  let T := spectralCPow hσ (star z)
  let Q := spectralCPow hq (-z)
  let R := spectralCPow hq (-(star z))
  let K := Q * p * R
  have hz : z + star z = 1 := upperExponent_add_star s
  have hTS : T * S = σ := by
    have hz' : star z + z = 1 := (add_comm _ _).trans hz
    dsimp only [S, T]
    rw [spectralCPow_mul, hz', spectralCPow_one]
  have hRQ : R * q * Q = 1 := by
    have he : (-(star z) + 1) + -z = 0 := by
      calc
        _ = 1 - (z + star z) := by ring
        _ = 0 := by rw [hz, sub_self]
    calc
      _ = R * spectralCPow hq 1 * Q := by rw [spectralCPow_one]
      _ = spectralCPow hq ((-(star z) + 1) + -z) := by
        dsimp only [R, Q]
        rw [spectralCPow_mul, spectralCPow_mul]
      _ = 1 := by rw [he, spectralCPow_zero]
  change (S * lift K * T).trace = ρ.trace
  calc
    _ = (T * S * lift K).trace := Matrix.trace_mul_cycle S (lift K) T
    _ = (lift K * σ).trace := by rw [hTS, Matrix.trace_mul_comm σ (lift K)]
    _ = (K * q).trace := trace_lift_mul K σ
    _ = (R * q * Q * p).trace := by
      simpa only [K, Matrix.mul_assoc] using Matrix.trace_mul_comm (Q * p) (R * q)
    _ = p.trace := by rw [hRQ, Matrix.one_mul]
    _ = ρ.trace := trace_partialTraceRight ρ

theorem gamma_upper_gram_trace_one (hρ : ρ.PosDef) (hσ : σ.PosDef) (htrace : ρ.trace = 1)
    (s : ℝ) : (gamma hρ hσ (upperExponent s) * (gamma hρ hσ (upperExponent s))ᴴ).trace = 1 := by
  rw [gamma_upper_gram, rotatedPetz_trace, htrace]

end PartialTrace

private theorem frobenius_eq_one_of_gram_trace {n : Type*} [Fintype n] (M : Matrix n n ℂ)
    (h : (M * Mᴴ).trace = 1) : ‖M‖ = 1 := by
  have hc : ((‖M‖ ^ 2 : ℝ) : ℂ) = 1 :=
    (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace M).trans
      ((Matrix.trace_mul_comm Mᴴ M).trans h)
  have hr : ‖M‖ ^ 2 = 1 := by
    simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re hc
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hr)

theorem sqrt_frobenius_eq_one {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.PosDef) (htrace : X.trace = 1) : ‖cfc Real.sqrt X‖ = 1 :=
  frobenius_eq_one_of_gram_trace _ (by rw [sqrt_gram hX, htrace])

theorem gamma_upper_frobenius_eq_one {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Nonempty B] {ρ σ : Matrix (A × B) (A × B) ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (htrace : ρ.trace = 1) (s : ℝ) :
    ‖gamma hρ hσ (upperExponent s)‖ = 1 :=
  frobenius_eq_one_of_gram_trace _ (gamma_upper_gram_trace_one hρ hσ htrace s)

end PetzPhysicalAmplitude
