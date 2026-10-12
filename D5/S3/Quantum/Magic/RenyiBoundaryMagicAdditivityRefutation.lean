/- GID: D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.claim; result=D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.result; claim=D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.claim
   digest: Boundary alpha-z magic additivity is refuted by a three-qubit marginal certificate. -/

import D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape

set_option linter.style.longLine false
set_option maxRecDepth 4096
set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation

open D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape

def SupportLE {n : ℕ} (ρ σ : Op n) : Prop :=
  ∀ v : Bits n → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0

def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

def DPI (α z : ℝ) : Prop :=
  0 < z ∧ ((0 < α ∧ α < 1 ∧ max α (1 - α) ≤ z) ∨ α = 1 ∨
    (1 < α ∧ α ≤ 2 ∧ α / 2 ≤ z ∧ z ≤ α) ∨
    (2 ≤ α ∧ α - 1 ≤ z ∧ z ≤ α))

private noncomputable def spectralPow {n : ℕ} (A : Op n) (x : ℝ) : Op n :=
  if h : A.IsHermitian then h.cfc (fun t => t ^ x) else 0

private noncomputable def spectralLog {n : ℕ} (A : Op n) : Op n :=
  if h : A.IsHermitian then h.cfc Real.log else 0

def Qaz {n : ℕ} (α z : ℝ) (ρ σ : Op n) : ℝ :=
  tr (spectralPow (spectralPow ρ (α / (2 * z)) *
    spectralPow σ ((1 - α) / z) * spectralPow ρ (α / (2 * z))) z)

def Daz {n : ℕ} (α z : ℝ) (ρ σ : Op n) : EReal := by
  classical
  exact if α = 2 ∧ z = 1 then
      if SupportLE ρ σ then
        ((log2 (tr (ρ * ρ * σ⁻¹)) : ℝ) : EReal)
      else ⊤
    else if α = 1 then
      if SupportLE ρ σ then
        ((tr (ρ * (spectralLog ρ - spectralLog σ)) / Real.log 2 : ℝ) : EReal)
      else ⊤
    else if (α < 1 ∧ ρ * σ ≠ 0) ∨ SupportLE ρ σ then
      ((log2 (Qaz α z ρ σ) / (α - 1) : ℝ) : EReal)
    else ⊤

def magic {n : ℕ} (α z : ℝ) (ρ : Op n) : EReal :=
  sInf ((fun σ : Op n => Daz α z ρ σ) '' STAB n)

def claim : Prop :=
  ∀ α z : ℝ, DPI α z → |(1 - α) / z| = 1 →
  ∀ n m : ℕ, (n = 2 ∨ n = 3) → (m = 2 ∨ m = 3) →
  ∀ (ρ : Op n) (ω : Op m), IsState ρ → IsState ω →
    magic α z (tensor ρ ω) = magic α z ρ + magic α z ω

private def rho : Op 3 := (11 / 88 : ℝ) • (1 : Op 3) + (1 / 22 : ℝ) • S

private def rhoBar : Op 3 := conjugate rho

private def C : Op 3 := (49 / 66 : ℝ) • (1 : Op 3) + (17 / 66 : ℝ) • S

private def Q : ℝ := 1015 / 726

private def sigmaInv : Op 3 := (28 / 3 : ℝ) • (1 : Op 3) - (4 / 3 : ℝ) • S

private lemma source_certificate :
    (∀ (n : ℕ) (η : Op n), η ∈ STAB n → IsState η) ∧
    (IsState sigma ∧ tr (sigma * S) = 1) ∧
    Sᴴ = S ∧ S * S = (7 : ℂ) • (1 : Op 3) ∧ S.trace = 0 ∧
    (∀ η ∈ STAB 3, tr (η * S) ≤ 1 ∧ tr (η * conjugate S) ≤ 1) := by
  have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1⟩

private lemma S_square_real : S * S = (7 : ℝ) • (1 : Op 3) := by
  rw [source_certificate.2.2.2.1]
  ext i j
  simp [Algebra.smul_def]

private lemma two_coeff_mul (a b c d : ℝ) :
    ((a : ℝ) • (1 : Op 3) + b • S) * (c • 1 + d • S) =
      (a * c + 7 * b * d) • (1 : Op 3) + (a * d + b * c) • S := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, S_square_real]
  module

private def rhoInv : Op 3 := (968 / 9 : ℝ) • (1 : Op 3) - (352 / 9 : ℝ) • S

private lemma rho_inverse_certificate : rho * rhoInv = (1 : Op 3) := by
  unfold rho
  unfold rhoInv
  rw [sub_eq_add_neg]
  simp only [← neg_smul]
  rw [two_coeff_mul]
  module

private lemma rho_inverse : rho⁻¹ = rhoInv :=
  Matrix.inv_eq_right_inv rho_inverse_certificate

private lemma sigma_expanded : sigma = (1 / 8 : ℝ) • (1 : Op 3) + (1 / 56 : ℝ) • S := by
  change (1 / 56 : ℝ) • ((7 : ℝ) • (1 : Op 3) + S) = _
  simp only [smul_add, smul_smul]
  module

private lemma sigma_inverse_certificate : sigma * sigmaInv = (1 : Op 3) := by
  rw [sigma_expanded]
  unfold sigmaInv
  rw [sub_eq_add_neg]
  simp only [← neg_smul]
  rw [two_coeff_mul]
  module

private lemma C_relation : rho * sigmaInv = C := by
  unfold rho sigmaInv C
  rw [sub_eq_add_neg]
  simp only [← neg_smul]
  rw [two_coeff_mul]
  module

private lemma C_square : C * C = (1 / 4356 : ℝ) •
    ((4424 : ℝ) • (1 : Op 3) + (1666 : ℝ) • S) := by
  unfold C
  rw [two_coeff_mul]
  module

private lemma completed_square_nonnegative (η E : Op 3) (hη : η.PosDef) :
    0 ≤ tr (Eᴴ * η⁻¹ * E) := by
  have hi : η⁻¹.PosDef := hη.inv
  have hp : (Eᴴ * η⁻¹ * E).PosSemidef :=
    hi.posSemidef.conjTranspose_mul_mul_same E
  change 0 ≤ (Eᴴ * η⁻¹ * E).trace.re
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

private lemma Daz_two_one_supported {n : ℕ} (ρ σ : Op n)
    (h : SupportLE ρ σ) :
    Daz 2 1 ρ σ = ((log2 (tr (ρ * ρ * σ⁻¹)) : ℝ) : EReal) := by
  simp [Daz, h, log2]

private lemma Daz_two_one_outside {n : ℕ} (ρ σ : Op n)
    (h : ¬ SupportLE ρ σ) : Daz 2 1 ρ σ = ⊤ := by
  simp [Daz, h]

private lemma C_square_expectation_bound (η : Op 3) (hη : η ∈ STAB 3) :
    tr (η * (C * C)) ≤ Q := by
  have hs := source_certificate.1 3 η hη
  have htr : tr η = 1 := by
    exact congrArg Complex.re hs.2
  have hS := (source_certificate.2.2.2.2.2 η hη).1
  change η.trace.re = 1 at htr
  change (η * S).trace.re ≤ 1 at hS
  rw [C_square]
  unfold tr Q
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, Complex.smul_re]
  norm_num at htr hS ⊢
  nlinarith

private lemma rho_C_trace : tr (rho * C) = Q := by
  unfold rho C
  rw [two_coeff_mul]
  unfold tr Q
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    source_certificate.2.2.2.2.1]
  norm_num

private lemma sigma_C_square_trace : tr (sigma * (C * C)) = Q := by
  have hs := source_certificate.2.1
  have htr : tr sigma = 1 := by
    change sigma.trace.re = 1
    exact congrArg Complex.re hs.1.2
  rw [C_square]
  unfold tr Q
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, Complex.smul_re]
  change sigma.trace.re = 1 at htr
  have he : (sigma * S).trace.re = 1 := by
    simpa [tr] using hs.2
  norm_num at htr he ⊢
  linarith

private lemma full_rank_support_guard {n : ℕ} (ρ η : Op n)
    (hρ : ρ.PosDef) (hsing : ¬ IsUnit η) : ¬ SupportLE ρ η := by
  intro h
  have hρi : Function.Injective ρ.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hρ.isUnit
  have hi : Function.Injective η.mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hρi
    simpa only [Matrix.mulVec_zero] using
      h (x - y) (by simpa [Matrix.mulVec_sub] using (sub_eq_zero.mpr hxy))
  exact hsing (Matrix.mulVec_injective_iff_isUnit.mp hi)

private lemma rho_trace : rho.trace = 1 := by
  unfold rho
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    source_certificate.2.2.2.2.1]
  norm_num

private lemma rho_pos : rho.PosDef := by
  have h := stabilizer_polar_tensor_escape (4 / 11 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, _, _, _, hW, _, _, _, _⟩
  have he : rho = (15 / 88 : ℝ) • W (4 / 11 : ℝ) := by
    unfold rho W
    module
  rw [he]
  exact hW.smul (by norm_num)

private lemma rho_state : IsState rho := by
  exact ⟨rho_pos.posSemidef, rho_trace⟩

end D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation
