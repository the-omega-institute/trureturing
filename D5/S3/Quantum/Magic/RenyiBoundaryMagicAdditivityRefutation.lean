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
  exact if α = 1 then
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

private lemma actual_consumption : C * C = Q • W (119 / 316 : ℝ) := by
  unfold Q W
  rw [C_square]
  module

private lemma polar_consumption (η : Op 3) (hη : η ∈ STAB 3) :
    tr (η * W (119 / 316 : ℝ)) ≤ 1 := by
  have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hp, _, _⟩
  exact (hp η hη).1

private lemma rho_C_trace : tr (rho * C) = Q := by
  unfold rho C
  rw [two_coeff_mul]
  unfold tr Q
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    source_certificate.2.2.2.2.1]
  norm_num

private lemma completed_square_nonnegative (η E : Op 3) (hη : η.PosDef) :
    0 ≤ tr (Eᴴ * η⁻¹ * E) := by
  have hi : η⁻¹.PosDef := hη.inv
  have hp : (Eᴴ * η⁻¹ * E).PosSemidef :=
    hi.posSemidef.conjTranspose_mul_mul_same E
  change 0 ≤ (Eᴴ * η⁻¹ * E).trace.re
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

set_option linter.style.haveILetI false in
private lemma completed_square_identity (X Y η : Op 3) (hη : η.PosDef)
    (hr : Xᴴ = X) (hc : Yᴴ = Y) (ht : tr (X * Y) = Q) :
    tr ((X - η * Y)ᴴ * η⁻¹ * (X - η * Y)) =
      tr (X * X * η⁻¹) - 2 * Q + tr (η * (Y * Y)) := by
  letI := hη.isUnit.invertible
  have hi : η⁻¹ * η = (1 : Op 3) := Matrix.inv_mul_of_invertible η
  have hj : η * η⁻¹ = (1 : Op 3) := Matrix.mul_inv_of_invertible η
  unfold tr
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hr, hη.isHermitian, hc,
    Matrix.sub_mul, Matrix.mul_sub]
  simp only [Matrix.mul_assoc, hj, Matrix.mul_one]
  rw [Matrix.sub_mul]
  simp only [Matrix.mul_assoc, Matrix.trace_sub]
  rw [Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  have hrc : (X * Y).trace.re = Q := ht
  have hcr : (Y * X).trace.re = Q := by
    rw [Matrix.trace_mul_comm]
    exact hrc
  rw [← Matrix.mul_assoc η⁻¹ η Y, hi, Matrix.one_mul]
  rw [Matrix.trace_sub]
  simp only [Complex.sub_re]
  rw [hrc, hcr]
  have hcycle : (X * (η⁻¹ * X)).trace.re =
      (X * (X * η⁻¹)).trace.re := by
    rw [← Matrix.mul_assoc X η⁻¹ X, Matrix.trace_mul_cycle,
      Matrix.mul_assoc]
  have hCcycle : (Y * (η * Y)).trace.re = (η * (Y * Y)).trace.re := by
    rw [← Matrix.mul_assoc Y η Y, ← Matrix.trace_mul_cycle η Y Y,
      Matrix.mul_assoc]
  rw [hcycle, hCcycle]
  ring

private lemma spectralPow_one {n : ℕ} (A : Op n) (hA : A.IsHermitian) :
    spectralPow A 1 = A := by
  unfold spectralPow
  rw [dif_pos hA]
  unfold Matrix.IsHermitian.cfc
  simpa only [Real.rpow_one, Function.comp_def] using hA.spectral_theorem.symm

private lemma spectralPow_inv {n : ℕ} (A : Op n) (hA : A.PosDef) :
    spectralPow A (-1) = A⁻¹ := by
  unfold spectralPow
  rw [dif_pos hA.isHermitian]
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  conv_lhs => rhs; rw [hA.isHermitian.spectral_theorem]
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul]
  have hd : Matrix.diagonal (RCLike.ofReal ∘ (fun t : ℝ => t ^ (-1 : ℝ)) ∘
      hA.isHermitian.eigenvalues) *
      Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) = (1 : Op n) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Function.comp_apply]
      rw [Real.rpow_neg_one]
      norm_cast
      rw [inv_mul_cancel₀ (ne_of_gt (hA.eigenvalues_pos i))]
      rfl
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [hd, map_one]

private lemma Daz_two_one_supported {n : ℕ} (ρ η : Op n)
    (hρ : IsState ρ) (hη : η.PosDef) :
    Daz 2 1 ρ η = ((log2 (tr (ρ * ρ * η⁻¹)) : ℝ) : EReal) := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hη.isUnit
  have hs : SupportLE ρ η := by
    intro v hv
    have hv0 : v = 0 := hi (by simpa only [Matrix.mulVec_zero] using hv)
    rw [hv0, Matrix.mulVec_zero]
  have hh : (ρ * η⁻¹ * ρ).IsHermitian := by
    have hp := hη.inv.posSemidef.conjTranspose_mul_mul_same ρ
    rw [hρ.1.isHermitian] at hp
    exact hp.isHermitian
  unfold Daz Qaz
  norm_num only
  rw [if_neg (by norm_num), if_pos (Or.inr hs)]
  norm_num
  rw [spectralPow_one ρ hρ.1.isHermitian, spectralPow_inv η hη,
    spectralPow_one _ hh]
  apply congrArg log2
  unfold tr
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]

private lemma Daz_two_one_outside {n : ℕ} (ρ σ : Op n)
    (h : ¬ SupportLE ρ σ) : Daz 2 1 ρ σ = ⊤ := by
  unfold Daz
  norm_num [h]

private lemma C_square_expectation_bound (η : Op 3) (hη : η ∈ STAB 3) :
    tr (η * (C * C)) ≤ Q := by
  rw [actual_consumption]
  have hp := polar_consumption η hη
  have hQ : (0 : ℝ) < Q := by norm_num [Q]
  unfold tr at hp ⊢
  simp only [Matrix.mul_smul]
  norm_num at hp ⊢
  nlinarith

private lemma marginal_lower_bound (η : Op 3) (hη : η ∈ STAB 3)
    (hηp : η.PosDef) : Q ≤ tr (rho * rho * η⁻¹) := by
  have hsq := completed_square_nonnegative η (rho - η * C) hηp
  have hid := completed_square_identity rho C η hηp
    (by unfold rho; simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, source_certificate.2.2.1])
    (by unfold C; simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, source_certificate.2.2.1]) rho_C_trace
  have hC := C_square_expectation_bound η hη
  linarith

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

private lemma magic_two_one_lower :
    ((log2 Q : ℝ) : EReal) ≤ magic 2 1 rho := by
  apply le_sInf
  intro d hd
  rcases hd with ⟨η, hη, rfl⟩
  by_cases hu : IsUnit η
  · have hps := (source_certificate.1 3 η hη).1
    have hηp : η.PosDef :=
      (Matrix.PosSemidef.posDef_iff_isUnit hps).mpr hu
    change ((log2 Q : ℝ) : EReal) ≤ Daz 2 1 rho η
    rw [Daz_two_one_supported rho η rho_state hηp]
    apply (EReal.coe_le_coe_iff).2
    have ht := marginal_lower_bound η hη hηp
    have hQ : (0 : ℝ) < Q := by norm_num [Q]
    unfold log2
    apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).2
    exact Real.log_le_log hQ ht
  · change ((log2 Q : ℝ) : EReal) ≤ Daz 2 1 rho η
    rw [Daz_two_one_outside rho η (full_rank_support_guard rho η rho_pos hu)]
    exact le_top

private def barAlg {n : ℕ} : Op n ≃ₐ[ℝ] Op n := Complex.conjAe.mapMatrix

private lemma bar_transpose {n : ℕ} (A : Op n) (hA : A.IsHermitian) :
    conjugate A = Aᵀ := by
  change Aᴴᵀ = Aᵀ
  rw [hA]

private lemma bar_trace {n : ℕ} (A : Op n) : tr (conjugate A) = tr A := by
  unfold tr conjugate
  change (A.map (starRingEnd ℂ)).trace.re = A.trace.re
  rw [← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl

private lemma rhoBar_pos : rhoBar.PosDef := by
  unfold rhoBar
  rw [bar_transpose rho rho_pos.isHermitian]
  exact rho_pos.transpose

private lemma rhoBar_state : IsState rhoBar := by
  refine ⟨rhoBar_pos.posSemidef, ?_⟩
  unfold rhoBar
  rw [bar_transpose rho rho_pos.isHermitian, Matrix.trace_transpose, rho_trace]

private lemma conjugate_marginal_lower (η : Op 3) (hη : η ∈ STAB 3)
    (hηp : η.PosDef) : Q ≤ tr (rhoBar * rhoBar * η⁻¹) := by
  have hc : C.IsHermitian := by
    change Cᴴ = C
    unfold C
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, source_certificate.2.2.1]
  have hbc : (conjugate C).IsHermitian := by
    rw [bar_transpose C hc]
    exact hc.transpose
  have ht : tr (rhoBar * conjugate C) = Q := by
    change tr (barAlg rho * barAlg C) = Q
    rw [← map_mul]
    exact (bar_trace (rho * C)).trans rho_C_trace
  have hs := completed_square_nonnegative η (rhoBar - η * conjugate C) hηp
  have he := completed_square_identity rhoBar (conjugate C) η hηp
    rhoBar_pos.isHermitian hbc ht
  have hcc : conjugate C * conjugate C = Q • conjugate (W (119 / 316 : ℝ)) := by
    change barAlg C * barAlg C = Q • barAlg (W (119 / 316 : ℝ))
    rw [← map_mul, actual_consumption, map_smul]
  have hp := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, hp, _, _⟩
  have hw := (hp η hη).2
  have hb : tr (η * (conjugate C * conjugate C)) ≤ Q := by
    rw [hcc]
    unfold tr
    simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    have hQ : 0 < Q := by norm_num [Q]
    exact (mul_le_mul_of_nonneg_left hw hQ.le).trans_eq (mul_one Q)
  linarith

private lemma magic_conjugate_lower :
    ((log2 Q : ℝ) : EReal) ≤ magic 2 1 rhoBar := by
  apply le_sInf
  rintro d ⟨η, hη, rfl⟩
  by_cases hu : IsUnit η
  · have hηp := (source_certificate.1 3 η hη).1.posDef_iff_isUnit.mpr hu
    change ((log2 Q : ℝ) : EReal) ≤ Daz 2 1 rhoBar η
    rw [Daz_two_one_supported rhoBar η rhoBar_state hηp]
    apply EReal.coe_le_coe_iff.mpr
    have ht := conjugate_marginal_lower η hη hηp
    have hQ : 0 < Q := by norm_num [Q]
    unfold log2
    exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr
      (Real.log_le_log hQ ht)
  · change ((log2 Q : ℝ) : EReal) ≤ Daz 2 1 rhoBar η
    rw [Daz_two_one_outside rhoBar η
      (full_rank_support_guard rhoBar η rhoBar_pos hu)]
    exact le_top

end D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation
