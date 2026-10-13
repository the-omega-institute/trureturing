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
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix tensorOp wordOp localOp tensor_mul)

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

private def blocks (n m : ℕ) : Bits (n + m) ≃ Bits n × Bits m :=
  (Fin.appendEquiv n m).symm

private lemma tensor_product {n m : ℕ} (A C : Op n) (B D : Op m) :
    tensor A B * tensor C D = tensor (A * C) (B * D) := by
  change (Matrix.kronecker A B).submatrix (blocks n m) (blocks n m) *
    (Matrix.kronecker C D).submatrix (blocks n m) (blocks n m) = _
  rw [Matrix.submatrix_mul_equiv]
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul]
  rfl

private lemma tensor_identity (n m : ℕ) : tensor (1 : Op n) (1 : Op m) = 1 := by
  change (Matrix.kronecker (1 : Op n) (1 : Op m)).submatrix (blocks n m) (blocks n m) = _
  unfold Matrix.kronecker
  rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

private lemma tensor_star {n m : ℕ} (A : Op n) (B : Op m) :
    (tensor A B)ᴴ = tensor Aᴴ Bᴴ := by
  unfold tensor
  unfold Matrix.kronecker
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

private def tensorLeft {n m : ℕ} (A : Op n) : Op m →ₗ[ℝ] Op (n + m) where
  toFun := tensor A
  map_add' B D := by unfold tensor Matrix.kronecker; rw [Matrix.kronecker_add]; rfl
  map_smul' r B := by unfold tensor Matrix.kronecker; rw [Matrix.kronecker_smul]; rfl

private def tensorRight {n m : ℕ} (B : Op m) : Op n →ₗ[ℝ] Op (n + m) where
  toFun := fun A => tensor A B
  map_add' A C := by unfold tensor Matrix.kronecker; rw [Matrix.add_kronecker]; rfl
  map_smul' r A := by unfold tensor Matrix.kronecker; rw [Matrix.smul_kronecker]; rfl

private lemma tensor_local_left {n m : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensor (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i A)
      (1 : Op m) =
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp
        (Fin.castAdd m i) A := by
  unfold tensor localOp
  ext x y
  dsimp only [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    tensorOp, Matrix.of_apply]
  have hdis : ∀ j : Fin m, Fin.natAdd n j ≠ Fin.castAdd m i := by
    intro j h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  change (∏ j : Fin n, Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i A j
    (x (Fin.castAdd m j)) (y (Fin.castAdd m j))) *
    (1 : Op m) (fun j => x (Fin.natAdd n j)) (fun j => y (Fin.natAdd n j)) = _
  rw [Fin.prod_univ_add]
  simp [Function.update_apply, hdis, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

private lemma tensor_local_right {n m : ℕ} (i : Fin m) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensor (1 : Op n)
      (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i A) =
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp
        (Fin.natAdd n i) A := by
  unfold tensor localOp
  ext x y
  dsimp only [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    tensorOp, Matrix.of_apply]
  have hdis : ∀ j : Fin n, Fin.castAdd m j ≠ Fin.natAdd n i := by
    intro j h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  change (1 : Op n) (fun j => x (Fin.castAdd m j)) (fun j => y (Fin.castAdd m j)) *
    (∏ j : Fin m, Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i A j
      (x (Fin.natAdd n j)) (y (Fin.natAdd n j))) = _
  rw [Fin.prod_univ_add]
  simp [Function.update_apply, hdis, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

private lemma tensor_cnot_left {n m : ℕ} (c t : Fin n) :
    tensor (gateCNOT c t) (1 : Op m) = gateCNOT (Fin.castAdd m c) (Fin.castAdd m t) := by
  ext x y
  have he : x = Function.update y (Fin.castAdd m t) (y (Fin.castAdd m t) +
      y (Fin.castAdd m c)) ↔
      (blocks n m x).1 = Function.update (blocks n m y).1 t
        ((blocks n m y).1 t + (blocks n m y).1 c) ∧
      (blocks n m x).2 = (blocks n m y).2 := by
    have hp : blocks n m (Function.update y (Fin.castAdd m t)
        (y (Fin.castAdd m t) + y (Fin.castAdd m c))) =
        (Function.update (blocks n m y).1 t
          ((blocks n m y).1 t + (blocks n m y).1 c), (blocks n m y).2) := by
      apply Prod.ext
      · funext i
        change Function.update y (Fin.castAdd m t) _ (Fin.castAdd m i) = _
        simp only [Function.update_apply, Fin.castAdd_inj]
        rfl
      · funext i
        have hd : Fin.natAdd n i ≠ Fin.castAdd m t := by
          intro h; have hv := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv; omega
        exact Function.update_of_ne hd _ _
    rw [← (blocks n m).injective.eq_iff, hp, Prod.ext_iff]
  change (if (blocks n m x).1 = Function.update (blocks n m y).1 t
      ((blocks n m y).1 t + (blocks n m y).1 c) then (1 : ℂ) else 0) *
    (if (blocks n m x).2 = (blocks n m y).2 then 1 else 0) =
    if x = Function.update y (Fin.castAdd m t)
      (y (Fin.castAdd m t) + y (Fin.castAdd m c)) then 1 else 0
  simp only [he]
  split_ifs <;> simp_all

private lemma tensor_cnot_right {n m : ℕ} (c t : Fin m) :
    tensor (1 : Op n) (gateCNOT c t) = gateCNOT (Fin.natAdd n c) (Fin.natAdd n t) := by
  ext x y
  have he : x = Function.update y (Fin.natAdd n t) (y (Fin.natAdd n t) +
      y (Fin.natAdd n c)) ↔
      (blocks n m x).1 = (blocks n m y).1 ∧
      (blocks n m x).2 = Function.update (blocks n m y).2 t
        ((blocks n m y).2 t + (blocks n m y).2 c) := by
    have hp : blocks n m (Function.update y (Fin.natAdd n t)
        (y (Fin.natAdd n t) + y (Fin.natAdd n c))) =
        ((blocks n m y).1, Function.update (blocks n m y).2 t
          ((blocks n m y).2 t + (blocks n m y).2 c)) := by
      apply Prod.ext
      · funext i
        have hd : Fin.castAdd m i ≠ Fin.natAdd n t := by
          intro h; have hv := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv; omega
        exact Function.update_of_ne hd _ _
      · funext i
        change Function.update y (Fin.natAdd n t) _ (Fin.natAdd n i) = _
        simp only [Function.update_apply, Fin.natAdd_inj]
        rfl
    rw [← (blocks n m).injective.eq_iff, hp, Prod.ext_iff]
  change (if (blocks n m x).1 = (blocks n m y).1 then (1 : ℂ) else 0) *
    (if (blocks n m x).2 = Function.update (blocks n m y).2 t
      ((blocks n m y).2 t + (blocks n m y).2 c) then 1 else 0) =
    if x = Function.update y (Fin.natAdd n t)
      (y (Fin.natAdd n t) + y (Fin.natAdd n c)) then 1 else 0
  simp only [he]
  split_ifs <;> simp_all

private lemma block_clifford {n m : ℕ} {U : Op n} {V : Op m}
    (hU : U ∈ Clifford n) (hV : V ∈ Clifford m) : tensor U V ∈ Clifford (n + m) := by
  have hl : ∀ A ∈ Clifford n, tensor A (1 : Op m) ∈ Clifford (n + m) := by
    intro A hA
    have hg : ∀ X ∈ gates n, tensor X (1 : Op m) ∈ gates (n + m) := by
      rintro X (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨c, t, h, rfl⟩)
      · rw [tensor_local_left]; exact Or.inl ⟨_, rfl⟩
      · rw [tensor_local_left]; exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [tensor_cnot_left]
        exact Or.inr (Or.inr ⟨_, _, fun e => h (Fin.castAdd_inj.mp e), rfl⟩)
    induction hA using Submonoid.closure_induction with
    | mem X hX =>
      apply Submonoid.subset_closure
      rcases hX with hX | ⟨Y, hY, rfl⟩
      · exact Or.inl (hg X hX)
      · exact Or.inr ⟨tensor Y (1 : Op m), hg Y hY,
          by dsimp only; rw [tensor_star, Matrix.conjTranspose_one]⟩
    | one => rw [tensor_identity]; exact (Clifford (n + m)).one_mem
    | mul X Y hX hY ihX ihY =>
      have ht := (Clifford (n + m)).mul_mem ihX ihY
      rwa [tensor_product, Matrix.one_mul] at ht
  have hr : ∀ B ∈ Clifford m, tensor (1 : Op n) B ∈ Clifford (n + m) := by
    intro B hB
    have hg : ∀ X ∈ gates m, tensor (1 : Op n) X ∈ gates (n + m) := by
      rintro X (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨c, t, h, rfl⟩)
      · rw [tensor_local_right]; exact Or.inl ⟨_, rfl⟩
      · rw [tensor_local_right]; exact Or.inr (Or.inl ⟨_, rfl⟩)
      · rw [tensor_cnot_right]
        exact Or.inr (Or.inr ⟨_, _, fun e => h (by simpa only [Fin.natAdd_inj] using e), rfl⟩)
    induction hB using Submonoid.closure_induction with
    | mem X hX =>
      apply Submonoid.subset_closure
      rcases hX with hX | ⟨Y, hY, rfl⟩
      · exact Or.inl (hg X hX)
      · exact Or.inr ⟨tensor (1 : Op n) Y, hg Y hY,
          by dsimp only; rw [tensor_star, Matrix.conjTranspose_one]⟩
    | one => rw [tensor_identity]; exact (Clifford (n + m)).one_mem
    | mul X Y hX hY ihX ihY =>
      have ht := (Clifford (n + m)).mul_mem ihX ihY
      rwa [tensor_product, Matrix.one_mul] at ht
  have ht := (Clifford (n + m)).mul_mem (hl U hU) (hr V hV)
  rwa [tensor_product, Matrix.mul_one, Matrix.one_mul] at ht

private lemma tensor_vacuum (n m : ℕ) : tensor (vacuum n) (vacuum m) = vacuum (n + m) := by
  change (Matrix.kronecker (Matrix.single (0 : Bits n) 0 (1 : ℂ))
    (Matrix.single (0 : Bits m) 0 (1 : ℂ))).submatrix (blocks n m) (blocks n m) =
    Matrix.single (0 : Bits (n + m)) 0 (1 : ℂ)
  unfold Matrix.kronecker
  rw [Matrix.single_kronecker_single]
  ext x y
  have hz : ((0 : Bits n), (0 : Bits m)) = blocks n m 0 := rfl
  simp only [Matrix.submatrix_apply, Matrix.single_apply, one_mul, hz,
    (blocks n m).injective.eq_iff]

private lemma stab_tensor {n m : ℕ} {A : Op n} {B : Op m}
    (hA : A ∈ STAB n) (hB : B ∈ STAB m) : tensor A B ∈ STAB (n + m) := by
  have hp : ∀ X ∈ PureStabilizer n, ∀ Y ∈ PureStabilizer m,
      tensor X Y ∈ STAB (n + m) := by
    rintro X ⟨U, hU, rfl⟩ Y ⟨V, hV, rfl⟩
    apply subset_convexHull ℝ (PureStabilizer (n + m))
    refine ⟨tensor U V, block_clifford hU hV, ?_⟩
    rw [tensor_star, ← tensor_vacuum, tensor_product, tensor_product]
  have hy : ∀ X ∈ PureStabilizer n, ∀ Y ∈ STAB m, tensor X Y ∈ STAB (n + m) := by
    intro X hX
    exact convexHull_min (hp X hX)
      ((convex_convexHull ℝ _).linear_preimage (tensorLeft X))
  exact convexHull_min (fun X hX => hy X hX B hB)
    ((convex_convexHull ℝ _).linear_preimage (tensorRight B)) hA

private def localHom {n : ℕ} (i : Fin n) : Matrix (Fin 2) (Fin 2) ℂ →* Op n where
  toFun := localOp i
  map_one' := by
    unfold localOp
    rw [Function.update_eq_self_iff.mpr rfl]
    exact D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.tensor_one
  map_mul' A B := by
    unfold localOp
    rw [tensor_mul]
    congr 1
    funext j
    by_cases h : j = i <;> simp [h]


end D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation
