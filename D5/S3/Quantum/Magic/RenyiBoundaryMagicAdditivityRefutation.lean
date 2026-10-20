/- GID: D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.claim; result=D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.result; claim=D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.claim
   digest: Boundary alpha-z magic additivity is refuted by a three-qubit marginal certificate. -/
import D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
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
def log2 (x : ℝ) : ℝ := Real.logb ((2 : ℕ) : ℝ) x
def DPI (α z : ℝ) : Prop :=
  0 < z ∧ ((0 < α ∧ α < 1 ∧ max α (1 - α) ≤ z) ∨ α = 1 ∨
    (1 < α ∧ α ≤ ((2 : ℕ) : ℝ) ∧ α / ((2 : ℕ) : ℝ) ≤ z ∧ z ≤ α) ∨
    (((2 : ℕ) : ℝ) ≤ α ∧ α - 1 ≤ z ∧ z ≤ α))
private noncomputable def spectralPow {n : ℕ} (A : Op n) (x : ℝ) : Op n :=
  if h : A.IsHermitian then h.cfc (fun t => t ^ x) else 0
private noncomputable def spectralLog {n : ℕ} (A : Op n) : Op n :=
  if h : A.IsHermitian then h.cfc Real.log else 0
def Qaz {n : ℕ} (α z : ℝ) (ρ σ : Op n) : ℝ :=
  tr (spectralPow (spectralPow ρ (α / (((2 : ℕ) : ℝ) * z)) *
    spectralPow σ ((1 - α) / z) * spectralPow ρ (α / (((2 : ℕ) : ℝ) * z))) z)
def Daz {n : ℕ} (α z : ℝ) (ρ σ : Op n) : EReal := by
  classical
  exact if α = 1 then
      if SupportLE ρ σ then
        ((tr (ρ * (spectralLog ρ - spectralLog σ)) / Real.log ((2 : ℕ) : ℝ) : ℝ) : EReal)
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
    Sᴴ = S ∧ S * S = (7 : ℂ) • (1 : Op 3) ∧ S.trace = 0 := by
  have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
private lemma S_square_real : S * S = (7 : ℝ) • (1 : Op 3) := by
  rw [source_certificate.2.2.2.1]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_ofNat]
private lemma two_coeff_mul (a b c d : ℝ) :
    ((a : ℝ) • (1 : Op 3) + b • S) * (c • 1 + d • S) =
      (a * c + 7 * b * d) • (1 : Op 3) + (a * d + b * c) • S := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, S_square_real]
  module
private lemma two_coeff_hermitian (a b : ℝ) :
    (a • (1 : Op 3) + b • S).IsHermitian :=
  (Matrix.isHermitian_one.smul (IsSelfAdjoint.all a)).add
    ((show S.IsHermitian from source_certificate.2.2.1).smul (IsSelfAdjoint.all b))
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
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hp, _, _⟩
  exact (hp η hη).1
private lemma sigma_C_square_trace : tr (sigma * (C * C)) = Q := by
  have hs := source_certificate.2.1
  have htr : tr sigma = 1 := by
    change sigma.trace.re = 1
    exact congrArg Complex.re hs.1.2
  rw [C_square]
  unfold tr RHLinalg.rtrace Q
  simp only [RCLike.re_eq_complex_re]
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, Complex.smul_re]
  change sigma.trace.re = 1 at htr
  have he : (sigma * S).trace.re = 1 := by
    exact hs.2
  norm_num at htr he ⊢
  linarith
private lemma rho_C_trace : tr (rho * C) = Q := by
  have he : sigma * C = rho := by
    rw [sigma_expanded]
    unfold C rho
    rw [two_coeff_mul]
    module
  rw [← he, Matrix.mul_assoc]
  exact sigma_C_square_trace
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
  unfold tr RHLinalg.rtrace
  simp only [RCLike.re_eq_complex_re]
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
  rw [dif_pos hA, ← hA.cfc_eq]
  simpa only [Real.rpow_one] using cfc_id' ℝ A (show IsSelfAdjoint A from hA)
private lemma spectralPow_inv {n : ℕ} (A : Op n) (hA : A.PosDef) :
    spectralPow A (-1) = A⁻¹ := by
  unfold spectralPow
  rw [dif_pos hA.isHermitian, ← hA.isHermitian.cfc_eq,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.inverse_eq_rpow_neg_one hA.isStrictlyPositive,
    ← Matrix.nonsing_inv_eq_ringInverse]
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
  unfold tr RHLinalg.rtrace
  simp only [RCLike.re_eq_complex_re]
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
private lemma Daz_two_one_outside {n : ℕ} (ρ σ : Op n)
    (h : ¬ SupportLE ρ σ) : Daz 2 1 ρ σ = ⊤ := by
  unfold Daz
  norm_num [h]
private lemma C_square_expectation_bound (η : Op 3) (hη : η ∈ STAB 3) :
    tr (η * (C * C)) ≤ Q := by
  rw [actual_consumption]
  have hp := polar_consumption η hη
  have hQ : (0 : ℝ) < Q := by unfold Q; norm_num
  unfold tr RHLinalg.rtrace at hp ⊢
  simp only [RCLike.re_eq_complex_re] at hp ⊢
  simp only [Matrix.mul_smul]
  norm_num at hp ⊢
  nlinarith
private lemma rho_trace : rho.trace = 1 := by
  unfold rho
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    source_certificate.2.2.2.2]
  norm_num
private lemma rho_pos : rho.PosDef := by
  have h := stabilizer_polar_tensor_escape (4 / 11 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, _, _, hW, _, _, _, _⟩
  have he : rho = (15 / 88 : ℝ) • W (4 / 11 : ℝ) := by
    unfold rho W
    module
  rw [he]
  exact hW.smul (by norm_num)
private lemma rho_state : IsState rho := by
  exact ⟨rho_pos.posSemidef, rho_trace⟩
private lemma marginal_lower_bound (η : Op 3) (hη : η ∈ STAB 3)
    (hηp : η.PosDef) : Q ≤ tr (rho * rho * η⁻¹) := by
  have hsq := completed_square_nonnegative η (rho - η * C) hηp
  have hid := completed_square_identity rho C η hηp
    rho_pos.isHermitian (two_coeff_hermitian _ _) rho_C_trace
  have hC := C_square_expectation_bound η hη
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
    have hQ : (0 : ℝ) < Q := by unfold Q; norm_num
    unfold log2
    exact Real.logb_le_logb_of_le (by norm_num) hQ ht
  · change ((log2 Q : ℝ) : EReal) ≤ Daz 2 1 rho η
    rw [Daz_two_one_outside rho η (full_rank_support_guard rho η rho_pos hu)]
    exact le_top
private def barAlg {n : ℕ} : Op n ≃ₐ[ℝ] Op n := Complex.conjAe.mapMatrix
private lemma bar_transpose {n : ℕ} (A : Op n) (hA : A.IsHermitian) :
    conjugate A = Aᵀ := by
  change Aᴴᵀ = Aᵀ
  rw [hA]
private lemma bar_trace {n : ℕ} (A : Op n) : tr (conjugate A) = tr A := by
  unfold tr RHLinalg.rtrace conjugate
  simp only [RCLike.re_eq_complex_re]
  change (A.map (starRingEnd ℂ)).trace.re = A.trace.re
  rw [← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl
private lemma rhoBar_pos : rhoBar.PosDef := by
  have h := stabilizer_polar_tensor_escape (4 / 11 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, _, _, _, hW, _, _, _⟩
  have he : rhoBar = (15 / 88 : ℝ) • conjugate (W (4 / 11 : ℝ)) := by
    change barAlg rho = (15 / 88 : ℝ) • barAlg (W (4 / 11 : ℝ))
    rw [← map_smul]
    congr 1
    unfold rho W
    module
  rw [he]
  exact hW.smul (by norm_num)
private lemma rhoBar_state : IsState rhoBar := by
  refine ⟨rhoBar_pos.posSemidef, ?_⟩
  unfold rhoBar
  rw [bar_transpose rho rho_pos.isHermitian, Matrix.trace_transpose, rho_trace]
private lemma conjugate_marginal_lower (η : Op 3) (hη : η ∈ STAB 3)
    (hηp : η.PosDef) : Q ≤ tr (rhoBar * rhoBar * η⁻¹) := by
  have hc : C.IsHermitian := two_coeff_hermitian _ _
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
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hp, _, _⟩
  have hw := (hp η hη).2
  have hb : tr (η * (conjugate C * conjugate C)) ≤ Q := by
    rw [hcc]
    unfold tr RHLinalg.rtrace
    simp only [RCLike.re_eq_complex_re]
    simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    have hQ : 0 < Q := by unfold Q; norm_num
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
    have hQ : 0 < Q := by unfold Q; norm_num
    unfold log2
    exact Real.logb_le_logb_of_le (by norm_num) hQ ht
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
  map_one' := local_identity i
  map_mul' A B := (local_product i A B).symm
private lemma X_circuit : D5.S3.Quantum.FiniteDimensional.qubitX = gateH * gateS ^ 2 * gateH := by
  have hs := TsirelsonInequality.sqrt_two_inv_mul_self
  rw [← Real.sqrt_div_self, ← pow_two, ← one_div] at hs
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals dsimp only [gateH, gateS,
    D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
    D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2, pauliMatrix,
    D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ]
  all_goals apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]
private def singlePrep (p : Pauli) (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if p = .X then gateH else if p = .Y then gateS * gateH else 1) *
    (if b = 0 then 1 else D5.S3.Quantum.FiniteDimensional.qubitX)
private def productPrep (w : Fin 3 → Pauli) (b : Bits 3) : Op 3 :=
  tensorOp (fun i => singlePrep (w i) (b i))
private lemma productPrep_mem (w : Fin 3 → Pauli) (b : Bits 3) :
    productPrep w b ∈ Clifford 3 := by
  have hl (i : Fin 3) : localHom i (singlePrep (w i) (b i)) ∈ Clifford 3 := by
    have hh : localHom i gateH ∈ Clifford 3 :=
      Submonoid.subset_closure (Or.inl (Or.inl ⟨i, rfl⟩))
    have hs : localHom i gateS ∈ Clifford 3 :=
      Submonoid.subset_closure (Or.inl (Or.inr (Or.inl ⟨i, rfl⟩)))
    unfold singlePrep
    rw [map_mul]
    apply (Clifford 3).mul_mem
    · split_ifs
      · exact hh
      · rw [map_mul]; exact (Clifford 3).mul_mem hs hh
      · rw [map_one]; exact (Clifford 3).one_mem
    · split_ifs
      · rw [map_one]; exact (Clifford 3).one_mem
      · rw [X_circuit, map_mul, map_mul, map_pow]
        exact (Clifford 3).mul_mem ((Clifford 3).mul_mem hh ((Clifford 3).pow_mem hs 2)) hh
  have he : productPrep w b = localHom 0 (singlePrep (w 0) (b 0)) *
      localHom 1 (singlePrep (w 1) (b 1)) * localHom 2 (singlePrep (w 2) (b 2)) := by
    change tensorOp _ = localOp _ _ * localOp _ _ * localOp _ _
    unfold localOp
    rw [tensor_mul, tensor_mul]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [he]
  exact (Clifford 3).mul_mem ((Clifford 3).mul_mem (hl 0) (hl 1)) (hl 2)
private lemma singlePrep_projector (p : Pauli) (b : Fin 2) :
    singlePrep p b * Matrix.single (0 : Fin 2) 0 (1 : ℂ) * (singlePrep p b)ᴴ =
      (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if b = 0 then (1 : ℂ) else -1) • pauliMatrix (if p = .I then .Z else p)) := by
  have hs := TsirelsonInequality.sqrt_two_inv_mul_self
  rw [← Real.sqrt_div_self, ← pow_two, ← one_div] at hs
  cases p <;> fin_cases b
  all_goals ext i j; fin_cases i <;> fin_cases j
  all_goals dsimp only [singlePrep, gateS, gateH,
    D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
    D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2,
    pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
    D5.S3.Quantum.FiniteDimensional.qubitZ]
  all_goals simp only [reduceCtorEq, if_true, if_false, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
  all_goals apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]
private lemma productPrep_projector (w : Fin 3 → Pauli) (b : Bits 3) :
    productPrep w b * vacuum 3 * (productPrep w b)ᴴ =
      tensorOp (fun i => (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (if b i = 0 then (1 : ℂ) else -1) •
          pauliMatrix (if w i = .I then .Z else w i))) := by
  have hv : vacuum 3 = tensorOp (fun _ => Matrix.single (0 : Fin 2) 0 (1 : ℂ)) := by
    ext x y
    change Matrix.single (0 : Bits 3) 0 (1 : ℂ) x y = _
    simp only [Matrix.single_apply, tensorOp, Matrix.of_apply]
    simp only [Fintype.prod_boole, forall_and, ← funext_iff]
    rfl
  rw [hv]
  unfold productPrep
  rw [D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_adj]
  rw [tensor_mul, tensor_mul]
  congr 1
  funext i
  exact singlePrep_projector (w i) (b i)
private def parityBits (w : Fin 3 → Pauli) (b : Fin 2 × Fin 2) : Bits 3 :=
  ![(if w 1 = .I then 0 else b.1) + (if w 2 = .I then 0 else b.2), b.1, b.2]
set_option maxHeartbeats 2000000 in
-- The seven Pauli identities reduce four tensor projectors at a time.
private lemma halfspace_prepared (j : Fin 7) :
    (1 / 8 : ℝ) • ((1 : Op 3) + wordOp (gammaWords j)) =
      ∑ b : Fin 2 × Fin 2, (1 / 4 : ℝ) •
        (productPrep (gammaWords j) (parityBits (gammaWords j) b) * vacuum 3 *
          (productPrep (gammaWords j) (parityBits (gammaWords j) b))ᴴ) := by
  have hi := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.tensor_one
    (n := 3)
  rw [← hi]
  simp only [productPrep_projector]
  fin_cases j
  all_goals first
    | erw [show gammaWords 0 = ![.X, .I, .I] from rfl]
    | erw [show gammaWords 1 = ![.Y, .I, .I] from rfl]
    | erw [show gammaWords 2 = ![.Z, .X, .I] from rfl]
    | erw [show gammaWords 3 = ![.Z, .Y, .I] from rfl]
    | erw [show gammaWords 4 = ![.Z, .Z, .X] from rfl]
    | erw [show gammaWords 5 = ![.Z, .Z, .Y] from rfl]
    | erw [show gammaWords 6 = ![.Z, .Z, .Z] from rfl]
  all_goals ext x y
  all_goals simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    tensorOp, wordOp, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.prod_univ_succ, smul_eq_mul]
  all_goals unfold parityBits
  all_goals norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ', Matrix.cons_val_zero', Fin.add_def, reduceCtorEq,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  all_goals dsimp only [pauliMatrix]
  all_goals try simp only [Matrix.smul_apply, smul_eq_mul]
  all_goals with_unfolding_all simp only [Matrix.one_apply]
  all_goals with_unfolding_all norm_num
  all_goals split_ifs <;> ring
private lemma sigma_mem : sigma ∈ STAB 3 := by
  have hj (j : Fin 7) : (1 / 8 : ℝ) • ((1 : Op 3) + wordOp (gammaWords j)) ∈ STAB 3 := by
    rw [halfspace_prepared]
    apply (convex_convexHull ℝ (PureStabilizer 3)).sum_mem (fun _ _ => by norm_num)
      (by norm_num)
    intro b _
    exact subset_convexHull ℝ (PureStabilizer 3)
      ⟨productPrep (gammaWords j) (parityBits (gammaWords j) b), productPrep_mem _ _, rfl⟩
  have he : sigma = ∑ j : Fin 7, (1 / 7 : ℝ) •
      ((1 / 8 : ℝ) • ((1 : Op 3) + wordOp (gammaWords j))) := by
    rw [sigma_expanded]
    have hw : S = ∑ j : Fin 7, wordOp (gammaWords j) := rfl
    rw [hw]
    simp only [smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← Finset.smul_sum]
    module
  rw [he]
  exact (convex_convexHull ℝ (PureStabilizer 3)).sum_mem (fun _ _ => by norm_num)
    (by norm_num) (fun j _ => hj j)
private lemma clifford_bar {n : ℕ} {U : Op n} (hU : U ∈ Clifford n) :
    conjugate U ∈ Clifford n := by
  have ha (A : Op n) : (barAlg A)ᴴ = barAlg Aᴴ :=
    (Matrix.conjTranspose_map star (fun _ => rfl)).symm
  have hl (i : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
      barAlg (localHom i M) = localHom i (M.map star) := by
    ext x y
    change star (∏ j : Fin n, Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
      i M j (x j) (y j)) = ∏ j : Fin n,
      Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i (M.map star) j (x j) (y j)
    rw [star_prod]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j = i <;> simp [hj, Matrix.one_apply]
  have hh : gateH.map star = gateH := by
    ext i j
    change star (gateH i j) = gateH i j
    fin_cases i <;> fin_cases j
    all_goals dsimp only [gateH,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard]
    all_goals dsimp only [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2,
      pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ]
    all_goals norm_num only [Matrix.add_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero', star_mul, star_div, star_ofNat,
      star_one, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.real_smul, smul_eq_mul, mul_one, one_mul, mul_neg_one, neg_one_mul]
  have hs : gateS.map star = gateSᴴ := by
    ext i j
    change star (gateS i j) = star (gateS j i)
    congr 1
    fin_cases i <;> fin_cases j <;> rfl
  have hg : ∀ A ∈ gates n, barAlg A ∈ gates n ∪ (fun X : Op n => Xᴴ) '' gates n := by
    rintro A (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨c, t, h, rfl⟩)
    · change barAlg (localHom i gateH) ∈ _
      rw [hl, hh]; exact Or.inl (Or.inl ⟨i, rfl⟩)
    · change barAlg (localHom i gateS) ∈ _
      rw [hl, hs]
      change localOp i gateSᴴ ∈ _
      rw [← local_adjoint]
      exact Or.inr ⟨localHom i gateS, Or.inr (Or.inl ⟨i, rfl⟩), rfl⟩
    · have he : barAlg (gateCNOT c t) = gateCNOT c t := by
        ext x y; change star (if _ then (1 : ℂ) else 0) = if _ then 1 else 0
        split_ifs <;> simp
      rw [he]; exact Or.inl (Or.inr (Or.inr ⟨c, t, h, rfl⟩))
  change barAlg U ∈ Clifford n
  induction hU using Submonoid.closure_induction with
  | mem A hA =>
    apply Submonoid.subset_closure
    rcases hA with hA | ⟨B, hB, rfl⟩
    · exact hg A hA
    · dsimp only
      rw [← ha]
      rcases hg B hB with hb | ⟨D, hD, he⟩
      · exact Or.inr ⟨barAlg B, hb, rfl⟩
      · rw [← he, Matrix.conjTranspose_conjTranspose]; exact Or.inl hD
  | one => rw [map_one]; exact (Clifford n).one_mem
  | mul A B hA hB ihA ihB => rw [map_mul]; exact (Clifford n).mul_mem ihA ihB
private lemma stab_bar {n : ℕ} {A : Op n} (hA : A ∈ STAB n) : conjugate A ∈ STAB n := by
  apply convexHull_min (t := barAlg.toLinearMap ⁻¹' STAB n) ?_
    ((convex_convexHull ℝ _).linear_preimage barAlg.toLinearMap) hA
  rintro X ⟨U, hU, rfl⟩
  apply subset_convexHull ℝ (PureStabilizer n)
  refine ⟨conjugate U, clifford_bar hU, ?_⟩
  change barAlg (U * vacuum n * Uᴴ) = _
  rw [map_mul, map_mul]
  have hv : barAlg (vacuum n) = vacuum n := by
    ext x y; change star (Matrix.single (0 : Bits n) 0 (1 : ℂ) x y) =
      Matrix.single (0 : Bits n) 0 (1 : ℂ) x y
    simp only [Matrix.single_apply, apply_ite star, star_one, star_zero]
  rw [hv]
  rfl
private def tau : Op 6 := (4095 / 4096 : ℝ) • tensor sigma (conjugate sigma) +
  (1 / 4096 : ℝ) • bell
private lemma tau_mem : tau ∈ STAB 6 := by
  have hp := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  rcases hp with ⟨_, _, _, _, _, _, hb, _, _, _, _, _⟩
  exact (convex_convexHull ℝ (PureStabilizer 6))
    (stab_tensor sigma_mem (stab_bar sigma_mem)) hb
    (by norm_num) (by norm_num) (by norm_num)
private def baseFree : Op 6 := tensor sigma (conjugate sigma)
private def baseInv : Op 6 := tensor sigmaInv (conjugate sigmaInv)
private def joint : Op 6 := tensor rho rhoBar
private def jointInv : Op 6 := (4096 / 4095 : ℝ) •
  (baseInv - (9 / 37751 : ℝ) • (baseInv * bell * baseInv))
private def F : ℝ := 270853390336 / 138572892315
private lemma tensor_trace {n m : ℕ} (A : Op n) (B : Op m) :
    (tensor A B).trace = A.trace * B.trace := by
  change (∑ x : Bits (n + m), (Matrix.kronecker A B) (blocks n m x) (blocks n m x)) = _
  unfold Matrix.kronecker
  exact ((blocks n m).sum_comp (fun x => (Matrix.kroneckerMap (· * ·) A B) x x)).trans
    (Matrix.trace_kronecker A B)
private lemma base_inverse : baseFree * baseInv = (1 : Op 6) := by
  unfold baseFree baseInv
  rw [tensor_product, sigma_inverse_certificate]
  have hb : conjugate sigma * conjugate sigmaInv = (1 : Op 3) := by
    change barAlg sigma * barAlg sigmaInv = 1
    rw [← map_mul, sigma_inverse_certificate, map_one]
  rw [hb, tensor_identity]
private lemma sigma_pos : sigma.PosDef :=
  source_certificate.2.1.1.1.posDef_iff_isUnit.mpr
    (isUnit_iff_exists_inv.mpr ⟨sigmaInv, sigma_inverse_certificate⟩)
private lemma tau_pos : tau.PosDef := by
  have hb : (conjugate sigma).PosDef := by
    rw [bar_transpose sigma sigma_pos.isHermitian]
    exact sigma_pos.transpose
  have hf : baseFree.PosDef := (sigma_pos.kronecker hb).submatrix (blocks 3 3).injective
  have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨hstates, _, _, _, _, _, hbell, _, _, _, _, _⟩
  exact (hf.smul (by norm_num : (0 : ℝ) < 4095 / 4096)).add_posSemidef
    ((hstates 6 bell hbell).1.smul (by norm_num : (0 : ℝ) ≤ 1 / 4096))
private lemma bell_sandwich (A : Op 6) : bell * A * bell = (bell * A).trace • bell := by
  let v : Bits 6 → ℂ := fun x => if (blocks 3 3 x).1 = (blocks 3 3 x).2 then 1 else 0
  have hb : bell = (1 / 8 : ℂ) • Matrix.vecMulVec v v := by
    ext x y
    change (if (blocks 3 3 x).1 = (blocks 3 3 x).2 ∧
      (blocks 3 3 y).1 = (blocks 3 3 y).2 then (1 / 8 : ℂ) else 0) = (1 / 8 : ℂ) * (v x * v y)
    dsimp only [v]
    split_ifs <;> norm_num <;> tauto
  rw [hb]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul]
  rw [Matrix.vecMulVec_mul]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, Matrix.trace_vecMulVec,
    dotProduct_comm]
  simp only [smul_smul]
  congr 1
  ring
private lemma sigmaInv_hermitian : sigmaInv.IsHermitian := by
  unfold sigmaInv
  rw [sub_eq_add_neg, ← neg_smul]
  exact two_coeff_hermitian _ _
private lemma baseInv_hermitian : baseInv.IsHermitian := by
  unfold baseInv
  rw [bar_transpose sigmaInv sigmaInv_hermitian]
  change (tensor sigmaInv sigmaInvᵀ)ᴴ = tensor sigmaInv sigmaInvᵀ
  rw [tensor_star, sigmaInv_hermitian, sigmaInv_hermitian.transpose]
private lemma base_bell_trace : tr (bell * baseInv) = 896 / 9 := by
  have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, ht, _, _, _, _, _, _⟩
  unfold baseInv
  rw [ht]
  rw [sigmaInv_hermitian]
  unfold sigmaInv
  rw [sub_eq_add_neg]
  simp only [← neg_smul]
  rw [two_coeff_mul]
  unfold tr RHLinalg.rtrace
  simp only [RCLike.re_eq_complex_re]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    source_certificate.2.2.2.2]
  norm_num
private lemma base_bell_sandwich : bell * baseInv * bell = (896 / 9 : ℝ) • bell := by
  rw [bell_sandwich]
  have hb : bell.IsHermitian := by
    have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
    rcases h with ⟨hstates, _, _, _, _, _, hbell, _, _, _, _, _⟩
    exact (hstates 6 bell hbell).1.isHermitian
  have hr : ((bell * baseInv).trace.re : ℂ) = (bell * baseInv).trace :=
    Complex.ext rfl
      (D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
        bell baseInv hb baseInv_hermitian).symm
  rw [← hr]
  change ((tr (bell * baseInv) : ℝ) : ℂ) • bell = _
  rw [base_bell_trace]
  rfl
private lemma joint_inverse : tau⁻¹ = jointInv := by
  apply Matrix.inv_eq_left_inv
  have hi : baseInv * baseFree = (1 : Op 6) := mul_eq_one_comm.mp base_inverse
  have h1 : baseInv * bell * baseInv * baseFree = baseInv * bell := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one]
  have h2 : baseInv * bell * baseInv * bell = (896 / 9 : ℝ) • (baseInv * bell) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc bell,
      base_bell_sandwich, Matrix.mul_smul]
  unfold jointInv tau
  change _ * ((4095 / 4096 : ℝ) • baseFree + (1 / 4096 : ℝ) • bell) = _
  simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul,
    smul_sub, smul_smul, hi, h1, h2]
  module
private lemma joint_state : IsState joint := by
  refine ⟨(rho_pos.kronecker rhoBar_pos).posSemidef.submatrix (blocks 3 3), ?_⟩
  change (tensor rho rhoBar).trace = 1
  rw [tensor_trace, rho_state.2, rhoBar_state.2, one_mul]
private lemma joint_evaluation : tr (joint * joint * tau⁻¹) = F := by
  have hc : sigmaInv * rho = C := by
    unfold sigmaInv rho C
    rw [sub_eq_add_neg]
    simp only [← neg_smul]
    rw [two_coeff_mul]
    module
  have ht : (rho * C).trace = (Q : ℂ) := by
    unfold rho C Q
    rw [two_coeff_mul]
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      source_certificate.2.2.2.2]
    norm_num
  have hb : tr (joint * joint * baseInv) = Q ^ 2 := by
    unfold joint baseInv rhoBar
    rw [tensor_product, tensor_product, Matrix.mul_assoc, C_relation]
    have he : conjugate rho * conjugate rho * conjugate sigmaInv = conjugate (rho * C) := by
      change barAlg rho * barAlg rho * barAlg sigmaInv = barAlg (rho * C)
      rw [← map_mul, ← map_mul, Matrix.mul_assoc, C_relation]
    rw [he]
    unfold tr RHLinalg.rtrace
    simp only [RCLike.re_eq_complex_re]
    rw [tensor_trace, ht]
    change ((Q : ℂ) * ((rho * C).map (starRingEnd ℂ)).trace).re = _
    rw [← AddMonoidHom.map_trace (starRingEnd ℂ), ht]
    norm_num [Complex.star_def, pow_two]
  have hh : baseInv * (joint * joint) * baseInv = tensor (C * C) (conjugate (C * C)) := by
    unfold baseInv joint rhoBar
    rw [tensor_product, tensor_product, tensor_product]
    have he : sigmaInv * (rho * rho) * sigmaInv = C * C := by
      rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, C_relation]
    rw [he]
    change tensor (C * C) (barAlg sigmaInv * (barAlg rho * barAlg rho) * barAlg sigmaInv) = _
    rw [← map_mul, ← map_mul, ← map_mul, he]
    rfl
  have hv : tr (joint * joint * (baseInv * bell * baseInv)) =
      Q ^ 2 * (198983 / 189225 : ℝ) := by
    unfold tr RHLinalg.rtrace
    simp only [RCLike.re_eq_complex_re]
    have he : (joint * joint * (baseInv * bell * baseInv)).trace =
        (bell * (baseInv * (joint * joint) * baseInv)).trace := by
      calc
        _ = ((baseInv * bell * baseInv) * (joint * joint)).trace := Matrix.trace_mul_comm _ _
        _ = ((bell * baseInv) * (joint * joint) * baseInv).trace := by
          simpa only [Matrix.mul_assoc] using
            Matrix.trace_mul_comm baseInv ((bell * baseInv) * (joint * joint))
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [he]
    change tr (bell * (baseInv * (joint * joint) * baseInv)) = _
    rw [hh, actual_consumption]
    have hbar : conjugate (Q • W (119 / 316 : ℝ)) = Q • conjugate (W (119 / 316 : ℝ)) :=
      map_smul barAlg Q _
    rw [hbar]
    change tr (bell * (tensorRight (n := 3) (m := 3) (Q • conjugate (W (119 / 316 : ℝ)))
      (Q • W (119 / 316 : ℝ)))) = _
    rw [map_smul]
    change tr (bell * (Q • (tensorLeft (n := 3) (m := 3) (W (119 / 316 : ℝ))
      (Q • conjugate (W (119 / 316 : ℝ)))))) = _
    rw [map_smul]
    have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
    rcases h with ⟨_, _, _, _, _, _, _, _, _, _, htW, _⟩
    unfold tr RHLinalg.rtrace at htW ⊢
    simp only [RCLike.re_eq_complex_re] at htW ⊢
    simp only [smul_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    change Q * Q * (bell * tensor (W (119 / 316 : ℝ))
      (conjugate (W (119 / 316 : ℝ)))).trace.re = _
    rw [htW]
    ring
  rw [joint_inverse]
  unfold jointInv
  simp only [Matrix.mul_smul, Matrix.mul_sub]
  unfold tr RHLinalg.rtrace at hb hv ⊢
  simp only [RCLike.re_eq_complex_re] at hb hv ⊢
  simp only [Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul]
  rw [hb, hv]
  unfold Q F
  norm_num
private lemma logarithmic_gap : log2 F < log2 Q + log2 Q := by
  have h := stabilizer_polar_tensor_escape (119 / 316 : ℝ) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, he, hs⟩
  have hid : Q ^ 2 - F = (29882962855 / 120195047396424 : ℝ) *
      (tr (bell * tensor (W (119 / 316 : ℝ)) (conjugate (W (119 / 316 : ℝ)))) - 1) := by
    rw [he]
    unfold Q F
    norm_num
  have hlt : F < Q ^ 2 := sub_pos.mp (hid ▸ mul_pos (by norm_num) (sub_pos.mpr hs))
  unfold log2
  have hl := Real.logb_lt_logb (by norm_num : 1 < ((2 : ℕ) : ℝ))
    (by unfold F; norm_num : 0 < F) hlt
  rw [Real.logb_pow] at hl
  simpa only [Nat.cast_ofNat, two_mul] using hl
private lemma magic_joint_upper : magic 2 1 joint ≤ ((log2 F : ℝ) : EReal) := by
  have h : magic 2 1 joint ≤ Daz 2 1 joint tau :=
    sInf_le ⟨tau, tau_mem, rfl⟩
  rw [Daz_two_one_supported joint tau joint_state tau_pos, joint_evaluation] at h
  exact h
theorem result : ¬ claim := by
  intro h
  have ha := h 2 1 (by unfold DPI; norm_num) (by norm_num) 3 3
    (Or.inr rfl) (Or.inr rfl) rho rhoBar rho_state rhoBar_state
  have hl : ((log2 Q + log2 Q : ℝ) : EReal) ≤
      magic 2 1 rho + magic 2 1 rhoBar := by
    rw [EReal.coe_add]
    exact add_le_add magic_two_one_lower magic_conjugate_lower
  have hu := magic_joint_upper
  change magic 2 1 (tensor rho rhoBar) ≤ _ at hu
  rw [ha] at hu
  have hh : ((log2 Q + log2 Q : ℝ) : EReal) ≤ ((log2 F : ℝ) : EReal) := hl.trans hu
  exact (not_le.mpr logarithmic_gap) (EReal.coe_le_coe_iff.mp hh)
end D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation
