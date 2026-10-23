/- GID: D5/S3/Quantum/Measurement/LocallyPositiveSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/LocallyPositiveSpectrum
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: LocallyPositiveSpectrum supports the overlap bound. -/

/-
proof_shape: hermitian_inverse_trace: bind-only; consumer: local_psd_reciprocal_budget
escape_witness: hermitian_inverse_trace: none
Direct frozen dependencies: hermitian_inverse_trace: F7, F8, F9, F10, F11, F12, F13
proof_shape: hermForm_sub_kernel: bind-only; consumer: local_psd_kernel_eq_zero
escape_witness: hermForm_sub_kernel: none
Direct frozen dependencies: hermForm_sub_kernel: F4
proof_shape: local_psd_negIndex: content; consumer: local_psd_negative_spectrum
escape_witness: local_psd_negIndex: local_psd_negIndex
Direct frozen dependencies: local_psd_negIndex: F1, F2, F3, F4, F5, F6
proof_shape: local_psd_principal: bind-only; consumer: local_psd_adjugate_diag_nonneg
escape_witness: local_psd_principal: none
Direct frozen dependencies: local_psd_principal: F4
proof_shape: local_psd_kernel_eq_zero: content; consumer: local_psd_isUnit_det
escape_witness: local_psd_kernel_eq_zero: local_psd_kernel_eq_zero
Direct frozen dependencies: local_psd_kernel_eq_zero: F4
proof_shape: local_psd_adjugate_diag_nonneg: bind-only; consumer: local_psd_inverse_trace_nonpos
escape_witness: local_psd_adjugate_diag_nonneg: none
Direct frozen dependencies: local_psd_adjugate_diag_nonneg: F4
proof_shape: local_psd_inverse_trace_nonpos: bind-only; consumer: local_psd_reciprocal_budget
escape_witness: local_psd_inverse_trace_nonpos: none
Direct frozen dependencies: local_psd_inverse_trace_nonpos: F4, F7
proof_shape: local_psd_isUnit_det: content; consumer: local_psd_negative_spectrum
escape_witness: local_psd_isUnit_det: local_psd_isUnit_det
Direct frozen dependencies: local_psd_isUnit_det: F4
proof_shape: local_psd_negative_spectrum: content; consumer: local_psd_reciprocal_budget
escape_witness: local_psd_negative_spectrum: local_psd_negative_spectrum
Direct frozen dependencies: local_psd_negative_spectrum: F1, F2, F3, F4, F5, F6
proof_shape: local_psd_reciprocal_budget: content; consumer: spectral_balanced_pairing_nonneg
escape_witness: local_psd_reciprocal_budget: local_psd_reciprocal_budget
Direct frozen dependencies: local_psd_reciprocal_budget: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13
admission_basis: escape-witness
Frozen declaration identities:
F1: owner GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne; declaration: D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart
  baseline declaration: _private.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.0.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart
  baseline declaration statement_id: sha256:70d3c448a772227785663f0117c0f159426907edd543b564aa470d834558dd8d
  current declaration statement_id: sha256:fa2079feef1191a452c3d4dbf8a1703c836eb544be648e3d7e26f7c50d152c41
F2: owner GID: D5/S3/Weil/ZetaLinear/PoleCapacityRankOne; declaration: D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  baseline declaration: _private.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.0.D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex
  baseline declaration statement_id: sha256:e7d3fba989f8d1191d850ac68b17f943aea8d31ca3e6e460fb7f05749ab26485
  current declaration statement_id: sha256:76ab22395c4e18ba0d43115f458e8587cc482420784a2490c224e68f89700709
F3: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.PosDefOn
  declaration statement_id: sha256:9ca9d30055bd50eda8453689225e563d10cdccb3278a2b8225dc9957a0890cc7
F4: owner GID: D5/S3/Weil/ZetaLinear/Sylvester; declaration: RHLinalg.hermForm
  declaration statement_id: sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
F5: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.hermNegPart
  declaration statement_id: sha256:ad2a8390443bab24ec786ac6b42ded024195da37fd6d90578e441e73bf03e026
F6: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.negIndex
  declaration statement_id: sha256:b5905a543106ad41223ab3c0f6f31f7fb0632341c5e830350ec889bee1806429
F7: owner GID: D5/S3/Weil/ZetaLinear/PosIndex; declaration: RHLinalg.rtrace
  declaration statement_id: sha256:355bea6db8a05c6ea83567c442e2673342fec1402e04cd71a61594040520ce82
F8: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.rtrace_specMap
  declaration statement_id: sha256:efa5f0bbdc4f0443275c16da086085a95c6f4e6395761aa1fadb48ed96f8ca46
F9: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap
  declaration statement_id: sha256:e1543a97599b6cc90234c264dc99210b245061ed4d182b4351174881ce0384e7
F10: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap._proof_1
  declaration statement_id: sha256:4505c32a9d334197dcdfbfe76a2b9041ae47c40d056e290040f762933ca6facf
F11: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap._proof_2
  declaration statement_id: sha256:71a8beda364a4cfc5bb497eb18cfcd54f8c12abc40e9a37962ca4f717d42c1e5
F12: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_id
  declaration statement_id: sha256:cea0a2fff8be7382546005ffd1843b01b9d335c34dac8252010b54857733eedb
F13: owner GID: D5/S3/Weil/ZetaLinear/HermitianPosPart; declaration: RHLinalg.specMap_mul
  declaration statement_id: sha256:7676c10505b22f0e9db5f08c8be82f86e9eb4db5a663554bc93b31c13a2aa6dc
Definition rows classify unfolding; they assert no proposition and supply no escape witness.
Utility: none; finite-dimensional symbolic mathematics for arbitrary parameters.
Published owner references use the protected baseline private declaration identities.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15730.
DTR reading: DTR-Unregistered for the public theorem targets in this module.
Registration gap: exact dependent source-family reconstruction, lawful template readout,
selection coordinates, whole-family variation, slot sensitivity and observational dependence
are not all established by the retained registration evidence.
-/

import D5.S3.Quantum.Measurement.AntidistinguishabilityGram
import D5.S3.Weil.ZetaLinear.PoleCapacityRankOne

open Matrix Finset Filter Unitary
open scoped BigOperators ComplexOrder Topology RealInnerProductSpace

namespace D5.S3.Quantum.Measurement.LocallyPositiveSpectrum
noncomputable section
open D5.S3.Quantum.Measurement.AntidistinguishabilityGram

section
variable {n : ℕ}

private theorem hermitian_inverse_trace {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.IsHermitian)
    (hne : ∀ i, hY.eigenvalues i ≠ 0) :
    RHLinalg.rtrace Y⁻¹ = ∑ i, (hY.eigenvalues i)⁻¹ := by
  have hp : RHLinalg.specMap hY (fun t => t⁻¹) * Y = 1 := by
    conv_lhs => rhs; rw [← RHLinalg.specMap_id hY]
    rw [← RHLinalg.specMap_mul]
    unfold RHLinalg.specMap
    have hd : diagonal (fun i => (((hY.eigenvalues i)⁻¹ * hY.eigenvalues i : ℝ) : ℂ)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp [hne i]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    change (conjStarAlgAut ℂ _ hY.eigenvectorUnitary)
      (diagonal (fun i => (((hY.eigenvalues i)⁻¹ * hY.eigenvalues i : ℝ) : ℂ))) = 1
    rw [hd, map_one]
  rw [Matrix.inv_eq_left_inv hp, RHLinalg.rtrace_specMap]

end

section
variable {n : ℕ}

private theorem hermForm_sub_kernel (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian)
    (x v : Fin n → ℂ) (hx : Y *ᵥ x = 0) (a b : ℂ) :
    RHLinalg.hermForm Y (a • v - b • x) = ‖a‖ ^ 2 * RHLinalg.hermForm Y v := by
  have hcross : star x ⬝ᵥ (Y *ᵥ v) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← hY.eq, ← Matrix.star_mulVec, hx]
    simp
  unfold RHLinalg.hermForm
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hx, smul_zero, sub_zero,
    star_sub, star_smul, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    hcross, mul_zero, sub_zero, smul_eq_mul]
  rw [← mul_assoc, RCLike.star_def, RCLike.mul_conj]
  simp [Complex.mul_re, pow_two]

end

section
variable {n : ℕ}

theorem local_psd_negIndex (hn : 1 ≤ n)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : LocallyPsd Y) :
    RHLinalg.negIndex hY.1 ≤ 1 := by
  let W := LinearMap.range (RHLinalg.hermNegPart hY.1).mulVecLin
  have hpos : RHLinalg.PosDefOn (-Y) W := D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.negDefOn_range_hermNegPart hY.1
  have hdim : Module.finrank ℂ W = RHLinalg.negIndex hY.1 := D5.S3.Weil.ZetaLinear.PoleCapacityRankOne.rank_hermNegPart_eq_negIndex hY.1
  let j : Fin n := ⟨0, by omega⟩
  let L : W →ₗ[ℂ] ℂ := (LinearMap.proj j).comp W.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    simp only [LinearMap.mem_ker, L, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply] at hx
    have hn := hY.2 j x hx
    have hp : x=0 := by
      by_contra hne
      have hxe : (x : Fin n → ℂ) ≠ 0 := fun he => hne (Subtype.ext he)
      have hneg := hpos x x.property hxe
      simp only [RHLinalg.hermForm, Matrix.neg_mulVec, dotProduct_neg, map_neg] at hneg
      unfold RHLinalg.hermForm at hn
      linarith
    simpa [Submodule.mem_bot] using hp
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  rw [hdim] at hd
  simpa using hd

end

section
variable {n : ℕ}

private theorem local_psd_principal (Y : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hY : LocallyPsd Y) (j : Fin (n+1)) :
    (Y.submatrix j.succAbove j.succAbove).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hY.1.submatrix _, ?_⟩
  intro x
  let z : Fin (n+1) → ℂ := Fin.insertNth j 0 x
  have hz : z j=0 := by simp [z]
  have he : star z ⬝ᵥ (Y *ᵥ z) =
      star x ⬝ᵥ ((Y.submatrix j.succAbove j.succAbove) *ᵥ x) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_succAbove _ j]
    simp only [Pi.star_apply, hz, star_zero, zero_mul, zero_add]
    apply sum_congr rfl
    intro k _
    rw [Fin.sum_univ_succAbove _ j]
    simp [z, Matrix.submatrix_apply]
  have hre := hY.2 j z hz
  change 0 ≤ (star z ⬝ᵥ (Y *ᵥ z)).re at hre
  rw [he] at hre
  have him := hY.1.im_star_dotProduct_mulVec_self z
  change (star z ⬝ᵥ (Y *ᵥ z)).im=0 at him
  rw [he] at him
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

end

section
variable {n : ℕ}

theorem local_psd_kernel_eq_zero (Y : Matrix (Fin n) (Fin n) ℂ) (hY : LocallyPsd Y)
    (v : Fin n → ℂ) (hv : RHLinalg.hermForm Y v < 0)
    (x : Fin n → ℂ) (hx : Y *ᵥ x = 0) : x = 0 := by
  ext j
  have hzero : (x j • v - v j • x) j = 0 := by simp [Pi.smul_apply]; ring
  have hp := hY.2 j (x j • v - v j • x) hzero
  rw [hermForm_sub_kernel Y hY.1 x v hx] at hp
  have hn : ‖x j‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x j‖]
  simpa using (sq_eq_zero_iff.mp hn)

end

section
variable {n : ℕ}

private theorem local_psd_adjugate_diag_nonneg
    (Y : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hY : LocallyPsd Y) (j : Fin (n+1)) :
    0 ≤ (Matrix.adjugate Y j j).re := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  exact (Complex.nonneg_iff.mp (local_psd_principal Y hY j).det_nonneg).1

end

section
variable {n : ℕ}

private theorem local_psd_inverse_trace_nonpos (Y : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hY : LocallyPsd Y) (hd : Y.det.re < 0) : RHLinalg.rtrace Y⁻¹ ≤ 0 := by
  unfold LocallyPsd at hY
  have hdet : Y.det = (Y.det.re : ℂ) := by
    rw [hY.1.det_eq_prod_eigenvalues]
    change (∏ i, (hY.1.eigenvalues i : ℂ)) = (((∏ i, (hY.1.eigenvalues i : ℂ)).re) : ℂ)
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hadj : 0 ≤ (Matrix.trace (Matrix.adjugate Y)).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    exact sum_nonneg fun i _ => local_psd_adjugate_diag_nonneg Y hY i
  change (Matrix.trace Y⁻¹).re ≤ 0
  rw [Matrix.inv_def, Matrix.trace_smul, Ring.inverse_eq_inv, hdet]
  simp only [smul_eq_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hd.le) hadj

end

section
variable {n : ℕ}

private theorem local_psd_isUnit_det (Y : Matrix (Fin n) (Fin n) ℂ) (hY : LocallyPsd Y)
    (v : Fin n → ℂ) (hv : RHLinalg.hermForm Y v < 0) : IsUnit Y.det := by
  apply (Matrix.isUnit_iff_isUnit_det Y).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x z hxz
  apply sub_eq_zero.mp
  apply local_psd_kernel_eq_zero Y hY v hv
  simp only [Matrix.mulVec_sub, hxz, sub_self]

end

section
variable {n : ℕ}

private theorem local_psd_negative_spectrum (hn : 1 ≤ n)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : LocallyPsd Y)
    (p : Fin n) (hp : hY.1.eigenvalues p < 0) :
    (∀ i, hY.1.eigenvalues i ≠ 0) ∧
    (∀ i, i ≠ p → 0 < hY.1.eigenvalues i) ∧ (Y.det).re < 0 := by
  unfold LocallyPsd at hY
  have hv : RHLinalg.hermForm Y (hY.1.eigenvectorBasis p) < 0 := by
    unfold RHLinalg.hermForm
    rw [← hY.1.eigenvalues_eq p]
    exact hp
  have hu := local_psd_isUnit_det Y hY _ hv
  have hdetne := hu.ne_zero
  rw [hY.1.det_eq_prod_eigenvalues] at hdetne
  have hne : ∀ i, hY.1.eigenvalues i ≠ 0 := by
    intro i
    have hi := Finset.prod_ne_zero_iff.mp hdetne i (mem_univ i)
    intro he
    apply hi
    simp [he]
  have hcount := local_psd_negIndex hn Y hY
  change (univ.filter (fun i => hY.1.eigenvalues i < 0)).card ≤ 1 at hcount
  have hpos : ∀ i, i ≠ p → 0 < hY.1.eigenvalues i := by
    intro i hip
    by_contra! hi
    have hi' : hY.1.eigenvalues i < 0 := lt_of_le_of_ne hi (hne i)
    have heq : i=p := Finset.card_le_one.mp hcount i (by simp [hi']) p (by simp [hp])
    exact hip heq
  refine ⟨hne,hpos,?_⟩
  rw [hY.1.det_eq_prod_eigenvalues]
  change (∏ i, (hY.1.eigenvalues i : ℂ)).re < 0
  rw [← Complex.ofReal_prod, Complex.ofReal_re]
  rw [← Finset.prod_erase_mul _ _ (mem_univ p)]
  exact mul_neg_of_pos_of_neg (Finset.prod_pos fun i hi => hpos i (mem_erase.mp hi).1) hp

end

section
variable {n : ℕ}

theorem local_psd_reciprocal_budget (Y : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hY : LocallyPsd Y) (p : Fin (n+1)) (hp : hY.1.eigenvalues p < 0) :
    (∀ i, i ≠ p → 0 < hY.1.eigenvalues i) ∧
      (∑ i ∈ univ.erase p, (hY.1.eigenvalues i)⁻¹) ≤ (-hY.1.eigenvalues p)⁻¹ := by
  obtain ⟨hne,hpos,hd⟩ := local_psd_negative_spectrum (by omega) Y hY p hp
  have ht := local_psd_inverse_trace_nonpos Y hY hd
  rw [hermitian_inverse_trace hY.1 hne, ← sum_erase_add _ _ (mem_univ p)] at ht
  refine ⟨hpos,?_⟩
  rw [inv_neg]
  linarith

end

end
end D5.S3.Quantum.Measurement.LocallyPositiveSpectrum
