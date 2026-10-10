/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Block-positive Frobenius control yields the Gurvits--Barnum separable ball. -/

import D5.S3.Resource.EntanglementWitnessExists
import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Resource.SeparableConeResidualWitness
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments

open Matrix Finset Complex
open scoped ComplexConjugate ComplexOrder Matrix.Norms.Frobenius
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
noncomputable section
set_option autoImplicit false

private theorem hermitian_trace_sq {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℂ) (hC : C.IsHermitian) :
    (trace (C * C)).re = ∑ i, ∑ j, ‖C i j‖ ^ 2 := by
  classical
  have h := D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace C
  rw [hC.eq] at h
  rw [← h]
  change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (C i))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2]

private theorem psd_trace_sq {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℂ) (hC : C.PosSemidef) :
    (trace (C * C)).re ≤ ((trace C).re) ^ 2 := by
  classical
  have ht : trace (C * C) = ∑ i, ((hC.1.eigenvalues i : ℂ) ^ 2) := by
    conv_lhs => rw [hC.1.spectral_theorem]
    rw [← map_mul]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    simp [diagonal_mul_diagonal, pow_two]
  rw [ht, hC.1.trace_eq_sum_eigenvalues]
  simpa [pow_two, Complex.mul_re] using
    sum_sq_le_sq_sum_of_nonneg (s := univ) (fun i _ => hC.eigenvalues_nonneg i)

private theorem sum_interleave {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ι → κ → κ → ℂ) :
    (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j := by
  calc
    _ = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j := by
      apply sum_congr rfl; intro a _; rw [sum_comm]
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro a _
      rw [sum_comm]

open D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
open D5.S3.Resource.CompositeCones
open D5.S3.Quantum.Information.PartialTraceMutualInformation
variable {m n : ℕ}

private def compress (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (z : Fin m → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun a b => quadratic (fun i j => H (i, a) (j, b)) z

private theorem compress_hermitian
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hH : H.IsHermitian) (z : Fin m → ℂ) :
    (compress H z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [compress, quadratic, star_sum, star_mul, starRingEnd_apply, star_star]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  rw [hH.apply (i, a) (j, b)]
  ring

private theorem compress_form
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (z : Fin m → ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((compress H z) *ᵥ y) =
      star (fun p : Fin m × Fin n => z p.1 * y p.2) ⬝ᵥ
        (H *ᵥ (fun p : Fin m × Fin n => z p.1 * y p.2)) := by
  simp only [dotProduct, mulVec, compress, quadratic, Pi.star_apply, star_mul,
    Fintype.sum_prod_type, sum_mul, mul_sum, starRingEnd_apply]
  rw [sum_interleave]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro b _
  ring

private theorem compress_psd
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hH : H.IsHermitian)
    (hpos : blockPositive H) (z : Fin m → ℂ) : (compress H z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (compress_hermitian H hH z)
  intro y
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [compress_form]
    exact hpos z y
  · exact (compress_hermitian H hH z).im_star_dotProduct_mulVec_self y |>.symm

private theorem trace_compress
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (z : Fin m → ℂ) :
    trace (compress H z) = quadratic (partialTraceRight H) z := by
  simp only [trace, diag_apply, compress, quadratic, partialTraceRight, mul_sum]
  calc
    _ = ∑ i, ∑ a, ∑ j, conj (z i) * z j * H (i, a) (j, a) := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl; intro i _; rw [sum_comm]

private theorem design_trace_square
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    designSum (fun z => trace (compress H z) * trace (compress H z)) =
      (4 : ℂ) ^ m * (trace H * trace H + trace (partialTraceRight H * partialTraceRight H)) := by
  simp_rw [trace_compress, quadratic_product_sum, trace_partialTraceRight]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem design_trace_product
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    designSum (fun z => trace (compress H z * compress H z)) =
      (4 : ℂ) ^ m * (trace (partialTraceLeft H * partialTraceLeft H) + trace (H * H)) := by
  simp only [trace, diag_apply, mul_apply, compress]
  simp_rw [designSum_sum, quadratic_product_sum]
  simp only [trace, diag_apply, sum_add_distrib, mul_add, ← mul_sum]
  congr 1
  congr 1
  simpa only [Fintype.sum_prod_type] using
    sum_interleave (fun a b i j => H (i, a) (j, b) * H (j, b) (i, a))

private theorem averaged_psd_bound
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hH : H.IsHermitian)
    (hpos : blockPositive H) :
    (trace (partialTraceLeft H * partialTraceLeft H)).re + (trace (H * H)).re ≤
      (trace H * trace H).re + (trace (partialTraceRight H * partialTraceRight H)).re := by
  have h := re_designSum_mono
    (fun z => trace (compress H z * compress H z))
    (fun z => trace (compress H z) * trace (compress H z)) (fun z => by
      have hp := compress_psd H hH hpos z
      have him := (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm
      simpa [Complex.mul_re, him, pow_two] using psd_trace_sq _ hp)
  rw [design_trace_product, design_trace_square] at h
  have hc : (4 : ℂ) ^ m = Complex.ofReal ((4 : ℝ) ^ m) := by simp
  rw [hc] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re] at h
  exact (mul_le_mul_iff_right₀ (pow_pos (show (0 : ℝ) < 4 by norm_num) m)).mp h

private def flip (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  H.submatrix Prod.swap Prod.swap

private theorem flip_blockPositive
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hpos : blockPositive H) :
    blockPositive (flip H) := by
  intro z y
  have heq : star (fun p : Fin n × Fin m => z p.1 * y p.2) ⬝ᵥ
      (flip H *ᵥ (fun p : Fin n × Fin m => z p.1 * y p.2)) =
      star (fun p : Fin m × Fin n => y p.1 * z p.2) ⬝ᵥ
      (H *ᵥ (fun p : Fin m × Fin n => y p.1 * z p.2)) := by
    simp only [flip, submatrix_apply, dotProduct, mulVec, Pi.star_apply,
      star_mul, Fintype.sum_prod_type, mul_sum, Prod.swap_prod_mk]
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro a _
    rw [sum_comm]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro b _
    ring
  change 0 ≤ Complex.re _
  rw [heq]
  exact hpos y z

private theorem trace_flip
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : trace (flip H) = trace H := by
  simp only [trace, diag_apply, flip, submatrix_apply, Fintype.sum_prod_type, Prod.swap_prod_mk]
  rw [sum_comm]

private theorem trace_flip_square
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    trace (flip H * flip H) = trace (H * H) := by
  change trace (H.submatrix Prod.swap Prod.swap * H.submatrix Prod.swap Prod.swap) = _
  have he := Matrix.submatrix_mul_equiv H H Prod.swap (Equiv.prodComm _ _) Prod.swap
  simp only [Equiv.coe_prodComm] at he
  rw [he]
  exact trace_flip (H * H)

/-- A Hermitian block-positive bipartite matrix has nonnegative trace and its
squared Frobenius sum is at most the square of its real trace. -/
theorem frobSq_le_trace_sq_of_blockPositive
    (H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hH : H.IsHermitian)
    (hpos : blockPositive H) :
    0 ≤ (trace H).re ∧ (∑ u, ∑ v, ‖H u v‖ ^ 2) ≤ ((trace H).re) ^ 2 := by
  have ht : 0 ≤ (trace H).re := by
    simp only [trace, diag_apply, Complex.re_sum]
    apply sum_nonneg
    rintro ⟨i, a⟩ _
    have h := hpos (Pi.single i 1) (Pi.single a 1)
    have hx : (fun p : Fin m × Fin n =>
        (Pi.single i 1 : Fin m → ℂ) p.1 * (Pi.single a 1 : Fin n → ℂ) p.2) =
        Pi.single (i, a) 1 := by
      ext ⟨j, b⟩
      simp only [Pi.single_apply]
      split_ifs <;> simp_all
    change 0 ≤ Complex.re _ at h
    rw [hx] at h
    have hq : star (Pi.single (i, a) (1 : ℂ)) ⬝ᵥ (H *ᵥ Pi.single (i, a) 1) =
        H (i, a) (i, a) := by
      simp [dotProduct, mulVec, Pi.single_apply]
    rwa [hq] at h
  refine ⟨ht, ?_⟩
  have h₁ := averaged_psd_bound H hH hpos
  have h₂ := averaged_psd_bound (flip H) (hH.submatrix Prod.swap) (flip_blockPositive H hpos)
  have hA : partialTraceLeft (flip H) = partialTraceRight H := rfl
  have hB : partialTraceRight (flip H) = partialTraceLeft H := rfl
  rw [hA, hB, trace_flip, trace_flip_square] at h₂
  have him : (trace H).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    change star (trace H) = trace H
    rw [← trace_conjTranspose, hH.eq]
  rw [Complex.mul_re, him, mul_zero, sub_zero] at h₁ h₂
  rw [← hermitian_trace_sq H hH]
  nlinarith [h₁, h₂]

#print axioms frobSq_le_trace_sq_of_blockPositive
open D5.S3.Resource.CompositeConeDuality
open D5.S3.Resource.EntanglementWitnessExists
open D5.S3.Resource.SeparableConeResidualWitness

private theorem entry_frob
    (R : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    ‖entryEquiv R‖ ^ 2 = ∑ u, ∑ v, ‖R u v‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

private theorem pairing_cauchy
    (S T : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (pairing S T) ^ 2 ≤ (∑ u, ∑ v, ‖S u v‖ ^ 2) * (∑ u, ∑ v, ‖T u v‖ ^ 2) := by
  have h := real_inner_mul_inner_self_le (entryEquiv S) (entryEquiv T)
  rw [entry_inner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    entry_frob, entry_frob] at h
  simpa only [pow_two] using h

private def hermitianPart
    (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  (realPart W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)

private theorem hermitianPart_hermitian
    (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : (hermitianPart W).IsHermitian :=
  (realPart W).property.isHermitian

private theorem quadratic_adjoint {ι : Type*} [Fintype ι]
    (W : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ (Wᴴ *ᵥ x) = star (star x ⬝ᵥ (W *ᵥ x)) := by
  rw [mulVec_conjTranspose, dotProduct_star, star_star, ← dotProduct_mulVec]

private theorem hermitianPart_quadratic
    (W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (x : Fin m × Fin n → ℂ) :
    (star x ⬝ᵥ (hermitianPart W *ᵥ x)).re = (star x ⬝ᵥ (W *ᵥ x)).re := by
  simp only [hermitianPart, realPart_apply_coe, Matrix.star_eq_conjTranspose,
    smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add]
  rw [quadratic_adjoint]
  norm_num [Complex.mul_re]
  ring

private theorem hermitianPart_pairing
    (R W : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hR : R.IsHermitian) :
    pairing R (hermitianPart W) = pairing R W := by
  have hAdj : pairing R Wᴴ = pairing R W := by
    unfold pairing
    change (trace (Rᴴ * Wᴴ)).re = (trace (Rᴴ * W)).re
    rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose]
    simp only [Complex.star_def, Complex.conj_re]
    rw [Matrix.trace_mul_comm, hR.eq]
  unfold pairing at hAdj ⊢
  change (trace (Rᴴ * hermitianPart W)).re = (trace (Rᴴ * W)).re
  simp only [hermitianPart, realPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add]
  norm_num [Complex.mul_re]
  change (trace (Rᴴ * Wᴴ)).re = (trace (Rᴴ * W)).re at hAdj
  rw [hAdj]
  ring

private theorem pairing_ball_center
    (R H : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (c : ℝ) :
    pairing R H = c * (trace H).re + pairing (R - (c : ℂ) • 1) H := by
  unfold pairing
  change (trace (Rᴴ * H)).re = c * (trace H).re +
    (trace ((R - (c : ℂ) • 1)ᴴ * H)).re
  simp [conjTranspose_sub, conjTranspose_smul, sub_mul, trace_sub,
    trace_smul, Complex.mul_re]

/-- Every PSD matrix in the Frobenius ball of radius c about c times the identity
belongs to the finite-sum separable cone, including c = 0. -/
theorem separableCone_of_frob_ball
    (R : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hR : R.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c)
    (hball : (∑ u, ∑ v, ‖(R - (c : ℂ) • 1) u v‖ ^ 2) ≤ c ^ 2) : separableCone R := by
  by_contra hnot
  obtain ⟨W, hW, hneg⟩ := exists_entanglementWitness R hR hnot
  let H := hermitianPart W
  have hH : H.IsHermitian := hermitianPart_hermitian W
  have hHp : blockPositive H := by
    intro a b
    change 0 ≤ Complex.re _
    rw [hermitianPart_quadratic]
    exact hW a b
  have hnegH : pairing R H < 0 := by
    rw [show H = hermitianPart W from rfl, hermitianPart_pairing R W hR.isHermitian]
    exact hneg
  obtain ⟨ht, hnorm⟩ := frobSq_le_trace_sq_of_blockPositive H hH hHp
  have hcs := pairing_cauchy (R - (c : ℂ) • 1) H
  have hprod := mul_le_mul hball hnorm (sum_nonneg (fun u _ =>
    sum_nonneg (fun v _ => sq_nonneg ‖H u v‖))) (sq_nonneg c)
  have hbound : (pairing (R - (c : ℂ) • 1) H) ^ 2 ≤ (c * (trace H).re) ^ 2 := by
    calc
      _ ≤ _ := hcs
      _ ≤ c ^ 2 * ((trace H).re) ^ 2 := hprod
      _ = _ := by ring
  have hlower : -(c * (trace H).re) ≤ pairing (R - (c : ℂ) • 1) H := by
    have habs := (sq_le_sq).mp hbound
    have habs' : |pairing (R - (c : ℂ) • 1) H| ≤ c * (trace H).re := by
      simpa only [abs_of_nonneg (mul_nonneg hc ht)] using habs
    exact (abs_le.mp habs').1
  rw [pairing_ball_center R H c] at hnegH
  linarith

#print axioms separableCone_of_frob_ball
open scoped MatrixOrder

/-- The complement of every unit rank-one projector is separable. This is the
codimension-one projection interface for the spectral ray decomposition. -/
theorem separableCone_one_sub_rankOne
    (ψ : Fin m × Fin n → ℂ) (hψ : (∑ u, ‖ψ u‖ ^ 2) = 1) :
    separableCone (1 - vecMulVec ψ (star ψ)) := by
  let P := vecMulVec ψ (star ψ)
  have hdot : star ψ ⬝ᵥ ψ = 1 := by
    let x : EuclideanSpace ℂ (Fin m × Fin n) := WithLp.toLp 2 ψ
    have hn : ‖x‖ ^ 2 = 1 := by
      simpa only [x, PiLp.norm_sq_eq_of_L2] using hψ
    have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
    rw [← RCLike.ofReal_pow, hn, RCLike.ofReal_one] at hi
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, x, WithLp.ofLp_toLp,
      dotProduct_comm] using hi
  have hP : P.IsHermitian := (posSemidef_vecMulVec_self_star ψ).isHermitian
  have hP₂ : P * P = P := by simp [P, vecMulVec_mul_vecMulVec, hdot]
  have hPtr : trace P = 1 := by
    simp only [P, trace_vecMulVec, dotProduct_comm ψ, hdot]
  have hproj : IsStarProjection P := ⟨hP₂, hP.isSelfAdjoint⟩
  have hR : (1 - P).PosSemidef := hproj.one_sub_nonneg.posSemidef
  apply separableCone_of_frob_ball (1 - P) hR 1 (by norm_num)
  have hF : (∑ u, ∑ v, ‖P u v‖ ^ 2) = 1 := by
    rw [← hermitian_trace_sq P hP, hP₂, hPtr]
    norm_num
  have hE : (1 - P) - 1 = -P := by abel
  simpa [hE] using hF.le

/-- A projection of real trace ell at least one gives a separable high-rank ray.
The real parameter also admits integer ranks by coercion. -/
theorem separableCone_scaled_one_sub_two_projection
    (Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hQ : Q.IsHermitian)
    (hQ₂ : Q * Q = Q) (ℓ : ℝ) (htr : trace Q = (ℓ : ℂ)) (hℓ : 1 ≤ ℓ) :
    separableCone (((ℓ : ℂ) + 1) • 1 - (2 : ℂ) • Q) := by
  have hproj : IsStarProjection Q := ⟨hQ₂, hQ.isSelfAdjoint⟩
  have hsub : (1 - Q).PosSemidef := hproj.one_sub_nonneg.posSemidef
  have hX : (((ℓ : ℂ) + 1) • 1 - (2 : ℂ) • Q).PosSemidef := by
    have h := (Matrix.PosSemidef.one (n := Fin m × Fin n) (R := ℂ)).smul
      (show (0 : ℝ) ≤ ℓ - 1 by linarith)
    have h' := hsub.smul (show (0 : ℝ) ≤ 2 by norm_num)
    have hid : (((ℓ : ℂ) + 1) • 1 - (2 : ℂ) • Q) =
        (ℓ - 1) • (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) +
          (2 : ℝ) • (1 - Q) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    rw [hid]
    exact h.add h'
  apply separableCone_of_frob_ball _ hX (ℓ + 1) (by linarith)
  have hE : (((ℓ : ℂ) + 1) • 1 - (2 : ℂ) • Q) - ((ℓ+1:ℝ):ℂ) • 1 =
      -(2 : ℂ) • Q := by
    push_cast
    module
  rw [hE]
  have hnorm : (∑ u, ∑ v, ‖(-(2 : ℂ) • Q) u v‖ ^ 2) = 4 * ℓ := by
    simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_neg, Complex.norm_ofNat,
      mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← mul_sum]
    rw [← hermitian_trace_sq Q hQ, hQ₂, htr]
    simp
  rw [hnorm]
  nlinarith [sq_nonneg (ℓ - 1)]

#print axioms separableCone_one_sub_rankOne
#print axioms separableCone_scaled_one_sub_two_projection
end
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
