/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Generalized Choi maps cannot detect entanglement in absolutely PPT qutrit states. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN3PurityBound
import D5.S3.Quantum.Matrix.CartesianVariance

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 64000000
set_option maxRecDepth 32768

noncomputable section
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.GeneralizedChoiNonDetection
open QutritPerturbationAttainment (APPT)

def choiGen (b c : ℝ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let a := 2 - b - c
  (1/2 : ℝ) • !![(a : ℂ)*X 0 0 + (b : ℂ)*X 1 1 + (c : ℂ)*X 2 2, -X 0 1, -X 0 2;
    -X 1 0, (c : ℂ)*X 0 0 + (a : ℂ)*X 1 1 + (b : ℂ)*X 2 2, -X 1 2;
    -X 2 0, -X 2 1, (b : ℂ)*X 0 0 + (c : ℂ)*X 1 1 + (a : ℂ)*X 2 2]

def idTensor (Φ : Matrix (Fin 3) (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q => Φ (fun k l => ρ (p.1,k) (q.1,l)) p.2 q.2

def claim : Prop :=
  ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → (b, c) ≠ (0, 0) →
    (b + c ≤ 1 ∨ (b + c - 1)^2 ≤ b*c) →
    ∀ ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → APPT ρ → (idTensor (choiGen b c) ρ).PosSemidef

private def witness (b c : ℝ) (v : Fin 3 × Fin 3 → ℂ) :=
  idTensor (choiGen c b) (vecMulVec v (star v))

private def mass (v : Fin 3 × Fin 3 → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

private def gram (v : Fin 3 × Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun k l => ∑ i : Fin 3, star (v (i,k)) * v (i,l)

private theorem output_hermitian (b c : ℝ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hρ : ρ.IsHermitian) :
    (idTensor (choiGen b c) ρ).IsHermitian := by
  ext ⟨i,k⟩ ⟨j,l⟩
  have he (s t : Fin 3) : star (ρ (j,t) (i,s)) = ρ (i,s) (j,t) :=
    congrFun (congrFun hρ (i,s)) (j,t)
  have hs (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  fin_cases k <;> fin_cases l <;>
    simp only [idTensor, choiGen, conjTranspose_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk, Complex.real_smul, smul_eq_mul, star_mul, star_add, star_neg,
      hs, he] <;> ring

private theorem witness_trace (b c : ℝ) (v : Fin 3 × Fin 3 → ℂ) :
    (witness b c v).trace = (mass v : ℂ) := by
  simp only [witness, mass, idTensor, choiGen, trace, diag_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.smul_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk,
    vecMulVec_apply, Pi.star_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_ofNat,
    ← Complex.mul_conj, Complex.star_def]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, Fin.reduceFinMk]
  ring

private theorem adjoint_identity (b c : ℝ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (v : Fin 3 × Fin 3 → ℂ) :
    star v ⬝ᵥ (idTensor (choiGen b c) ρ *ᵥ v) = (ρ * witness b c v).trace := by
  simp only [witness, idTensor, choiGen, trace, diag_apply, Matrix.mul_apply,
    dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_three,
    Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_one, Matrix.cons_val_two, Fin.reduceFinMk, vecMulVec_apply, Pi.star_apply,
    Complex.real_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_ofNat]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, Fin.reduceFinMk]
  ring


private theorem gram_trace (v : Fin 3 × Fin 3 → ℂ) : (gram v).trace.re = mass v := by
  simp only [gram, mass, trace, diag_apply, Complex.re_sum, Pi.star_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem gram_purity_le (v : Fin 3 × Fin 3 → ℂ) :
    (gram v * gram v).trace.re ≤ (mass v)^2 := by
  have hp : (gram v).PosSemidef := by
    convert posSemidef_conjTranspose_mul_self (fun i k : Fin 3 => v (i,k)) using 1
    ext k l
    rfl
  have he := RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hp.isHermitian
  have ht := congrArg Complex.re hp.isHermitian.trace_eq_sum_eigenvalues
  simp only [Complex.re_sum, Complex.ofReal_re, RCLike.re_eq_complex_re, gram_trace] at ht
  have hb := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun i _ => hp.eigenvalues_nonneg i)
  rw [← he] at hb
  have heq : (∑ i, hp.isHermitian.eigenvalues i) = mass v := by
    simpa [Complex.re_sum, Complex.ofReal_re, gram_trace] using ht.symm
  simpa only [RHLinalg.frobSq, hp.isHermitian.eq, RCLike.re_eq_complex_re, heq] using hb

private theorem witness_purity_identity (b c : ℝ) (v : Fin 3 × Fin 3 → ℂ) :
    (mass v)^2/2 - (witness b c v * witness b c v).trace.re =
      (4 - ((2-b-c)^2+b^2+c^2)) * ((mass v)^2 - (gram v * gram v).trace.re)/8 +
      (2 - ((2-b-c)^2+b^2+c^2)) *
        (3*(∑ k : Fin 3, (∑ i : Fin 3, Complex.normSq (v (i,k)))^2) - (mass v)^2)/8 := by
  simp only [witness, mass, gram, idTensor, choiGen, trace, diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.smul_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk, vecMulVec_apply, Pi.star_apply,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  norm_num only [Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem witness_purity_bound (b c : ℝ) (hq : (2-b-c)^2+b^2+c^2 ≤ 2)
    (v : Fin 3 × Fin 3 → ℂ) :
    ((idTensor (choiGen c b) (vecMulVec v (star v))) *
      (idTensor (choiGen c b) (vecMulVec v (star v)))).trace.re ≤
      (∑ i, Complex.normSq (v i))^2/2 := by
  let p (k : Fin 3) : ℝ := ∑ i : Fin 3, Complex.normSq (v (i,k))
  have hm : mass v = p 0 + p 1 + p 2 := by
    simp only [mass, p, Fintype.sum_prod_type, Fin.sum_univ_three]
    ring
  have hS : 0 ≤ 3*(∑ k : Fin 3, (p k)^2) - (mass v)^2 := by
    rw [hm]
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (p 0-p 1), sq_nonneg (p 0-p 2), sq_nonneg (p 1-p 2)]
  have hr := sub_nonneg.mpr (gram_purity_le v)
  have h1 := mul_nonneg (show 0 ≤ 4-((2-b-c)^2+b^2+c^2) by linarith) hr
  have h2 := mul_nonneg (show 0 ≤ 2-((2-b-c)^2+b^2+c^2) by linarith) hS
  have hi := witness_purity_identity b c v
  change (witness b c v * witness b c v).trace.re ≤ (mass v)^2/2
  change 0 ≤ (2-((2-b-c)^2+b^2+c^2))*
    (3*(∑ k : Fin 3, (∑ i : Fin 3, Complex.normSq (v (i,k)))^2) - (mass v)^2) at h2
  linarith only [hi, h1, h2]


private theorem trace_cauchy
    (A B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A*B).trace.re^2 ≤ (A*A).trace.re * (B*B).trace.re := by
  let e : Fin 9 ≃ Fin 3 × Fin 3 := (finProdFinEquiv (m := 3) (n := 3)).symm
  have ht (M : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
      (M.submatrix e e).trace = M.trace := e.sum_comp (fun i => M i i)
  have hs := D5.S3.Quantum.Matrix.CartesianVariance.trace_product_cauchy
    (A.submatrix e e) (B.submatrix e e)
  simp only [RHLinalg.frobSq, conjTranspose_submatrix, submatrix_mul_equiv,
    ht, hA.eq, hB.eq, RCLike.re_eq_complex_re] at hs
  rw [Complex.normSq_apply] at hs
  nlinarith only [hs, sq_nonneg (A*B).trace.im]

private theorem small_purity_output (b c : ℝ) (hq : (2-b-c)^2+b^2+c^2 ≤ 2)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) (happt : APPT ρ)
 :
    (idTensor (choiGen b c) ρ).PosSemidef := by
  have hout := output_hermitian b c ρ hρ.isHermitian
  refine PosSemidef.of_dotProduct_mulVec_nonneg hout (fun v => ?_)
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hout.im_star_dotProduct_mulVec_self v).symm⟩
  rw [adjoint_identity]
  let W := witness b c v
  let t := mass v
  let R := ρ - (1/9 : ℝ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
  let C := W - (t/9 : ℝ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
  have ht : 0 ≤ t := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i))
  have hw : W.IsHermitian :=
    output_hermitian c b _ (posSemidef_vecMulVec_self_star v).isHermitian
  have hwtrace : W.trace = (t : ℂ) := witness_trace b c v
  have hr : R.IsHermitian := hρ.isHermitian.sub
    ((PosSemidef.one.smul (show (0:ℝ) ≤ 1/9 by norm_num)).isHermitian)
  have hc : C.IsHermitian := hw.sub ((PosSemidef.one.smul (div_nonneg ht (by norm_num))).isHermitian)
  have hR : (R*R).trace.re = (ρ*ρ).trace.re - 1/9 := by
    simp only [R, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      Matrix.one_mul, Matrix.mul_one, trace_sub, trace_smul, trace_one, htrace,
      Fintype.card_prod, Fintype.card_fin, Complex.real_smul,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    norm_num [Complex.re_ofNat, Complex.im_ofNat]
  have hC : (C*C).trace.re = (W*W).trace.re - t^2/9 := by
    simp only [C, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      Matrix.one_mul, Matrix.mul_one, trace_sub, trace_smul, trace_one, hwtrace,
      Fintype.card_prod, Fintype.card_fin, Complex.real_smul,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num [Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hdecomp : (ρ*W).trace.re = t/9 + (R*C).trace.re := by
    simp only [R, C, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      Matrix.one_mul, Matrix.mul_one, trace_sub, trace_smul, trace_one, htrace, hwtrace,
      Fintype.card_prod, Fintype.card_fin, Complex.real_smul,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    norm_num [Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hRn : 0 ≤ (R*R).trace.re := by
    simpa only [hr.eq, RCLike.re_eq_complex_re] using
      (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self R).trace_nonneg).1
  have hCn : 0 ≤ (C*C).trace.re := by
    simpa only [hc.eq, RCLike.re_eq_complex_re] using
      (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self C).trace_nonneg).1
  have hRb : (R*R).trace.re ≤ 32/1089 := by
    rw [hR]
    linarith only [QutritN3PurityBound.purity_bound ρ hρ htrace happt]
  have hCb : (C*C).trace.re ≤ 7/18*t^2 := by
    rw [hC]
    have hb := witness_purity_bound b c hq v
    change (W*W).trace.re ≤ t^2/2 at hb
    linarith only [hb]
  have hs := (trace_cauchy R C hr hc).trans
    (mul_le_mul hRb hCb hCn (by norm_num : (0:ℝ) ≤ 32/1089))
  change 0 ≤ (ρ*W).trace.re
  rw [hdecomp]
  by_contra hn
  have hn : (R*C).trace.re < -(t/9) := by linarith
  have hp : 0 < (-(R*C).trace.re-t/9)*(-(R*C).trace.re+t/9) :=
    mul_pos (by linarith) (by linarith)
  nlinarith only [hs, hp, sq_nonneg t]


private theorem zero_map_posSemidef
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hρ : ρ.PosSemidef) :
    (idTensor (choiGen 0 0) ρ).PosSemidef := by
  let d : Fin 3 → Fin 3 → ℂ :=
    fun k => (![![1,-1,0], ![0,1,-1], ![-1,0,1]] : Fin 3 → Fin 3 → ℂ) k
  let D (k : Fin 3) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
    diagonal (fun p => d k p.2)
  have he : idTensor (choiGen 0 0) ρ = (1/2 : ℝ) •
      (D 0 * ρ * (D 0)ᴴ + D 1 * ρ * (D 1)ᴴ + D 2 * ρ * (D 2)ᴴ) := by
    ext ⟨i,k⟩ ⟨j,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [D, d, idTensor, choiGen, Matrix.mul_apply, diagonal, Fin.sum_univ_succ,
        Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Complex.real_smul,
        Complex.ofReal_zero, Complex.ofReal_one] <;> ring
  rw [he]
  exact (((hρ.mul_mul_conjTranspose_same (D 0)).add
    (hρ.mul_mul_conjTranspose_same (D 1))).add
    (hρ.mul_mul_conjTranspose_same (D 2))).smul (by norm_num : (0:ℝ) ≤ 1/2)

private theorem triangle_decomposition (b c : ℝ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    idTensor (choiGen b c) ρ =
      (1-b-c) • idTensor (choiGen 0 0) ρ +
      b • idTensor (choiGen 1 0) ρ + c • idTensor (choiGen 0 1) ρ := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases k <;> fin_cases l <;>
    simp only [idTensor, choiGen, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk,
      Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_zero, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  all_goals ring

theorem result : claim := by
  intro b c hb hc _ hreg ρ hρ ht ha
  rcases hreg with htri | hcurve
  · rw [triangle_decomposition]
    exact (((zero_map_posSemidef ρ hρ).smul (show 0 ≤ 1-b-c by linarith)).add
      ((small_purity_output 1 0 (by norm_num) ρ hρ ht ha).smul hb)).add
      ((small_purity_output 0 1 (by norm_num) ρ hρ ht ha).smul hc)
  · apply small_purity_output b c _ ρ hρ ht ha
    nlinarith only [hcurve]

#print axioms result


end D5.S3.Quantum.Entanglement.AbsolutePPT.GeneralizedChoiNonDetection
