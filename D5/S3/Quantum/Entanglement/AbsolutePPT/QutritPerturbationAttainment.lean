/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment
   mirror-E: none(waiver:kernel-checked-positive-decomposition)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.pure_attainment; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.symOps
   digest: Rank-one and projector perturbations attain the two qutrit purity candidates. -/

/-
proof_shape: pure_attainment: content; projector_attainment: content
escape_witness: pure_attainment uses the normalized-vector antisymmetric Gram
  complement construction; projector_attainment uses the positive qutrit Kraus decomposition.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose
  statement_id: sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089
Information-escape registration is paused under CLAUDE.md section 3.9.

transpose_cp_identity; proof_shape: bind-only; escape_witness: none; consumer: projector_attainment, pure_attainment
-/

import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

def APPT {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ U : unitaryGroup (A × B) ℂ, partialTranspose ((U : Matrix _ _ ℂ) * M * (U : Matrix _ _ ℂ)ᴴ) |>.PosSemidef

noncomputable def rhoPure (n : ℕ) (v : Fin 3 × Fin n → ℂ) : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  ((1 / (3*(n : ℝ)+2) : ℝ) : ℂ) • (1+(2 : ℂ) • vecMulVec v (star v))

noncomputable def rhoProjector (n : ℕ) (P : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  ((1 / (4*(n : ℝ)) : ℝ) : ℂ) • (1+P)

private def symOps : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
   ![!![0,1,0;1,0,0;0,0,0], !![0,0,1;0,0,0;1,0,0], !![0,0,0;0,0,1;0,1,0]]

private def antiOps : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
   ![!![0,1,0;-1,0,0;0,0,0], !![0,0,1;0,0,0;-1,0,0], !![0,0,0;0,0,1;0,-1,0]]

private def antiColumns {B : Type} [Fintype B] [DecidableEq B] (v : Fin 3 × B → ℂ) : Matrix (Fin 3 × B) (Fin 3) ℂ :=
    fun (i,j) a => ((antiOps a) *ᵥ (fun k => v (k,j))) i

private def reducedColumns {B : Type} [Fintype B] [DecidableEq B] (v : Fin 3 × B → ℂ) : Matrix B (Fin 3) ℂ :=
    fun j a => star ((![v (2,j), -v (1,j), v (0,j)] : Fin 3 → ℂ) a)

private theorem transpose_cp_identity {B : Type} [Fintype B] [DecidableEq B] (M : Matrix (Fin 3 × B) (Fin 3 × B) ℂ) :
      (2 : ℂ) • ∑ a : Fin 3, (Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)) * M * ((Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)))ᴴ +
      (∑ a : Fin 3, (Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)) * M * ((Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)))ᴴ) +
      (∑ a : Fin 3, (Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)) * (1-M) * ((Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)))ᴴ) =
        (2 : ℂ) • (1 + (partialTranspose M)ᵀ) := by
  have local_conjugate {B : Type} [Fintype B] [DecidableEq B] (F : Matrix (Fin 3) (Fin 3) ℂ)
      (M : Matrix (Fin 3 × B) (Fin 3 × B) ℂ) (i k : Fin 3) (j l : B) :
      ((Matrix.kronecker F (1 : Matrix B B ℂ)) * M * ((Matrix.kronecker F (1 : Matrix B B ℂ)))ᴴ) (i,j) (k,l) =
      ∑ a : Fin 3, ∑ b : Fin 3, F i a * M (a,j) (b,l) * star (F k b) := by
    simp only [Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type]
    simp only [starRingEnd_apply, apply_ite, star_zero, mul_ite, mul_zero, ite_mul, zero_mul]
    simp [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Finset.sum_apply, local_conjugate,
    Fin.sum_univ_succ, Finset.sum_empty, zero_add, add_zero]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.single, symOps, antiOps, Matrix.single, Matrix.of_apply, partialTranspose, Matrix.transpose_apply,
      Matrix.one_apply, Prod.mk.injEq, Fin.reduceEq, Fin.reduceFinMk, eq_comm]
  all_goals try split_ifs
  all_goals try simp_all
  all_goals ring

theorem pure_attainment (n : ℕ) (v : Fin 3 × Fin n → ℂ)
    (hv : ∑ ij, star (v ij)*v ij=1) :
    APPT (rhoPure n v) ∧ (rhoPure n v).PosSemidef ∧ (rhoPure n v).trace=1 ∧
      ((rhoPure n v)*(rhoPure n v)).trace = ((3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 : ℝ) := by
  have pt_add {A B : Type} (M N : Matrix (A × B) (A × B) ℂ) : partialTranspose (M+N)=partialTranspose M+partialTranspose N := rfl

  have pt_smul {A B : Type} (c : ℂ) (M : Matrix (A × B) (A × B) ℂ) : partialTranspose (c • M)=c • partialTranspose M := rfl

  have pt_one {A B : Type} [DecidableEq A] [DecidableEq B] :
      partialTranspose (1 : Matrix (A × B) (A × B) ℂ)=1 := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp [partialTranspose, Matrix.one_apply, Prod.mk.injEq, eq_comm]



  have gram_complement {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
      (W : Matrix I J ℂ) (h : (1-Wᴴ*W).PosSemidef) : (1-W*Wᴴ).PosSemidef := by
    letI : Invertible (1 : Matrix I I ℂ) := invertibleOne
    letI : Invertible (1 : Matrix J J ℂ) := invertibleOne
    have hblock : (fromBlocks (1 : Matrix I I ℂ) W Wᴴ (1 : Matrix J J ℂ)).PosSemidef := by
      apply (Matrix.PosDef.fromBlocks₁₁ W 1 Matrix.PosDef.one).mpr
      simpa using h
    have h' := (Matrix.PosDef.fromBlocks₂₂ (1 : Matrix I I ℂ) W Matrix.PosDef.one).mp hblock
    simpa using h'



  have anti_gram_identity {B : Type} [Fintype B] [DecidableEq B] (v : Fin 3 × B → ℂ)
      (hv : ∑ ij, star (v ij) * v ij=1) :
      1-(antiColumns v)ᴴ*antiColumns v = (reducedColumns v)ᴴ*reducedColumns v := by
    have hv' : ∑ j, star (v (0,j))*v (0,j) + ∑ j, star (v (1,j))*v (1,j) +
        ∑ j, star (v (2,j))*v (2,j)=1 := by
      simpa [Fintype.sum_prod_type, Fin.sum_univ_succ, add_assoc] using hv
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [antiColumns, reducedColumns, antiOps, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.of_apply,
        Matrix.one_apply, Fin.reduceEq, Fin.reduceFinMk, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    all_goals simp only [starRingEnd_apply, mul_comm] at hv' ⊢
    all_goals first | linear_combination -hv' | (apply Finset.sum_congr rfl; intro j hj; ring)

  have local_mulVec {B : Type} [Fintype B] [DecidableEq B] (F : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 × B → ℂ)
      (i : Fin 3) (j : B) :
      ((Matrix.kronecker F (1 : Matrix B B ℂ)) *ᵥ v) (i,j) = ∑ a, F i a * v (a,j) := by
    simp [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type, ite_mul]

  have conjugate_outer {I : Type} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) :
      A * vecMulVec v (star v) * Aᴴ = vecMulVec (A *ᵥ v) (star (A *ᵥ v)) := by
    rw [mul_vecMulVec, vecMulVec_mul]
    simp [Matrix.vecMul_conjTranspose]

  have anti_outer_identity {B : Type} [Fintype B] [DecidableEq B] (v : Fin 3 × B → ℂ) :
      antiColumns v * (antiColumns v)ᴴ =
      ∑ a : Fin 3, (Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)) * vecMulVec v (star v) *
        ((Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)))ᴴ := by
    simp only [conjugate_outer]
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply,
      starRingEnd_apply, Pi.star_apply]
    simp only [local_mulVec]
    simp only [antiColumns, Matrix.mulVec, dotProduct]

  have anti_one_identity {B : Type} [Fintype B] [DecidableEq B] :
      (∑ a : Fin 3, (Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)) * 1 * ((Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)))ᴴ) =
        (2 : ℂ) • (1 : Matrix (Fin 3 × B) (Fin 3 × B) ℂ) := by
    have hz : (partialTranspose (0 : Matrix (Fin 3 × B) (Fin 3 × B) ℂ))ᵀ=0 := rfl
    simpa only [mul_zero, zero_mul, Finset.sum_const_zero, smul_zero, add_zero, zero_add, sub_zero, hz] using transpose_cp_identity (0 : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)

  have pure_lower_bound {B : Type} [Fintype B] [DecidableEq B] (v : Fin 3 × B → ℂ) (hv : ∑ ij, star (v ij)*v ij=1) :
      (1+(2 : ℂ) • partialTranspose (vecMulVec v (star v))).PosSemidef := by
    let P := vecMulVec v (star v)
    have hp : P.PosSemidef := posSemidef_vecMulVec_self_star v
    have ha : (1-antiColumns v*(antiColumns v)ᴴ).PosSemidef := by
      apply gram_complement
      rw [anti_gram_identity v hv]
      exact posSemidef_conjTranspose_mul_self _
    have hs : ((2 : ℂ) • ∑ a : Fin 3, (Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)))ᴴ +
        ∑ a : Fin 3, (Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)))ᴴ).PosSemidef :=
      (Matrix.posSemidef_sum _ (fun _ _ => hp.mul_mul_conjTranspose_same _)).smul (show (0 : ℂ) ≤ 2 by norm_num) |>.add
        (Matrix.posSemidef_sum _ (fun _ _ => hp.mul_mul_conjTranspose_same _))
    have hc := transpose_cp_identity P
    have heq : (∑ a : Fin 3, (Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)) * (1-P) * ((Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)))ᴴ) =
        (2 : ℂ) • 1 - antiColumns v*(antiColumns v)ᴴ := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
      rw [anti_one_identity, anti_outer_identity]
    rw [heq] at hc
    have hpos := hs.add ha
    have heq' : (2 : ℂ) • (∑ a : Fin 3, (Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)))ᴴ) +
        (∑ a : Fin 3, (Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)))ᴴ) +
        (1-antiColumns v*(antiColumns v)ᴴ) = 1+(2 : ℂ) • (partialTranspose P)ᵀ := by
      ext i j
      have hc' := congrFun (congrFun hc i) j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hc' ⊢
      linear_combination hc'
    rw [heq'] at hpos
    have ht := hpos.transpose
    have heqT : (1+(2 : ℂ) • (partialTranspose P)ᵀ)ᵀ = 1+(2 : ℂ) • partialTranspose P := by
      ext ⟨i,j⟩ ⟨k,l⟩
      simp [partialTranspose, partialTranspose, Matrix.transpose_apply, Matrix.transpose_apply, Matrix.one_apply, Prod.mk.injEq, eq_comm]
    rw [heqT] at ht
    exact ht

  have appt_smul {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      {M : Matrix (A × B) (A × B) ℂ} (h : APPT M) (r : ℝ) (hr : 0 ≤ r) : APPT ((r : ℂ) • M) := by
    intro U
    have hp := (h U).smul (Complex.zero_le_real.mpr hr)
    rw [Matrix.mul_smul, Matrix.smul_mul, pt_smul]
    exact hp

  have unitary_vector_norm {I : Type} [Fintype I] [DecidableEq I]
      (U : unitaryGroup I ℂ) (v : I → ℂ) (hv : star v ⬝ᵥ v=1) :
      star ((U : Matrix I I ℂ) *ᵥ v) ⬝ᵥ ((U : Matrix I I ℂ) *ᵥ v)=1 := by
    have hu : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ)=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul, hu, vecMul_one]
    exact hv

  have pure_numerator_appt {B : Type} [Fintype B] [DecidableEq B]
      (v : Fin 3 × B → ℂ) (hv : ∑ ij, star (v ij)*v ij=1) :
      APPT (1+(2 : ℂ) • vecMulVec v (star v)) := by
    intro U
    have hu : (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ) * (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)ᴴ=1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
    have hv' := unitary_vector_norm U v hv
    have h := pure_lower_bound ((U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)*ᵥ v) hv'
    simpa only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hu,
      conjugate_outer, pt_add, pt_smul, pt_one] using h

  have pure_outer_square {I : Type} [Fintype I] (v : I → ℂ) (hv : star v ⬝ᵥ v=1) :
      vecMulVec v (star v) * vecMulVec v (star v)=vecMulVec v (star v) := by
    rw [vecMulVec_mul_vecMulVec, hv]
    simp

  have hd : 0 < 3*(n : ℝ)+2 := by positivity
  have hs : 0 ≤ (1/(3*(n : ℝ)+2) : ℝ) := by positivity
  have hdc : 3*(n : ℂ)+2 ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hap : APPT (rhoPure n v) := appt_smul (pure_numerator_appt v hv) _ hs
  have hps : (rhoPure n v).PosSemidef := by
    apply Matrix.PosSemidef.smul _ (Complex.zero_le_real.mpr hs)
    exact Matrix.PosSemidef.one.add ((posSemidef_vecMulVec_self_star v).smul (by norm_num))
  have htr : (vecMulVec v (star v)).trace=1 := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    simpa only [dotProduct, Pi.star_apply, starRingEnd_apply] using hv
  have hi : (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ).trace=3*(n : ℂ) := by
    simp [Matrix.trace_one, Fintype.card_prod]
  have hsq := pure_outer_square v hv
  have hm : (1+(2 : ℂ) • vecMulVec v (star v)) * (1+(2 : ℂ) • vecMulVec v (star v))=
      1+(8 : ℂ) • vecMulVec v (star v) := by
    simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hsq]
    module
  refine ⟨hap,hps,?_,?_⟩
  · simp only [rhoPure, Matrix.trace_smul, Matrix.trace_add, hi,htr]
    simp only [smul_eq_mul]
    push_cast
    field_simp [hdc]
  · simp only [rhoPure, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
      Matrix.trace_smul, Matrix.trace_add, hi, htr]
    simp only [smul_eq_mul]
    push_cast
    field_simp [hdc]

theorem projector_attainment (n : ℕ) (hn : 0<n)
    (P : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (hH : P.IsHermitian)
    (hP : P*P=P) (hr : P.rank=n) :
    APPT (rhoProjector n P) ∧ (rhoProjector n P).PosSemidef ∧ (rhoProjector n P).trace=1 ∧
      ((rhoProjector n P)*(rhoProjector n P)).trace=(3/(8*(n : ℝ)) : ℝ) := by
  have pt_add {A B : Type} (M N : Matrix (A × B) (A × B) ℂ) : partialTranspose (M+N)=partialTranspose M+partialTranspose N := rfl

  have pt_smul {A B : Type} (c : ℂ) (M : Matrix (A × B) (A × B) ℂ) : partialTranspose (c • M)=c • partialTranspose M := rfl

  have pt_one {A B : Type} [DecidableEq A] [DecidableEq B] :
      partialTranspose (1 : Matrix (A × B) (A × B) ℂ)=1 := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp [partialTranspose, Matrix.one_apply, Prod.mk.injEq, eq_comm]



  have one_add_ptA_psd {B : Type} [Fintype B] [DecidableEq B] {P : Matrix (Fin 3 × B) (Fin 3 × B) ℂ}
      (hP : P.PosSemidef) (hQ : (1-P).PosSemidef) : (1+(partialTranspose P)ᵀ).PosSemidef := by
    have hdiag : (∑ a : Fin 3, (Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)))ᴴ).PosSemidef :=
      Matrix.posSemidef_sum (s := Finset.univ) (x := fun a => (Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker ((Matrix.single a a (1 : ℂ))) (1 : Matrix B B ℂ)))ᴴ) (fun a _ => hP.mul_mul_conjTranspose_same _)
    have hsym : (∑ a : Fin 3, (Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)))ᴴ).PosSemidef :=
      Matrix.posSemidef_sum (s := Finset.univ) (x := fun a => (Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)) * P * ((Matrix.kronecker (symOps a) (1 : Matrix B B ℂ)))ᴴ) (fun a _ => hP.mul_mul_conjTranspose_same _)
    have hanti : (∑ a : Fin 3, (Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)) * (1-P) * ((Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)))ᴴ).PosSemidef :=
      Matrix.posSemidef_sum (s := Finset.univ) (x := fun a => (Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)) * (1-P) * ((Matrix.kronecker (antiOps a) (1 : Matrix B B ℂ)))ᴴ) (fun a _ => hQ.mul_mul_conjTranspose_same _)
    have h := ((hdiag.smul (show (0 : ℂ) ≤ 2 by norm_num)).add hsym).add hanti
    rw [transpose_cp_identity] at h
    have h' := h.smul (show (0 : ℂ) ≤ (1/2 : ℝ) by exact_mod_cast (show (0 : ℝ) ≤ 1/2 by norm_num))
    convert h' using 1 <;> ext i j <;> simp <;> ring

  have one_add_pt_psd {B : Type} [Fintype B] [DecidableEq B] {P : Matrix (Fin 3 × B) (Fin 3 × B) ℂ}
      (hP : P.PosSemidef) (hQ : (1-P).PosSemidef) : (1+partialTranspose P).PosSemidef := by
    have ht := (one_add_ptA_psd hP hQ).transpose
    have heq : (1 + (partialTranspose P)ᵀ)ᵀ = 1 + partialTranspose P := by
      ext ⟨i,j⟩ ⟨k,l⟩
      simp [partialTranspose, partialTranspose, Matrix.transpose_apply, Matrix.transpose_apply, Matrix.one_apply, Prod.mk.injEq, eq_comm]
    rw [heq] at ht
    exact ht

  have contraction_appt {B : Type} [Fintype B] [DecidableEq B] {P : Matrix (Fin 3 × B) (Fin 3 × B) ℂ}
      (hP : P.PosSemidef) (hQ : (1-P).PosSemidef) : APPT (1+P) := by
    intro U
    have hu : (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ) * (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)ᴴ=1 :=
      by simpa only [Matrix.star_eq_conjTranspose] using (mem_unitaryGroup_iff.mp U.property)
    have hp := hP.mul_mul_conjTranspose_same (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)
    have hq := hQ.mul_mul_conjTranspose_same (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)
    have heq : (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ) * (1-P) * (U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)ᴴ =
        1-(U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)*P*(U : Matrix (Fin 3 × B) (Fin 3 × B) ℂ)ᴴ := by
      rw [mul_sub, sub_mul, mul_one, hu]
    rw [heq] at hq
    have h := one_add_pt_psd hp hq
    simpa only [mul_add, add_mul, mul_one, hu, pt_add, pt_one] using h

  have appt_smul {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      {M : Matrix (A × B) (A × B) ℂ} (h : APPT M) (r : ℝ) (hr : 0 ≤ r) : APPT ((r : ℂ) • M) := by
    intro U
    have hp := (h U).smul (Complex.zero_le_real.mpr hr)
    rw [Matrix.mul_smul, Matrix.smul_mul, pt_smul]
    exact hp

  have projection_pos_and_complement {I : Type} [Fintype I] [DecidableEq I]
      (P : Matrix I I ℂ) (hH : P.IsHermitian) (hP : P*P=P) :
      P.PosSemidef ∧ (1-P).PosSemidef := by
    have h : Pᴴ*P=P := by rw [hH.eq,hP]
    have hp : P.PosSemidef := h ▸ posSemidef_conjTranspose_mul_self P
    have hQ : (1-P)ᴴ*(1-P)=1-P := by
      simp only [conjTranspose_sub, conjTranspose_one, hH.eq]
      noncomm_ring [hP]
    exact ⟨hp,hQ ▸ posSemidef_conjTranspose_mul_self (1-P)⟩

  have projection_trace_rank {I : Type} [Fintype I] [DecidableEq I]
      (P : Matrix I I ℂ) (hP : P*P=P) : P.trace=(P.rank : ℂ) := by
    have hlin : IsIdempotentElem P.mulVecLin := by
      rw [← Matrix.toLin'_apply']
      change Matrix.toLin' P ∘ₗ Matrix.toLin' P=Matrix.toLin' P
      rw [← Matrix.toLin'_mul, hP]
    have ht := (LinearMap.IsIdempotentElem.isProj_range _ hlin).trace
    have htrace : LinearMap.trace ℂ (I → ℂ) P.mulVecLin=P.trace := by
      rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I),
        LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rw [htrace] at ht
    exact ht

  have hpos := projection_pos_and_complement P hH hP
  have hs : 0 ≤ (1/(4*(n : ℝ)) : ℝ) := by positivity
  have hd : (n : ℂ) ≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have ht : P.trace=(n : ℂ) := by rw [projection_trace_rank P hP, hr]
  have hi : (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ).trace=3*(n : ℂ) := by
    simp [Matrix.trace_one,Fintype.card_prod]
  have hm : (1+P)*(1+P)=1+(3 : ℂ) • P := by
    simp only [mul_add, add_mul, one_mul, mul_one, hP]
    module
  refine ⟨appt_smul (contraction_appt hpos.1 hpos.2) _ hs,
    (Matrix.PosSemidef.one.add hpos.1).smul (Complex.zero_le_real.mpr hs),?_,?_⟩
  · simp only [rhoProjector, Matrix.trace_smul, Matrix.trace_add, hi,ht]
    simp only [smul_eq_mul]
    push_cast
    field_simp [hd]
    norm_num
  · simp only [rhoProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
      Matrix.trace_smul, Matrix.trace_add, hi,ht]
    simp only [smul_eq_mul]
    push_cast
    field_simp [hd]
    ring

#print axioms pure_attainment
#print axioms projector_attainment
#check symOps
#check antiOps
#check antiColumns
#check reducedColumns
end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
