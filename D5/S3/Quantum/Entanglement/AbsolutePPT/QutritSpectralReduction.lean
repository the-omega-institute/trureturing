/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction
   mirror-E: none(waiver:kernel-checked-spectral-construction)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.spectral_reduction; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction.bell
   digest: Literal APPT density matrices yield ordered certificate coordinates satisfying both qutrit LMIs. -/

/-
proof_shape: spectral_reduction: content
escape_witness: An explicit extended Bell unitary and its swapped partner force
  the two qutrit spectral matrices to be positive through principal compressions.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose
  statement_id: sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089
Information-escape registration is paused under CLAUDE.md section 3.9.

castMat_mul, castMat_transpose, castMat_diagonal; proof_shape: bind-only; escape_witness: none; consumer: psd_of_rat_ldl, QutritN4PurityBound.certificate_bound, QutritN5PurityBound.certificate_bound, QutritN6PurityBound.certificate_bound, QutritN7PurityBound.certificate_bound, QutritN8PurityBound.Q_psd, QutritN9PurityBound.Q_psd, QutritN10PurityBound.Q_psd
castIntMat_mul, castIntMat_transpose, castIntMat_diagonal; proof_shape: bind-only; escape_witness: none; consumer: psd_of_int_scaled_ldl
psd_of_rat_ldl; proof_shape: bind-only; escape_witness: none; consumer: QutritN4PurityBound.certificate_bound, QutritN5PurityBound.certificate_bound, QutritN6PurityBound.certificate_bound, QutritN7PurityBound.certificate_bound, QutritN8PurityBound.A1_k_psd, QutritN8PurityBound.A2_k_psd, QutritN9PurityBound.A1_k_psd, QutritN9PurityBound.A2_k_psd, QutritN10PurityBound.A1_k_psd, QutritN10PurityBound.A2_k_psd
psd_of_int_scaled_ldl; proof_shape: bind-only; escape_witness: none; consumer: QutritN4PurityBound.certificate_bound, QutritN5PurityBound.certificate_bound, QutritN6PurityBound.certificate_bound, QutritN7PurityBound.certificate_bound, QutritN8PurityBound.G_psd, QutritN9PurityBound.G_psd, QutritN10PurityBound.G_psd
cast_vec_cons, cast_vec_empty; proof_shape: bind-only; escape_witness: none; consumer: QutritN8PurityBound.A1_k_real, QutritN8PurityBound.A2_k_real, QutritN8PurityBound.N_real, QutritN8PurityBound.Q_real, QutritN9PurityBound.A1_k_real, QutritN9PurityBound.A2_k_real, QutritN9PurityBound.N_real, QutritN9PurityBound.Q_real, QutritN10PurityBound.A1_k_real, QutritN10PurityBound.A2_k_real, QutritN10PurityBound.N_real, QutritN10PurityBound.Q_real
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open QutritPerturbationAttainment
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

noncomputable def castMat {I J : Type} (A : Matrix I J ℚ) : Matrix I J ℝ := A.map Rat.cast
theorem castMat_mul {I J K : Type} [Fintype J]
    (A : Matrix I J ℚ) (B : Matrix J K ℚ) : castMat (A*B)=castMat A*castMat B := by
  ext i k
  simp [castMat, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul]
theorem castMat_transpose {I J : Type} (A : Matrix I J ℚ) :
    castMat A.transpose=(castMat A)ᴴ := by
  ext i j
  simp [castMat, Matrix.conjTranspose_apply]
theorem castMat_diagonal {I : Type} [DecidableEq I] (d : I → ℚ) :
    castMat (diagonal d)=diagonal (fun i => (d i : ℝ)) := by
  ext i j
  by_cases h : i=j <;> simp [castMat, diagonal,h]
theorem psd_of_rat_ldl {I J : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (L : Matrix I J ℚ) (d : J → ℚ)
    (he : A=L*diagonal d*L.transpose) (hd : ∀ i, 0 ≤ d i) :
    (castMat A).PosSemidef := by
  rw [he,castMat_mul,castMat_mul,castMat_diagonal,castMat_transpose]
  exact (Matrix.PosSemidef.diagonal (fun i => by change (0 : ℝ) ≤ (d i : ℝ); exact_mod_cast hd i)).mul_mul_conjTranspose_same _
noncomputable def castIntMat {I J : Type} (A : Matrix I J ℤ) : Matrix I J ℝ := A.map Int.cast
theorem castIntMat_mul {I J K : Type} [Fintype J]
    (A : Matrix I J ℤ) (B : Matrix J K ℤ) : castIntMat (A*B)=castIntMat A*castIntMat B := by
  ext i k
  simp [castIntMat,Matrix.mul_apply]
theorem castIntMat_transpose {I J : Type} (A : Matrix I J ℤ) :
    castIntMat A.transpose=(castIntMat A)ᴴ := by
  ext i j
  simp [castIntMat,Matrix.conjTranspose_apply]
theorem castIntMat_diagonal {I : Type} [DecidableEq I] (d : I → ℤ) :
    castIntMat (diagonal d)=diagonal (fun i => (d i : ℝ)) := by
  ext i j
  by_cases h : i=j <;> simp [castIntMat,diagonal,h]
theorem psd_of_int_scaled_ldl {I J : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (A : Matrix I I ℚ) (AI : Matrix I I ℤ) (L : Matrix I J ℤ) (d : J → ℤ)
    (s : ℤ) (hscale : ∀ i j, A i j=(AI i j : ℚ)/(s : ℚ))
    (he : AI=L*diagonal d*L.transpose) (hd : ∀ i, 0 ≤ d i) (hs : 0<s) :
    (castMat A).PosSemidef := by
  have hp : (castIntMat AI).PosSemidef := by
    rw [he,castIntMat_mul,castIntMat_mul,castIntMat_diagonal,castIntMat_transpose]
    exact (Matrix.PosSemidef.diagonal (fun i => by change (0 : ℝ) ≤ (d i : ℝ); exact_mod_cast hd i)).mul_mul_conjTranspose_same _
  have heq : castMat A=(1/(s : ℝ)) • castIntMat AI := by
    ext i j
    simp only [castMat,castIntMat,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul]
    rw [hscale]
    push_cast
    ring
  rw [heq]
  apply hp.smul
  have h : (0 : ℝ)<s := by exact_mod_cast hs
  positivity
theorem cast_vec_cons {n : ℕ} (x : ℚ) (v : Fin n → ℚ) :
     (fun i => ((Matrix.vecCons x v i : ℚ) : ℝ)) =
       Matrix.vecCons (x : ℝ) (fun i => (v i : ℝ)) := by
   exact Fin.comp_cons Rat.cast x v
theorem cast_vec_empty : (fun i : Fin 0 => ((Matrix.vecEmpty i : ℚ) : ℝ)) =
       (Matrix.vecEmpty : Fin 0 → ℝ) := Subsingleton.elim _ _

def K1 (l : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*l 8, l 7-l 0, l 5-l 1; l 7-l 0, 2*l 6, l 4-l 2; l 5-l 1, l 4-l 2, 2*l 3]
def K2 (l : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*l 8, l 7-l 0, l 6-l 1; l 7-l 0, 2*l 5, l 4-l 2; l 6-l 1, l 4-l 2, 2*l 3]
def boundaryValues (k : ℕ) (l : Fin (3*(3+k)) → ℝ) : Fin 9 → ℝ :=
  fun q => l (if h : q.val < 3 then ⟨q.val, by omega⟩ else ⟨3*k+q.val, by omega⟩)

private noncomputable def bell : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun (i,j) (k,l) =>
  if i=j then if (i,j)=(k,l) then 1 else 0
  else if (i,j)=(k,l) then (if i<j then (Real.sqrt 2 : ℂ)⁻¹ else -(Real.sqrt 2 : ℂ)⁻¹)
  else if (i,j)=(l,k) then (Real.sqrt 2 : ℂ)⁻¹ else 0

private noncomputable def extendedBell (k : ℕ) : Matrix (Fin 3 × (Fin 3 ⊕ Fin k)) (Fin 3 × (Fin 3 ⊕ Fin k)) ℂ :=
  (fromBlocks bell 0 0 (1 : Matrix (Fin 3 × Fin k) (Fin 3 × Fin k) ℂ)).submatrix
    (((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm (((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm

private noncomputable def extendUnitary (k : ℕ) (V : unitaryGroup (Fin 3 × Fin 3) ℂ) : unitaryGroup (Fin 3 × (Fin 3 ⊕ Fin k)) ℂ :=
  ⟨(fromBlocks (V : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) 0 0 (1 : Matrix (Fin 3 × Fin k) (Fin 3 × Fin k) ℂ)).submatrix
    (((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm (((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm, by
      rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_submatrix,
        submatrix_mul_equiv _ _ _ (((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm _]
      have hv : (V : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) * (V : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)ᴴ=1 := by
        simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp V.property
      simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv, fromBlocks_one]⟩

private noncomputable def permutationU {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) : unitaryGroup I ℂ := ⟨e.permMatrix ℂ, by
  rw [mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp⟩

private noncomputable def swapU : unitaryGroup (Fin 3 × Fin 3) ℂ :=
  ⟨(Equiv.swap ((1,1) : Fin 3 × Fin 3) ((0,2) : Fin 3 × Fin 3)).permMatrix ℂ, by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul]
    simp⟩

theorem spectral_reduction (k : ℕ)
    (rho : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    ∃ l : Fin (3*(3+k)) → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
      (K1 (boundaryValues k l)).PosSemidef ∧ (K2 (boundaryValues k l)).PosSemidef ∧
      (rho*rho).trace.re = ∑ i, (l i)^2 := by


  have c_square : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)=2 := by
      norm_cast
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [← mul_inv, h]
    norm_num

  have c_star : star (Real.sqrt 2 : ℂ)⁻¹=(Real.sqrt 2 : ℂ)⁻¹ := by simp

  have bell_unitary : bell ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, bell, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.reduceEq, Fin.reduceFinMk, Fin.reduceLT, c_star, c_square]
    all_goals simp only [show (starRingEnd ℂ) (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ)⁻¹ by simp, c_square]
    all_goals norm_num

  let pack (l : Fin 9 → ℝ) : (Fin 3 × Fin 3) → ℂ := fun (i,j) =>
    (if i=0 then (if j=0 then l 8 else if j=1 then l 7 else l 5)
      else if i=1 then (if j=0 then l 0 else if j=1 then l 6 else l 4)
      else (if j=0 then l 1 else if j=1 then l 2 else l 3) : ℝ)

  let KC1 (l : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
    !![2*(l 8 : ℂ), (l 7-l 0 : ℝ), (l 5-l 1 : ℝ);
       (l 7-l 0 : ℝ), 2*(l 6 : ℂ), (l 4-l 2 : ℝ);
       (l 5-l 1 : ℝ), (l 4-l 2 : ℝ), 2*(l 3 : ℂ)]

  have bell_pt_principal (l : Fin 9 → ℝ) :
      (partialTranspose (bell * diagonal (pack l) * bellᴴ)).submatrix (fun i => (i,i)) (fun i => (i,i)) =
        (1/2 : ℂ) • KC1 l := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.submatrix_apply, partialTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_three]
    all_goals norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, pack, bell, diagonal, KC1, Matrix.of_apply,
      Fin.reduceEq, Fin.reduceFinMk, Fin.reduceLT, c_star, c_square, Complex.ofReal_sub]
    all_goals ring_nf
    all_goals norm_num [pow_two, c_square] <;> ring

  have appt_conjugate {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      {M : Matrix (A × B) (A × B) ℂ} (h : APPT M) (V : unitaryGroup (A × B) ℂ) :
      APPT ((V : Matrix (A × B) (A × B) ℂ)*M*(V : Matrix (A × B) (A × B) ℂ)ᴴ) := by
    intro U
    have hp := h (U*V)
    simpa only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hp

  let swap56 : Equiv.Perm (Fin 3 × Fin 3) := Equiv.swap (1,1) (0,2)


  let flip56 (l : Fin 9 → ℝ) : Fin 9 → ℝ := l ∘ Equiv.swap 5 6

  have swap_pack (l : Fin 9 → ℝ) :
      (swapU : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)*diagonal (pack l)*(swapU : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)ᴴ =
        diagonal (pack (flip56 l)) := by
    change swap56.permMatrix ℂ * diagonal (pack l) * (swap56.permMatrix ℂ)ᴴ = _
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    change (diagonal (pack l)).submatrix swap56 swap56 = _
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, swap56, flip56, pack,
        Function.comp_apply, Equiv.swap_apply_def, Fin.reduceEq, Fin.reduceFinMk]

  let KC2 (l : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ := KC1 (flip56 l)


  have extendedBell_unitary (k : ℕ) : extendedBell k ∈ unitaryGroup (Fin 3 × (Fin 3 ⊕ Fin k)) ℂ := by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    unfold extendedBell
    rw [conjTranspose_submatrix, submatrix_mul_equiv _ _ _ (((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm _]
    have hb : bell * bellᴴ=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp bell_unitary
    simp [fromBlocks_conjTranspose, fromBlocks_multiply, hb, fromBlocks_one]

  let packExtended (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ) : Fin 3 × (Fin 3 ⊕ Fin k) → ℂ :=
      fun (i,j) => match j with
        | Sum.inl a => pack l (i,a)
        | Sum.inr a => mid (i,a)

  have extended_principal (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ) :
      (partialTranspose (extendedBell k * diagonal (packExtended k l mid) * (extendedBell k)ᴴ)).submatrix
        (fun i => (i,Sum.inl i)) (fun i => (i,Sum.inl i)) = (1/2 : ℂ) • KC1 l := by
    rw [← bell_pt_principal]
    ext i j
    simp only [Matrix.submatrix_apply, partialTranspose, extendedBell, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type]
    simp [Equiv.prodSumDistrib, packExtended, Equiv.prodSumDistrib, Equiv.sumProdDistrib,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, diagonal, Matrix.submatrix_apply]

  have necessary_K1_extended (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ)
      (h : APPT (diagonal (packExtended k l mid))) : (KC1 l).PosSemidef := by
    have hp := (h ⟨extendedBell k,extendedBell_unitary k⟩).submatrix (fun i => (i,Sum.inl i))
    change ((partialTranspose (extendedBell k * diagonal (packExtended k l mid) * (extendedBell k)ᴴ)).submatrix _ _).PosSemidef at hp
    rw [extended_principal] at hp
    have hscale := hp.smul (show (0 : ℂ) ≤ 2 by norm_num)
    convert hscale using 1 <;> ext i j <;> simp


  have extended_swap_pack (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ) :
      (extendUnitary k swapU : Matrix (Fin 3 × (Fin 3 ⊕ Fin k)) (Fin 3 × (Fin 3 ⊕ Fin k)) ℂ) * diagonal (packExtended k l mid) *
        (extendUnitary k swapU : Matrix (Fin 3 × (Fin 3 ⊕ Fin k)) (Fin 3 × (Fin 3 ⊕ Fin k)) ℂ)ᴴ = diagonal (packExtended k (flip56 l) mid) := by
    ext ⟨i,j⟩ ⟨a,b⟩
    rcases j with j|j <;> rcases b with b|b
    all_goals simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, extendUnitary,
      Fintype.sum_prod_type, Fintype.sum_sum_type]
    all_goals simp [Equiv.prodSumDistrib, packExtended, Equiv.prodSumDistrib, Equiv.sumProdDistrib,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, diagonal, Matrix.submatrix_apply, Matrix.one_apply, Prod.mk.injEq, ite_and, eq_comm]
    · have hs := congrFun (congrFun (swap_pack l) (i,j)) (a,b)
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, diagonal, Prod.mk.injEq, ite_mul, mul_ite, ite_and] using hs
    · by_cases hi : i=a <;> by_cases hj : j=b <;> simp [hi,hj]

  have necessary_K2_extended (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ)
      (h : APPT (diagonal (packExtended k l mid))) : (KC2 l).PosSemidef := by
    have h' := appt_conjugate h (extendUnitary k swapU)
    rw [extended_swap_pack] at h'
    exact necessary_K1_extended k _ mid h'

  have real_psd_of_complex {I : Type} [Fintype I] [DecidableEq I]
      (M : Matrix I I ℝ) (h : (M.map Complex.ofReal).PosSemidef) : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      have he := congrFun (congrFun h.isHermitian i) j
      have hr := congrArg Complex.re he
      simpa [Matrix.conjTranspose_apply, Matrix.map_apply] using hr
    · intro x
      have hp := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
      have he : star (fun i => (x i : ℂ)) ⬝ᵥ ((M.map Complex.ofReal) *ᵥ (fun i => (x i : ℂ))) =
          ((star x ⬝ᵥ (M *ᵥ x) : ℝ) : ℂ) := by
        simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
          ← Complex.ofReal_sum, ← Complex.ofReal_mul]
      rw [he] at hp
      exact Complex.zero_le_real.mp hp

  have KC1_map (l : Fin 9 → ℝ) : KC1 l=(K1 l).map Complex.ofReal := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [KC1, K1, Matrix.map_apply]

  have KC2_map (l : Fin 9 → ℝ) : KC2 l=(K2 l).map Complex.ofReal := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff,KC2,KC1,flip56,Equiv.swap_apply_def,K2,Matrix.map_apply, Fin.reduceEq, Fin.reduceFinMk]

  have appt_local_reindex {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
      [DecidableEq A] [DecidableEq B] [DecidableEq C]
      (e : C ≃ B) {M : Matrix (A × B) (A × B) ℂ} (h : APPT M) :
      APPT (M.submatrix (Equiv.prodCongr (Equiv.refl A) e) (Equiv.prodCongr (Equiv.refl A) e)) := by
    let f : (A × C) ≃ (A × B) := Equiv.prodCongr (Equiv.refl A) e
    intro U
    let V : unitaryGroup (A × B) ℂ := ⟨(U : Matrix (A × C) (A × C) ℂ).submatrix f.symm f.symm, by
      rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_submatrix,
        submatrix_mul_equiv _ _ _ f.symm _]
      have hu : (U : Matrix (A × C) (A × C) ℂ)*(U : Matrix (A × C) (A × C) ℂ)ᴴ=1 := by
        simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp U.property
      simp [hu]⟩
    have hp := (h V).submatrix f
    change (partialTranspose ((U : Matrix (A × C) (A × C) ℂ)*M.submatrix f f*(U : Matrix (A × C) (A × C) ℂ)ᴴ)).PosSemidef
    convert hp using 1
    have he : (U : Matrix (A × C) (A × C) ℂ)*M.submatrix f f*(U : Matrix (A × C) (A × C) ℂ)ᴴ =
        ((V : Matrix (A × B) (A × B) ℂ)*M*(V : Matrix (A × B) (A × B) ℂ)ᴴ).submatrix f f := by
      change _ = ((U : Matrix (A × C) (A × C) ℂ).submatrix f.symm f.symm * M *
        ((U : Matrix (A × C) (A × C) ℂ).submatrix f.symm f.symm)ᴴ).submatrix f f
      rw [← Matrix.submatrix_mul_equiv _ _ _ f _, ← Matrix.submatrix_mul_equiv _ _ _ f _]
      simp [conjTranspose_submatrix, Matrix.submatrix_submatrix]
    rw [he]
    rfl

  let packedFin (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ) :
      Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ :=
    (diagonal (packExtended k l mid)).submatrix
      (Equiv.prodCongr (Equiv.refl (Fin 3)) finSumFinEquiv.symm)
      (Equiv.prodCongr (Equiv.refl (Fin 3)) finSumFinEquiv.symm)

  have necessary_both_fin (k : ℕ) (l : Fin 9 → ℝ) (mid : Fin 3 × Fin k → ℂ)
      (V : unitaryGroup (Fin 3 × Fin (3+k)) ℂ)
      (h : APPT ((V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)*packedFin k l mid*
        (V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ)) :
      (K1 l).PosSemidef ∧ (K2 l).PosSemidef := by
    have h' := appt_conjugate h (star V)
    have hv : (V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ*
        (V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    have hp : APPT (packedFin k l mid) := by
      have heq : (star V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)*
          ((V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)*packedFin k l mid*
            (V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ)*
          (star V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ=packedFin k l mid := by
        simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_conjTranspose]
        calc
          _ = ((V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ*V)*packedFin k l mid*
              ((V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ*V) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hv,one_mul,mul_one]
      simp only [Unitary.coe_star] at h'
      rw [heq] at h'
      exact h'
    have ht := appt_local_reindex finSumFinEquiv hp
    have hd : APPT (diagonal (packExtended k l mid)) := by
      convert ht using 1
      ext ⟨i,j⟩ ⟨a,b⟩
      simp [packedFin, Matrix.submatrix_apply]
    have hc := And.intro (necessary_K1_extended k l mid hd) (necessary_K2_extended k l mid hd)
    rw [KC1_map, KC2_map] at hc
    exact ⟨real_psd_of_complex _ hc.1, real_psd_of_complex _ hc.2⟩

  let packIndex : (Fin 3 × Fin 3) → Fin 9 := fun (i,j) =>
    if i=0 then (if j=0 then 8 else if j=1 then 7 else 5)
    else if i=1 then (if j=0 then 0 else if j=1 then 6 else 4)
    else (if j=0 then 1 else if j=1 then 2 else 3)

  let packEquiv : (Fin 3 × Fin 3) ≃ Fin 9 := Equiv.ofBijective packIndex (by decide +kernel)

  let boundaryMiddleEquiv (k : ℕ) : (Fin 9 ⊕ Fin (3*k)) ≃ Fin (3*(3+k)) :=
    (Equiv.sumCongr ((@finSumFinEquiv 3 6).symm : Fin 9 ≃ Fin 3 ⊕ Fin 6) (Equiv.refl _)).trans
      ((Equiv.sumAssoc (Fin 3) (Fin 6) (Fin (3*k))).trans
        ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
          ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
            (finSumFinEquiv.trans (finCongr (by omega))))))

  let fullPackingEquiv (k : ℕ) : (Fin 3 × Fin (3+k)) ≃ Fin (3*(3+k)) :=
    (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv.symm).trans
      ((((Equiv.prodSumDistrib (Fin 3) (Fin 3) (Fin k)).symm)).symm.trans
        ((Equiv.sumCongr packEquiv finProdFinEquiv).trans (boundaryMiddleEquiv k)))

  let packedBoundaryValues (k : ℕ) (l : Fin (3*(3+k)) → ℝ) : Fin 9 → ℝ :=
    fun q => l (boundaryMiddleEquiv k (Sum.inl q))

  let middleValues (k : ℕ) (l : Fin (3*(3+k)) → ℝ) : Fin 3 × Fin k → ℂ :=
    fun q => (l (boundaryMiddleEquiv k (Sum.inr (finProdFinEquiv q))) : ℂ)

  have packedFin_full (k : ℕ) (l : Fin (3*(3+k)) → ℝ) :
      packedFin k (packedBoundaryValues k l) (middleValues k l) =
        diagonal (fun q => (l (fullPackingEquiv k q) : ℂ)) := by
    unfold packedFin
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext ⟨i,j⟩
    change packExtended k (packedBoundaryValues k l) (middleValues k l) (i,finSumFinEquiv.symm j)=_
    generalize he : finSumFinEquiv.symm j=z
    rcases z with z|z
    · fin_cases i <;> fin_cases z <;>
        simp [packExtended,pack,fullPackingEquiv,he,Equiv.prodSumDistrib,packEquiv,packIndex,packedBoundaryValues]
    · simp [packExtended,fullPackingEquiv,he,Equiv.prodSumDistrib,middleValues]

  have necessary_ordered_spectrum (k : ℕ) (l : Fin (3*(3+k)) → ℝ)
      (V : unitaryGroup (Fin 3 × Fin (3+k)) ℂ)
      (h : APPT ((V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)*
        diagonal (fun q => (l (fullPackingEquiv k q) : ℂ))*
        (V : Matrix (Fin 3 × Fin (3+k)) (Fin 3 × Fin (3+k)) ℂ)ᴴ)) :
      (K1 (packedBoundaryValues k l)).PosSemidef ∧
        (K2 (packedBoundaryValues k l)).PosSemidef := by
    rw [← packedFin_full] at h
    exact necessary_both_fin k _ _ V h

  have appt_unconjugate {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (M : Matrix (A × B) (A × B) ℂ) (V : unitaryGroup (A × B) ℂ)
      (h : APPT ((V : Matrix (A × B) (A × B) ℂ)*M*(V : Matrix (A × B) (A × B) ℂ)ᴴ)) : APPT M := by
    have h' := appt_conjugate h (star V)
    have hv : (V : Matrix (A × B) (A × B) ℂ)ᴴ*(V : Matrix (A × B) (A × B) ℂ)=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    have heq : (star V : Matrix (A × B) (A × B) ℂ)*
        ((V : Matrix (A × B) (A × B) ℂ)*M*(V : Matrix (A × B) (A × B) ℂ)ᴴ)*
        (star V : Matrix (A × B) (A × B) ℂ)ᴴ=M := by
      simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
      calc
        _ = ((V : Matrix (A × B) (A × B) ℂ)ᴴ*V)*M*((V : Matrix (A × B) (A × B) ℂ)ᴴ*V) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hv,one_mul,mul_one]
    simp only [Unitary.coe_star] at h'
    rw [heq] at h'
    exact h'

  have unitary_purity_trace {I : Type} [Fintype I] [DecidableEq I]
      (M : Matrix I I ℂ) (V : unitaryGroup I ℂ) :
      (((V : Matrix I I ℂ)*M*(V : Matrix I I ℂ)ᴴ)*
        ((V : Matrix I I ℂ)*M*(V : Matrix I I ℂ)ᴴ)).trace=(M*M).trace := by
    have hv : (V : Matrix I I ℂ)ᴴ*(V : Matrix I I ℂ)=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    have he : ((V : Matrix I I ℂ)*M*(V : Matrix I I ℂ)ᴴ)*
        ((V : Matrix I I ℂ)*M*(V : Matrix I I ℂ)ᴴ) =
          (V : Matrix I I ℂ)*(M*M)*(V : Matrix I I ℂ)ᴴ := by
      calc
        _ = (V : Matrix I I ℂ)*M*((V : Matrix I I ℂ)ᴴ*V)*M*(V : Matrix I I ℂ)ᴴ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hv,mul_one]; simp only [Matrix.mul_assoc]
    rw [he, Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc,hv,one_mul]


  have permutation_conjugate {I : Type} [Fintype I] [DecidableEq I]
      (e : Equiv.Perm I) (M : Matrix I I ℂ) :
      (permutationU e : Matrix I I ℂ)*M*(permutationU e : Matrix I I ℂ)ᴴ=M.submatrix e e := by
    change e.permMatrix ℂ*M*(e.permMatrix ℂ)ᴴ=M.submatrix e e
    rw [Matrix.conjTranspose_permMatrix]
    change e.toPEquiv.toMatrix*M*(e⁻¹).toPEquiv.toMatrix=M.submatrix e e
    rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
    rfl

  have unitary_trace {I : Type} [Fintype I] [DecidableEq I]
      (M : Matrix I I ℂ) (V : unitaryGroup I ℂ) :
      ((V : Matrix I I ℂ)*M*(V : Matrix I I ℂ)ᴴ).trace=M.trace := by
    have hv : (V : Matrix I I ℂ)ᴴ*(V : Matrix I I ℂ)=1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc,hv,one_mul]

  have packed_trace (k : ℕ) (l : Fin (3*(3+k)) → ℝ) :
      (diagonal (fun q => (l (fullPackingEquiv k q) : ℂ))).trace=
        ((∑ i, l i : ℝ) : ℂ) := by
    rw [trace_diagonal]
    have he := (fullPackingEquiv k).sum_comp (fun i => (l i : ℂ))
    rw [he]
    simp

  have packed_purity (k : ℕ) (l : Fin (3*(3+k)) → ℝ) :
      (diagonal (fun q => (l (fullPackingEquiv k q) : ℂ))*
        diagonal (fun q => (l (fullPackingEquiv k q) : ℂ))).trace=
        ((∑ i, (l i)^2 : ℝ) : ℂ) := by
    rw [diagonal_mul_diagonal, trace_diagonal]
    have he := (fullPackingEquiv k).sum_comp (fun i => (l i : ℂ)*(l i : ℂ))
    rw [he]
    simp [pow_two]

  let I := Fin 3 × Fin (3+k)
  let H := hrho.isHermitian
  have hc : Fintype.card I=3*(3+k) := by simp [I,Fintype.card_prod]
  let f : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
  let l : Fin (3*(3+k)) → ℝ := fun i => H.eigenvalues₀ (Fin.cast hc.symm i)
  let e : Equiv.Perm I := (fullPackingEquiv k).trans ((finCongr hc.symm).trans f)
  let D := diagonal (fun i : I => (H.eigenvalues i : ℂ))
  let P := diagonal (fun q => (l (fullPackingEquiv k q) : ℂ))
  have hspec : rho=(H.eigenvectorUnitary : Matrix I I ℂ)*D*(H.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
    simpa [D,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Function.comp_def] using H.spectral_theorem
  have hpacked : (permutationU e : Matrix I I ℂ)*D*(permutationU e : Matrix I I ℂ)ᴴ=P := by
    rw [permutation_conjugate,Matrix.submatrix_diagonal_equiv]
    congr 1
    funext q
    simp [D,P,e,l,Matrix.IsHermitian.eigenvalues,f]
  have hd : APPT D := by
    rw [hspec] at happt
    exact appt_unconjugate D H.eigenvectorUnitary happt
  have hp := appt_conjugate hd (permutationU e)
  rw [hpacked] at hp
  have hord : Antitone l := by
    intro i j hij
    exact H.eigenvalues₀_antitone (show Fin.cast hc.symm i ≤ Fin.cast hc.symm j from hij)
  have hnonneg (i) : 0 ≤ l i := by
    have hn := hrho.eigenvalues_nonneg (f (Fin.cast hc.symm i))
    simpa [Matrix.IsHermitian.eigenvalues,f,l,H] using hn
  have ht : ∑ i, l i=1 := by
    have htD : D.trace=1 := by rw [hspec,unitary_trace] at htrace; exact htrace
    have htp := unitary_trace D (permutationU e)
    rw [hpacked] at htp
    change (diagonal (fun q => (l (fullPackingEquiv k q) : ℂ))).trace=D.trace at htp
    rw [packed_trace,htD] at htp
    exact_mod_cast htp
  have hpur : (rho*rho).trace=(P*P).trace := by
    rw [hspec,unitary_purity_trace]
    have he := unitary_purity_trace D (permutationU e)
    rw [hpacked] at he
    exact he.symm
  have hn := necessary_ordered_spectrum k l (1 : unitaryGroup I ℂ) (by simpa [P] using hp)
  have boundary_left_value (k : ℕ) (q : Fin 9) :
      (boundaryMiddleEquiv k (Sum.inl q)).val = if q.val<3 then q.val else 3*k+q.val := by
    fin_cases q <;> simp [boundaryMiddleEquiv, finSumFinEquiv, Equiv.sumAssoc, Fin.addCases] <;> omega
  have hbv : packedBoundaryValues k l = boundaryValues k l := by
    funext q
    apply congrArg l
    apply Fin.ext
    rw [boundary_left_value]
    split_ifs <;> rfl
  rw [hbv] at hn
  refine ⟨l, hord, hnonneg, ht, hn.1, hn.2, ?_⟩
  rw [hpur]
  dsimp only [P]
  rw [packed_purity, Complex.ofReal_re]

#print axioms spectral_reduction
#check bell
#check extendedBell
#check extendUnitary
#check permutationU
#check swapU
end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
