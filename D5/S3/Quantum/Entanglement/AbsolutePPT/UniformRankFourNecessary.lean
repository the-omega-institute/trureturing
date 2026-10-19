/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary
   mirror-E: none(waiver:product-local-unitary-construction)
   anchors: []
   utility: none
   digest: A genuine four-by-four product corner forces the first-six versus last-ten APPT mass inequality in all larger local dimensions. -/

/-
proof_shape: uniform_rank_four_necessary: content
admission_basis: escape-witness
escape_witness: Six antisymmetric and ten symmetric/diagonal columns form a
  concrete product-local unitary; a finite permutation extends their prescribed
  spectral assignment over the actual complement. Trace duality and APPT
  positivity give the signed mass inequality without spectral nondegeneracy.
Private finite-algebra and packing helpers are consumed by this construction.
Literature: Library/QuantumStates/hildebrand2007pptspectra.md.
This theorem is dimension-general at fixed rank four, not generic in rank.
Disclosure: https://github.com/the-omega-institute/trureturing/issues/17734
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
import D5.S3.Quantum.Matrix.PartialTransposeTrace
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
open QutritPerturbationAttainment QutritSpectralReduction
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Matrix.PartialTransposeTrace

noncomputable section

/-- Sum of the first k coordinates; out-of-range terms are zero. -/
def sumFirst {N : ℕ} (k : ℕ) (l : Fin N → ℝ) : ℝ :=
  ∑ i : Fin k, if h : i.val < N then l ⟨i.val,h⟩ else 0

/-- Sum of the last k coordinates when k <= N. -/
def sumLast {N : ℕ} (k : ℕ) (l : Fin N → ℝ) : ℝ :=
  ∑ i : Fin k, if h : N-k+i.val < N then l ⟨N-k+i.val,h⟩ else 0

private abbrev J := Fin 4 × Fin 4

private def rankIndex : J → Fin 16 := fun p =>
  (!![6,10,11,12; 0,7,13,14; 1,3,8,15; 2,4,5,9] : Matrix (Fin 4) (Fin 4) (Fin 16)) p.1 p.2

private theorem rankIndex_injective : Function.Injective rankIndex := by
  decide +kernel

/-- Upper-triangular columns are symmetric, lower-triangular columns are
antisymmetric, and product diagonals are fixed. -/
private def pairRotation : Matrix J J ℂ := fun (i,j) (k,l) =>
  if i=j then if (i,j)=(k,l) then 1 else 0
  else if (i,j)=(k,l) then
    (if i<j then (Real.sqrt 2 : ℂ)⁻¹ else -(Real.sqrt 2 : ℂ)⁻¹)
  else if (i,j)=(l,k) then (Real.sqrt 2 : ℂ)⁻¹ else 0

private theorem pairRotation_unitary : pairRotation ∈ unitaryGroup J ℂ := by
  rw [mem_unitaryGroup_iff]
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff,
      pairRotation, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.reduceEq, Fin.reduceFinMk, Fin.reduceLT, c_star, c_square]
  all_goals simp only [show (starRingEnd ℂ) (Real.sqrt 2 : ℂ)⁻¹ =
    (Real.sqrt 2 : ℂ)⁻¹ by simp, c_square]
  all_goals norm_num

private def eta : J → ℂ := fun p => if p.1=p.2 then 1 else 0

private def swap : Matrix J J ℂ := fun p q => if p=(q.2,q.1) then 1 else 0

private theorem eta_partialTranspose :
    partialTranspose (vecMulVec eta (star eta)) = swap := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [partialTranspose, vecMulVec_apply, eta, swap, Prod.mk.injEq]

private theorem rotation_trace (z : Fin 16 → ℝ) :
    ((pairRotation * diagonal (fun p => (z (rankIndex p) : ℂ)) * pairRotationᴴ) *
      swap).trace =
    (((∑ i : Fin 10, z ⟨6+i.val,by omega⟩) -
      (∑ i : Fin 6, z ⟨i.val,by omega⟩) : ℝ) : ℂ) := by
  have hs (M : Matrix J J ℂ) :
      (M * swap).trace = ∑ p : J, M p (p.2,p.1) := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, swap]
  rw [hs]
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff,
    Matrix.mul_diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ, pairRotation, rankIndex, swap,
    Fin.reduceEq, Fin.reduceFinMk, Fin.reduceLT, c_star, c_square]
  ring_nf
  all_goals simp [pow_two, c_square]
  all_goals ring

private theorem core_nonnegative (z : Fin 16 → ℝ)
    (hp : (partialTranspose
      (pairRotation * diagonal (fun p => (z (rankIndex p) : ℂ)) * pairRotationᴴ)).PosSemidef) :
    (∑ i : Fin 6, z ⟨i.val,by omega⟩) ≤ ∑ i : Fin 10, z ⟨6+i.val,by omega⟩ := by
  have h := hp.dotProduct_mulVec_nonneg eta
  rw [partial_transpose_trace_duality, eta_partialTranspose, rotation_trace] at h
  have hr : (0 : ℝ) ≤ (∑ i : Fin 10, z ⟨6+i.val,by omega⟩) -
      (∑ i : Fin 6, z ⟨i.val,by omega⟩) := by
    exact Complex.zero_le_real.mp h
  linarith

private def slot {N : ℕ} (hN : 16 ≤ N) (i : Fin 16) : Fin N :=
  if h : i.val < 6 then ⟨i.val,by omega⟩ else ⟨N-16+i.val,by omega⟩

private theorem slot_injective {N : ℕ} (hN : 16 ≤ N) :
    Function.Injective (slot hN) := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  by_cases ha : a.val < 6 <;> by_cases hb : b.val < 6 <;>
    simp [slot, ha, hb] at hv <;> omega

private def corner {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) (p : J) : Fin m × Fin n :=
  (Fin.castLE hm p.1, Fin.castLE hn p.2)

private theorem corner_injective {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) :
    Function.Injective (corner hm hn) := by
  intro a b h
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun p : Fin m × Fin n => p.1.val) h
  · apply Fin.ext
    exact congrArg (fun p : Fin m × Fin n => p.2.val) h

private abbrev Outside {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) :=
  {p : Fin m × Fin n // p ∉ Set.range (corner hm hn)}

private instance outsideFintype {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) :
    Fintype (Outside hm hn) := Fintype.ofFinite _

private def cornerEquiv {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) :
    (J ⊕ Outside hm hn) ≃ (Fin m × Fin n) := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective (corner hm hn) (corner_injective hm hn))
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (corner hm hn)))

@[simp] private theorem cornerEquiv_inl {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n) (p : J) :
    cornerEquiv hm hn (Sum.inl p) = corner hm hn p := rfl

@[simp] private theorem cornerEquiv_symm_corner {m n : ℕ}
    (hm : 4 ≤ m) (hn : 4 ≤ n) (p : J) :
    (cornerEquiv hm hn).symm (corner hm hn p) = Sum.inl p :=
  (cornerEquiv hm hn).symm_apply_apply (Sum.inl p)

private theorem conjugate_corner {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n)
    (d : Fin m × Fin n → ℂ) (V : unitaryGroup J ℂ) :
    (((extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ) * diagonal d *
      (extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ)ᴴ).submatrix
      (corner hm hn) (corner hm hn)) =
    (V : Matrix J J ℂ) * diagonal (fun p => d (corner hm hn p)) * (V : Matrix J J ℂ)ᴴ := by
  have hd : diagonal d = diagonal (fun p =>
      Sum.elim (fun q => d (corner hm hn q))
        (fun q => d (cornerEquiv hm hn (Sum.inr q))) ((cornerEquiv hm hn).symm p)) := by
    congr 1
    funext p
    obtain ⟨q,rfl⟩ := (cornerEquiv hm hn).surjective p
    cases q <;> simp
  rw [hd, extendUnitaryAlong_diagonal]
  ext i j
  simp [Matrix.submatrix_apply]

/-- Literal APPT on an arbitrary labelled real diagonal spectrum forces the
rank-four uniform mass inequality. Ordering, nonnegativity, normalization,
strictly positive eigenvalues and distinct eigenvalues are unnecessary. -/
theorem uniform_rank_four_necessary {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n)
    (e : (Fin m × Fin n) ≃ Fin (m*n)) (l : Fin (m*n) → ℝ)
    (happt : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    sumFirst 6 l ≤ sumLast 10 l := by
  classical
  have hN : 16 ≤ m*n := by
    have h := Nat.mul_le_mul hm hn
    norm_num at h ⊢
    exact h
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair
    (corner hm hn) (fun q => e.symm (slot hN (rankIndex q)))
    (corner_injective hm hn) (e.symm.injective.comp
      ((slot_injective hN).comp rankIndex_injective))
  let P := permutationU p
  let d : Fin m × Fin n → ℂ := fun q => (l (e (p q)) : ℂ)
  have hd : (P : Matrix _ _ ℂ) * diagonal (fun q => (l (e q) : ℂ)) *
      (P : Matrix _ _ ℂ)ᴴ = diagonal d := by
    change p.permMatrix ℂ * _ * (p.permMatrix ℂ)ᴴ = _
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
    change (diagonal (fun q => (l (e q) : ℂ))).submatrix p p = diagonal d
    exact Matrix.submatrix_diagonal_equiv (fun q => (l (e q) : ℂ)) p
  have hdiag : APPT (diagonal d) := by
    rw [← hd]
    exact appt_conjugate happt P
  let V : unitaryGroup J ℂ := ⟨pairRotation,pairRotation_unitary⟩
  have hpos := (hdiag (extendUnitaryAlong (cornerEquiv hm hn) V)).submatrix (corner hm hn)
  have hlocal : (partialTranspose ((V : Matrix J J ℂ) *
      diagonal (fun q => d (corner hm hn q)) * (V : Matrix J J ℂ)ᴴ)).PosSemidef := by
    change (partialTranspose
      ((((extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ) * diagonal d *
        (extendUnitaryAlong (cornerEquiv hm hn) V : Matrix _ _ ℂ)ᴴ)).submatrix
        (corner hm hn) (corner hm hn))).PosSemidef at hpos
    rw [conjugate_corner] at hpos
    exact hpos
  have hdc : (fun q => d (corner hm hn q)) =
      fun q => (l (slot hN (rankIndex q)) : ℂ) := by
    funext q
    simp [d,hp q]
  rw [hdc] at hlocal
  have hmass := core_nonnegative (fun q => l (slot hN q)) hlocal
  have hf : (∑ i : Fin 6, l (slot hN ⟨i.val,by omega⟩)) = sumFirst 6 l := by
    unfold sumFirst
    apply Finset.sum_congr rfl
    intro i hi
    simp [slot, show i.val < 6 from i.isLt, show i.val < m*n by omega]
  have hl : (∑ i : Fin 10, l (slot hN ⟨6+i.val,by omega⟩)) = sumLast 10 l := by
    unfold sumLast
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos (show m*n-10+i.val < m*n by omega)]
    congr 1
    apply Fin.ext
    simp [slot, show ¬ 6+i.val < 6 by omega]
    omega
  rwa [hf,hl] at hmass

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
