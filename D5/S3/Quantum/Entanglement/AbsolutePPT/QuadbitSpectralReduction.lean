/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralReduction
   mirror-E: none(waiver:kernel-checked-spectral-construction)
   anchors: []
   utility: none
   digest: A genuine local qutrit corner extracts both spectral LMIs from a 4 by 4 APPT state. -/

/-
proof_shape: spectral_reduction: content
escape_witness: an explicit tensor-product corner, with a seven-dimensional
  complement, derives both boundary LMIs from literal four-by-four APPT.
admission_basis: content
Direct frozen dependencies: QutritSpectralReduction,
  QutritHildebrandSufficiency.OrderedDiagonalization.sorted_diagonalization.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritHildebrandSufficiency

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSpectralReduction

noncomputable section

open QutritPerturbationAttainment QutritSpectralReduction
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)


private abbrev I := Fin 4 × Fin 4
private abbrev J := Fin 3 × Fin 3

private def corner (p : J) : I := (Fin.castLE (by omega) p.1, Fin.castLE (by omega) p.2)

private def complement : Fin 7 → I := ![(0,3), (1,3), (2,3), (3,0), (3,1), (3,2), (3,3)]

private def cornerEquiv : (J ⊕ Fin 7) ≃ I :=
  Equiv.ofBijective (Sum.elim corner complement) (by decide +kernel)

@[simp] private theorem cornerEquiv_inl (p : J) : cornerEquiv (Sum.inl p) = corner p := rfl
@[simp] private theorem cornerEquiv_symm_corner (p : J) :
    cornerEquiv.symm (corner p) = Sum.inl p := by
  exact cornerEquiv.symm_apply_apply (Sum.inl p)

private noncomputable def packed (l : Fin 9 → ℝ) (mid : Fin 7 → ℂ) : Matrix I I ℂ :=
  diagonal (fun i => Sum.elim (pack l) mid (cornerEquiv.symm i))

private theorem corner_partialTranspose (M : Matrix I I ℂ) :
    (partialTranspose M).submatrix (fun i => corner (i,i)) (fun i => corner (i,i)) =
      (partialTranspose (M.submatrix corner corner)).submatrix
        (fun i => (i,i)) (fun i => (i,i)) := rfl

private theorem corner_conjugate (V : unitaryGroup J ℂ) (x : J → ℂ) (y : Fin 7 → ℂ) :
    ((extendUnitaryAlong cornerEquiv V : Matrix I I ℂ) *
      diagonal (fun i => Sum.elim x y (cornerEquiv.symm i)) *
      (extendUnitaryAlong cornerEquiv V : Matrix I I ℂ)ᴴ).submatrix corner corner =
      (V : Matrix J J ℂ) * diagonal x * (V : Matrix J J ℂ)ᴴ := by
  rw [extendUnitaryAlong_diagonal]
  ext i j
  simp [Matrix.submatrix_apply]

private theorem necessary_K1 (l : Fin 9 → ℝ) (mid : Fin 7 → ℂ)
    (h : APPT (packed l mid)) : (KC1 l).PosSemidef := by
  let B : unitaryGroup J ℂ := ⟨bell, bell_mem_unitaryGroup⟩
  have hp := (h (extendUnitaryAlong cornerEquiv B)).submatrix (fun i => corner (i,i))
  change ((partialTranspose ((extendUnitaryAlong cornerEquiv B : Matrix I I ℂ) *
    packed l mid * (extendUnitaryAlong cornerEquiv B : Matrix I I ℂ)ᴴ)).submatrix
      (fun i => corner (i,i)) (fun i => corner (i,i))).PosSemidef at hp
  rw [corner_partialTranspose] at hp
  unfold packed at hp
  rw [corner_conjugate] at hp
  change ((partialTranspose (bell * diagonal (pack l) * bellᴴ)).submatrix
    (fun i => (i,i)) (fun i => (i,i))).PosSemidef at hp
  rw [bell_pt_principal] at hp
  have hs := hp.smul (show (0 : ℂ) ≤ 2 by norm_num)
  convert hs using 1 <;> ext i j <;> simp

private theorem packed_swap (l : Fin 9 → ℝ) (mid : Fin 7 → ℂ) :
    (extendUnitaryAlong cornerEquiv (permutationU swap56) : Matrix I I ℂ) *
      packed l mid *
      (extendUnitaryAlong cornerEquiv (permutationU swap56) : Matrix I I ℂ)ᴴ =
      packed (flip56 l) mid := by
  unfold packed
  rw [extendUnitaryAlong_diagonal, swap_pack, fromBlocks_diagonal,
    Matrix.submatrix_diagonal_equiv]
  rfl

private theorem necessary_both (l : Fin 9 → ℝ) (mid : Fin 7 → ℂ)
    (h : APPT (packed l mid)) : (K1 l).PosSemidef ∧ (K2 l).PosSemidef := by
  have h1 := necessary_K1 l mid h
  have h' := appt_conjugate h (extendUnitaryAlong cornerEquiv (permutationU swap56))
  rw [packed_swap] at h'
  have h2 : (KC2 l).PosSemidef := necessary_K1 (flip56 l) mid h'
  rw [KC1_map] at h1
  rw [KC2_map] at h2
  exact ⟨real_psd_of_complex _ h1, real_psd_of_complex _ h2⟩

private def boundaryMiddle (q : Fin 9 ⊕ Fin 7) : Fin 16 :=
  match q with
  | Sum.inl q => if h : q.val < 3 then ⟨q.val, by omega⟩ else ⟨7 + q.val, by omega⟩
  | Sum.inr q => ⟨3 + q.val, by omega⟩

private def boundaryMiddleEquiv : (Fin 9 ⊕ Fin 7) ≃ Fin 16 :=
  Equiv.ofBijective boundaryMiddle (by decide +kernel)

private noncomputable def fullPackingEquiv : I ≃ Fin 16 :=
  cornerEquiv.symm.trans ((Equiv.sumCongr packEquiv (Equiv.refl _)).trans boundaryMiddleEquiv)

def boundaryValues16 (l : Fin 16 → ℝ) : Fin 9 → ℝ :=
  fun q => l (boundaryMiddleEquiv (Sum.inl q))

private noncomputable def middleValues (l : Fin 16 → ℝ) : Fin 7 → ℂ :=
  fun q => (l (boundaryMiddleEquiv (Sum.inr q)) : ℂ)

private theorem packed_full (l : Fin 16 → ℝ) :
    packed (boundaryValues16 l) (middleValues l) =
      diagonal (fun q => (l (fullPackingEquiv q) : ℂ)) := by
  unfold packed
  congr 1
  funext q
  generalize he : cornerEquiv.symm q = z
  rcases z with p | p
  · rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [pack, boundaryValues16, fullPackingEquiv, he, packEquiv, packIndex]
  · simp [middleValues, fullPackingEquiv, he]

theorem spectral_reduction (rho : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    ∃ l : Fin 16 → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
      (K1 (boundaryValues16 l)).PosSemidef ∧ (K2 (boundaryValues16 l)).PosSemidef ∧
      (rho * rho).trace.re = ∑ i, (l i)^2 := by
  let H := hrho.isHermitian
  have hc : Fintype.card I = 16 := by decide
  let l : Fin 16 → ℝ := fun i => H.eigenvalues₀ (Fin.cast hc.symm i)
  let P := diagonal (fun q => (l (fullPackingEquiv q) : ℂ))
  obtain ⟨U, hU⟩ := QutritHildebrandSufficiency.OrderedDiagonalization.sorted_diagonalization
    hc rho H fullPackingEquiv
  change rho = (U : Matrix I I ℂ) * P * (U : Matrix I I ℂ)ᴴ at hU
  have hp : APPT P := by
    rw [hU] at happt
    exact appt_unconjugate P U happt
  have hn : (K1 (boundaryValues16 l)).PosSemidef ∧
      (K2 (boundaryValues16 l)).PosSemidef := by
    apply necessary_both _ (middleValues l)
    rw [packed_full]
    exact hp
  have hord : Antitone l := by
    intro i j hij
    exact H.eigenvalues₀_antitone (show Fin.cast hc.symm i ≤ Fin.cast hc.symm j from hij)
  have hnonneg (i) : 0 ≤ l i := by
    let f : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
    have hn := hrho.eigenvalues_nonneg (f (Fin.cast hc.symm i))
    simpa [Matrix.IsHermitian.eigenvalues, f, l, H] using hn
  have htP : P.trace = ((∑ i, l i : ℝ) : ℂ) := by
    dsimp only [P]
    rw [trace_diagonal]
    have he := fullPackingEquiv.sum_comp (fun i => (l i : ℂ))
    rw [he]
    simp
  have ht : ∑ i, l i = 1 := by
    rw [hU, unitary_trace, htP] at htrace
    exact_mod_cast htrace
  have hpurP : (P * P).trace = ((∑ i, (l i)^2 : ℝ) : ℂ) := by
    dsimp only [P]
    rw [diagonal_mul_diagonal, trace_diagonal]
    have he := fullPackingEquiv.sum_comp (fun i => (l i : ℂ) * (l i : ℂ))
    rw [he]
    simp [pow_two]
  refine ⟨l, hord, hnonneg, ht, hn.1, hn.2, ?_⟩
  rw [hU, unitary_purity_trace, hpurP, Complex.ofReal_re]

#print axioms spectral_reduction

end

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitSpectralReduction
