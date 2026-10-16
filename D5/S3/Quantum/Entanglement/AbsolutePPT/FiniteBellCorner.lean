/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiniteBellCorner
   mirror-E: none(waiver:kernel-checked-spectral-construction)
   anchors: []
   utility: none
   digest: Every finite bipartite APPT density matrix with both local dimensions at least three satisfies both Bell-corner spectral LMIs. -/

/-
proof_shape: spectral_reduction and every construction lemma are bind-only.
The finite complement, extended Bell tests, PSD compression, sorted
spectral diagonalization and moment identities instantiate existing
results and normalize their parameters. They supply no standalone
escape witness. spectral_reduction is consumed by
QuadbitQuintitMaximumPurity.density_bound, whose live upper-bound path
continues through DimensionTwentySpectralPurityBound.spectral_purity_bound
and the structural SpectralBoundaryTransfer.spectral_bound_transfer.
All private construction helpers are consumed by spectral_reduction.
The product partial-transpose identity is definitional; no arbitrary
full packing is commuted through partial transpose.
utility:none rationale: These helpers organize symbolic matrix and
unitary applications, not a new finite certificate or enumeration.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritHildebrandSufficiency

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner

noncomputable section

open QutritPerturbationAttainment QutritSpectralReduction
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)


private abbrev J := Fin 3 × Fin 3

private def boundaryMiddleEquiv (N : ℕ) (hN : 9 ≤ N) :
    (Fin 9 ⊕ Fin (N-9)) ≃ Fin N :=
  (Equiv.sumCongr ((@finSumFinEquiv 3 6).symm : Fin 9 ≃ Fin 3 ⊕ Fin 6)
    (Equiv.refl _)).trans
    ((Equiv.sumAssoc (Fin 3) (Fin 6) (Fin (N-9))).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
        ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
          (finSumFinEquiv.trans (finCongr (by omega))))))

def boundaryValues (N : ℕ) (hN : 9 ≤ N) (l : Fin N → ℝ) : Fin 9 → ℝ :=
  fun q => l (if h : q.val < 3 then ⟨q.val, by omega⟩ else ⟨N-9+q.val, by omega⟩)


variable {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)

private def corner (p : J) : Fin m × Fin n := (Fin.castLE hm p.1, Fin.castLE hn p.2)

private theorem corner_injective : Function.Injective (corner hm hn) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun z => z.1.val) h
  · exact congrArg (fun z => z.2.val) h

private def cornerEquiv : (J ⊕ Fin (m*n-9)) ≃ (Fin m × Fin n) := by
  classical
  let c := corner hm hn
  let C := {z : Fin m × Fin n // z ∉ Set.range c}
  let e : (J ⊕ C) ≃ (Fin m × Fin n) :=
    (Equiv.sumCongr (Equiv.ofInjective c (corner_injective hm hn))
      (Equiv.refl C)).trans (Equiv.sumCompl (fun z => z ∈ Set.range c))
  have hcard : Fintype.card C = m*n-9 := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
    omega
  exact (Equiv.sumCongr (Equiv.refl J) (Fintype.equivFinOfCardEq hcard).symm).trans e

@[simp] private theorem cornerEquiv_inl (p : J) :
    cornerEquiv hm hn (Sum.inl p) = corner hm hn p := by
  classical
  simp [cornerEquiv, Equiv.ofInjective_apply]

@[simp] private theorem cornerEquiv_symm_corner (p : J) :
    (cornerEquiv hm hn).symm (corner hm hn p) = Sum.inl p := by
  rw [← cornerEquiv_inl hm hn p, Equiv.symm_apply_apply]

local notation "I" => (Fin m × Fin n)
local notation "c" => corner hm hn
local notation "ce" => cornerEquiv hm hn

private noncomputable def packed (l : Fin 9 → ℝ) (mid : Fin (m*n-9) → ℂ) : Matrix I I ℂ :=
  diagonal (fun i => Sum.elim (pack l) mid ((ce).symm i))

private theorem product_partialTranspose {A B C D : Type}
    (a : C → A) (b : D → B) (M : Matrix (A × B) (A × B) ℂ) :
    (partialTranspose M).submatrix (Prod.map a b) (Prod.map a b) =
      partialTranspose (M.submatrix (Prod.map a b) (Prod.map a b)) := rfl

private theorem corner_partialTranspose (M : Matrix I I ℂ) :
    (partialTranspose M).submatrix (fun i => c (i,i)) (fun i => c (i,i)) =
      (partialTranspose (M.submatrix c c)).submatrix
        (fun i => (i,i)) (fun i => (i,i)) := by
  exact congrArg (fun T : Matrix J J ℂ => T.submatrix (fun i => (i,i)) (fun i => (i,i)))
    (product_partialTranspose (Fin.castLE hm) (Fin.castLE hn) M)

private theorem corner_conjugate (V : unitaryGroup J ℂ) (x : J → ℂ) (y : Fin (m*n-9) → ℂ) :
    ((extendUnitaryAlong ce V : Matrix I I ℂ) *
      diagonal (fun i => Sum.elim x y ((ce).symm i)) *
      (extendUnitaryAlong ce V : Matrix I I ℂ)ᴴ).submatrix c c =
      (V : Matrix J J ℂ) * diagonal x * (V : Matrix J J ℂ)ᴴ := by
  rw [extendUnitaryAlong_diagonal]
  ext i j
  simp [Matrix.submatrix_apply]

private theorem necessary_K1 (l : Fin 9 → ℝ) (mid : Fin (m*n-9) → ℂ)
    (h : APPT ((packed hm hn) l mid)) : (KC1 l).PosSemidef := by
  let B : unitaryGroup J ℂ := ⟨bell, bell_mem_unitaryGroup⟩
  have hp := (h (extendUnitaryAlong ce B)).submatrix (fun i => c (i,i))
  change ((partialTranspose ((extendUnitaryAlong ce B : Matrix I I ℂ) *
    (packed hm hn) l mid * (extendUnitaryAlong ce B : Matrix I I ℂ)ᴴ)).submatrix
      (fun i => c (i,i)) (fun i => c (i,i))).PosSemidef at hp
  rw [(corner_partialTranspose hm hn)] at hp
  unfold packed at hp
  rw [(corner_conjugate hm hn)] at hp
  change ((partialTranspose (bell * diagonal (pack l) * bellᴴ)).submatrix
    (fun i => (i,i)) (fun i => (i,i))).PosSemidef at hp
  rw [bell_pt_principal] at hp
  have hs := hp.smul (show (0 : ℂ) ≤ 2 by norm_num)
  convert hs using 1 <;> ext i j <;> simp

private theorem packed_swap (l : Fin 9 → ℝ) (mid : Fin (m*n-9) → ℂ) :
    (extendUnitaryAlong ce (permutationU swap56) : Matrix I I ℂ) *
      (packed hm hn) l mid *
      (extendUnitaryAlong ce (permutationU swap56) : Matrix I I ℂ)ᴴ =
      (packed hm hn) (flip56 l) mid := by
  unfold packed
  rw [extendUnitaryAlong_diagonal, swap_pack, fromBlocks_diagonal,
    Matrix.submatrix_diagonal_equiv]
  rfl

private theorem necessary_both (l : Fin 9 → ℝ) (mid : Fin (m*n-9) → ℂ)
    (h : APPT ((packed hm hn) l mid)) : (K1 l).PosSemidef ∧ (K2 l).PosSemidef := by
  have h1 := (necessary_K1 hm hn) l mid h
  have h' := appt_conjugate h (extendUnitaryAlong ce (permutationU swap56))
  rw [(packed_swap hm hn)] at h'
  have h2 : (KC2 l).PosSemidef := (necessary_K1 hm hn) (flip56 l) mid h'
  rw [KC1_map] at h1
  rw [KC2_map] at h2
  exact ⟨real_psd_of_complex _ h1, real_psd_of_complex _ h2⟩

include hm hn in
private theorem total_ge : 9 ≤ m*n := le_trans (by decide : 9 ≤ 3*3) (Nat.mul_le_mul hm hn)

local notation "bm" => boundaryMiddleEquiv (m*n) (total_ge hm hn)

private noncomputable def fullPackingEquiv : I ≃ Fin (m*n) :=
  (ce).symm.trans ((Equiv.sumCongr packEquiv (Equiv.refl _)).trans bm)

private def packedBoundaryValues (l : Fin (m*n) → ℝ) : Fin 9 → ℝ :=
  fun q => l (bm (Sum.inl q))

private noncomputable def middleValues (l : Fin (m*n) → ℝ) : Fin (m*n-9) → ℂ :=
  fun q => (l (bm (Sum.inr q)) : ℂ)

private theorem packed_full (l : Fin (m*n) → ℝ) :
    (packed hm hn) (packedBoundaryValues hm hn l) ((middleValues hm hn) l) =
      diagonal (fun q => (l ((fullPackingEquiv hm hn) q) : ℂ)) := by
  unfold packed
  congr 1
  funext q
  generalize he : (ce).symm q = z
  rcases z with p | p
  · rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [pack, packedBoundaryValues, fullPackingEquiv, he, packEquiv, packIndex]
  · simp [middleValues, fullPackingEquiv, he]

theorem spectral_reduction (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    ∃ l : Fin (m*n) → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
      (K1 (boundaryValues (m*n) (total_ge hm hn) l)).PosSemidef ∧ (K2 (boundaryValues (m*n) (total_ge hm hn) l)).PosSemidef ∧
      (rho * rho).trace.re = ∑ i, (l i)^2 := by
  classical
  let H := hrho.isHermitian
  have hc : Fintype.card I = m*n := by simp [Fintype.card_prod]
  let l : Fin (m*n) → ℝ := fun i => H.eigenvalues₀ (Fin.cast hc.symm i)
  let P := diagonal (fun q => (l ((fullPackingEquiv hm hn) q) : ℂ))
  obtain ⟨U, hU⟩ := QutritHildebrandSufficiency.OrderedDiagonalization.sorted_diagonalization
    hc rho H (fullPackingEquiv hm hn)
  change rho = (U : Matrix I I ℂ) * P * (U : Matrix I I ℂ)ᴴ at hU
  have hp : APPT P := by
    rw [hU] at happt
    exact appt_unconjugate P U happt
  have hboth : (K1 (boundaryValues (m*n) (total_ge hm hn) l)).PosSemidef ∧
      (K2 (boundaryValues (m*n) (total_ge hm hn) l)).PosSemidef := by
    have hb : packedBoundaryValues hm hn l = boundaryValues (m*n) (total_ge hm hn) l := by
      funext q
      apply congrArg l
      apply Fin.ext
      fin_cases q <;> simp [packedBoundaryValues, boundaryValues, boundaryMiddleEquiv,
        finSumFinEquiv, Equiv.sumAssoc, Fin.addCases] <;> omega
    rw [← hb]
    apply (necessary_both hm hn) _ ((middleValues hm hn) l)
    rw [(packed_full hm hn)]
    exact hp
  have hord : Antitone l := by
    intro i j hij
    exact H.eigenvalues₀_antitone (show Fin.cast hc.symm i ≤ Fin.cast hc.symm j from hij)
  have hnonneg (i) : 0 ≤ l i := by
    let f : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
    have heig := hrho.eigenvalues_nonneg (f (Fin.cast hc.symm i))
    simpa [Matrix.IsHermitian.eigenvalues, f, l, H] using heig
  have htP : P.trace = ((∑ i, l i : ℝ) : ℂ) := by
    dsimp only [P]
    rw [trace_diagonal]
    have he := (fullPackingEquiv hm hn).sum_comp (fun i => (l i : ℂ))
    rw [he]
    simp
  have ht : ∑ i, l i = 1 := by
    rw [hU, unitary_trace, htP] at htrace
    exact_mod_cast htrace
  have hpurP : (P * P).trace = ((∑ i, (l i)^2 : ℝ) : ℂ) := by
    dsimp only [P]
    rw [diagonal_mul_diagonal, trace_diagonal]
    have he := (fullPackingEquiv hm hn).sum_comp (fun i => (l i : ℂ) * (l i : ℂ))
    rw [he]
    simp [pow_two]
  refine ⟨l, hord, hnonneg, ht, hboth.1, hboth.2, ?_⟩
  rw [hU, unitary_purity_trace, hpurP, Complex.ofReal_re]

#print axioms spectral_reduction

end

end D5.S3.Quantum.Entanglement.AbsolutePPT.FiniteBellCorner
