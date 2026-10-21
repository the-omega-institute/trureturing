/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
   mirror-E: none(waiver:structural-density-transfer)
   anchors: []
   utility: none
   digest: The literal four-by-five APPT purity maximum is 7/121, attained by the diagonal density (3,1^19)/22. -/

/-
proof_shape: spectral_reduction and all finite-corner construction lemmas
  are bind-only helpers consumed by density_bound. Their finite-complement,
  Bell-unitary, compression and diagonalization applications provide no
  independent escape witness.
proof_shape: normalized_ray and normalized_basis_diagonal are bind-only
  helpers, both consumed by result. Their normalization uses the generic
  separable-ray theorem, the exported normalization/PT helpers, and
  rank-one and trace identities.
proof_shape: density_bound and result are content after unfolding the
  same-delivery spectral transfer. The actual finite Bell corner supplies
  the necessary K1/K2 constraints for this physical matrix; the full
  length-twenty upper bound uses the new insertion/deletion inference
  from lengths eighteen and twenty-one through nineteen. The live
  intermediate is SpectralBoundaryTransfer.spectral_bound_transfer,
  not the Bell-corner packaging or the rational attainer arithmetic.
admission_basis: escape-witness, subject to independent combined review.
utility:none rationale: The new inference is a symbolic structural
  transfer over arbitrary ordered spectra and arbitrary complex densities.
  The generic ray formulas are consumed algebraic normalization of an
  existing separable-ray theorem. Every finite-corner and ray helper is
  consumed by the physical result; none delivers a standalone numerical
  certificate. The full physical maximum uses the same-delivery new
  structural transfer, with baseline-frozen endpoint certificates.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritHildebrandSufficiency
import D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped ComplexOrder
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open QutritPerturbationAttainment
open AbsoluteSeparability.LowRankRays

noncomputable section

section FiniteCorner

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

def cornerBoundaryValues (N : ℕ) (hN : 9 ≤ N) (l : Fin N → ℝ) : Fin 9 → ℝ :=
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

theorem product_partialTranspose {A B C D : Type}
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

/-- Both Bell pencils for the actual labelled diagonal, with arbitrary local
dimensions at least three. No ordering, positivity or mass premise is used. -/
theorem diagonal_necessary_both
    (e : (Fin m × Fin n) ≃ Fin (m*n)) (l : Fin (m*n) → ℝ)
    (hdiag : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    (K1 (cornerBoundaryValues (m*n) (total_ge hm hn) l)).PosSemidef ∧
      (K2 (cornerBoundaryValues (m*n) (total_ge hm hn) l)).PosSemidef := by
  classical
  let σ : Equiv.Perm (Fin m × Fin n) := (fullPackingEquiv hm hn).trans e.symm
  have hp : APPT (diagonal (fun p => (l ((fullPackingEquiv hm hn) p) : ℂ))) := by
    have h := appt_conjugate hdiag (permutationU σ)
    rw [permutation_conjugate, Matrix.submatrix_diagonal_equiv] at h
    simpa only [σ, Function.comp_def, Equiv.trans_apply, Equiv.apply_symm_apply] using h
  have hb : packedBoundaryValues hm hn l =
      cornerBoundaryValues (m*n) (total_ge hm hn) l := by
    funext q
    apply congrArg l
    apply Fin.ext
    fin_cases q <;> simp [packedBoundaryValues, cornerBoundaryValues, boundaryMiddleEquiv,
      finSumFinEquiv, Equiv.sumAssoc, Fin.addCases] <;> omega
  rw [← hb]
  apply (necessary_both hm hn) _ ((middleValues hm hn) l)
  rw [(packed_full hm hn)]
  exact hp

/-- One sorted spectrum, retaining APPT of its actual diagonal in the supplied
labelling. This is consumed by the old two-pencil reduction and the rank-four
physical consumer; neither consumer needs a second diagonalization. -/
theorem diagonal_spectral_reduction
    (e : (Fin m × Fin n) ≃ Fin (m*n))
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    ∃ l : Fin (m*n) → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
      APPT (diagonal (fun p => (l (e p) : ℂ))) ∧
      (rho * rho).trace.re = ∑ i, (l i)^2 := by
  classical
  let H := hrho.isHermitian
  have hc : Fintype.card I = m*n := by simp [Fintype.card_prod]
  let l : Fin (m*n) → ℝ := fun i => H.eigenvalues₀ (Fin.cast hc.symm i)
  let P := diagonal (fun q => (l (e q) : ℂ))
  obtain ⟨U, hU⟩ := QutritHildebrandSufficiency.OrderedDiagonalization.sorted_diagonalization
    hc rho H e
  change rho = (U : Matrix I I ℂ) * P * (U : Matrix I I ℂ)ᴴ at hU
  have hp : APPT P := by
    rw [hU] at happt
    exact appt_unconjugate P U happt
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
    have he := e.sum_comp (fun i => (l i : ℂ))
    rw [he]
    simp
  have ht : ∑ i, l i = 1 := by
    rw [hU, unitary_trace, htP] at htrace
    exact_mod_cast htrace
  have hpurP : (P * P).trace = ((∑ i, (l i)^2 : ℝ) : ℂ) := by
    dsimp only [P]
    rw [diagonal_mul_diagonal, trace_diagonal]
    have he := e.sum_comp (fun i => (l i : ℂ) * (l i : ℂ))
    rw [he]
    simp [pow_two]
  refine ⟨l, hord, hnonneg, ht, hp, ?_⟩
  rw [hU, unitary_purity_trace, hpurP, Complex.ofReal_re]

/-- The original public interface is preserved. Both pencils now consume the
same actual diagonal APPT evidence returned by `diagonal_spectral_reduction`. -/
theorem spectral_reduction (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    ∃ l : Fin (m*n) → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧ (∑ i, l i = 1) ∧
      (K1 (cornerBoundaryValues (m*n) (total_ge hm hn) l)).PosSemidef ∧ (K2 (cornerBoundaryValues (m*n) (total_ge hm hn) l)).PosSemidef ∧
      (rho * rho).trace.re = ∑ i, (l i)^2 := by
  obtain ⟨l, ho, hnonneg, ht, hdiag, hpur⟩ :=
    diagonal_spectral_reduction (fullPackingEquiv hm hn) rho hrho htrace happt
  obtain ⟨h1, h2⟩ := diagonal_necessary_both hm hn (fullPackingEquiv hm hn) l hdiag
  exact ⟨l, ho, hnonneg, ht, h1, h2, hpur⟩

end FiniteCorner

/-- The normalized separable ray, for arbitrary local dimensions. -/
def normalizedRay {m n : ℕ} (v : Fin m × Fin n → ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ((1 / (((m*n : ℕ) : ℝ) + 2) : ℝ) : ℂ) •
    (1 + (2 : ℂ) • vecMulVec v (star v))

/-- Normalization preserves the separable ray after every global unitary. -/
theorem normalized_ray {m n : ℕ} (v : Fin m × Fin n → ℂ)
    (hv : star v ⬝ᵥ v = (1 : ℂ)) :
    (normalizedRay v).PosSemidef ∧ (normalizedRay v).trace = 1 ∧
      APPT (normalizedRay v) ∧
      (normalizedRay v * normalizedRay v).trace.re =
        (((m*n : ℕ) : ℝ) + 8) / (((m*n : ℕ) : ℝ) + 2)^2 := by
  let d : ℝ := (m*n : ℕ)
  have hd : 0 < d + 2 := by dsimp [d]; positivity
  have hs : 0 ≤ (1 / (d + 2) : ℝ) := by positivity
  have htr : (vecMulVec v (star v)).trace = (1 : ℂ) := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm, hv]
  have hi : (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).trace = (d : ℂ) := by
    simp [d, Matrix.trace_one, Fintype.card_prod]
  have hm : (1 + (2 : ℂ) • vecMulVec v (star v)) *
      (1 + (2 : ℂ) • vecMulVec v (star v)) =
      1 + (8 : ℂ) • vecMulVec v (star v) := by
    simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, pure_outer_square v hv]
    module
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Matrix.PosSemidef.one.add
      ((posSemidef_vecMulVec_self_star v).smul (by norm_num))).smul
        (Complex.zero_le_real.mpr hs)
  · simp only [normalizedRay, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_smul, hi, htr, smul_eq_mul]
    change ((1 / (d + 2) : ℝ) : ℂ) * ((d : ℂ) + 2 * 1) = 1
    norm_cast
    exact div_mul_cancel₀ 1 hd.ne'
  · intro U
    have hnorm := QuadbitMaximumPurity.norm_of_dot_eq_one _ (unitary_vector_norm U v hv)
    have hsep := separableCone_smul (c := (1 / (d + 2) : ℝ)) hs
      (separableCone_one_add_two_rankOne _ hnorm)
    have hconj : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * normalizedRay v *
        (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ =
        ((1 / (d + 2) : ℝ) : ℂ) •
          (1 + (2 : ℂ) • vecMulVec ((U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *ᵥ v)
            (star ((U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *ᵥ v))) := by
      have hu : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *
          (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ = 1 := by
        simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
      simp only [normalizedRay, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_one, hu, conjugate_outer]
      rfl
    change (partialTranspose ((U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *
      normalizedRay v * (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ)).PosSemidef
    rw [hconj]
    exact QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef hsep
  · simp only [normalizedRay, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
      Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, hi, htr, smul_eq_mul]
    have hc : (↑(1 / (d + 2) : ℝ) * ↑(1 / (d + 2) : ℝ) *
        ((d : ℂ) + 8 * 1)) =
        ((((d + 8) / (d + 2)^2 : ℝ)) : ℂ) := by
      have hdc : (d : ℂ) + 2 ≠ 0 := by exact_mod_cast hd.ne'
      push_cast
      field_simp [hdc]
      <;> ring
    change (↑(1 / (d + 2) : ℝ) * ↑(1 / (d + 2) : ℝ) *
      ((d : ℂ) + 8 * 1)).re = (d + 8) / (d + 2)^2
    rw [hc, Complex.ofReal_re]

/-- A coordinate vector gives the diagonal representative of the normalized ray. -/
theorem normalized_basis_diagonal {m n : ℕ} (a : Fin m × Fin n) :
    normalizedRay (Pi.single a 1) = diagonal (fun i =>
      if i = a then (3 / (((m*n : ℕ) : ℂ) + 2) : ℂ)
      else (1 / (((m*n : ℕ) : ℂ) + 2) : ℂ)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = a <;>
      simp [normalizedRay, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hi]
    <;> push_cast <;> ring
  · by_cases hi : i = a
    · have hj : j ≠ a := by intro h; exact hij (hi.trans h.symm)
      simp [normalizedRay, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
        Pi.single_apply, hij, hi, hj, eq_comm]
      all_goals simp_all
    · simp [normalizedRay, Matrix.diagonal_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, hij, hi]

def claim : Prop :=
    (∀ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) → APPT rho →
        (rho * rho).trace.re ≤ (7 / 121 : ℝ)) ∧
    (sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = p} = (7 / 121 : ℝ)) ∧
    ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 5 =>
        if ij = (0, 0) then (3 / 22 : ℂ) else (1 / 22 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (7 / 121 : ℝ)

private theorem density_bound (rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ)
    (hrho : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    (rho * rho).trace.re ≤ (7 / 121 : ℝ) := by
  obtain ⟨l, ho, hn, ht, h1, h2, hp⟩ :=
    spectral_reduction (by decide : 3 ≤ 4) (by decide : 3 ≤ 5)
      rho hrho htrace happt
  have hb : cornerBoundaryValues 20 (by decide) l =
      SpectralBoundaryTransfer.boundaryValues 11 l := by
    funext q
    apply congrArg l
    apply Fin.ext
    simp only [cornerBoundaryValues, SpectralBoundaryTransfer.boundaryValues,
      SpectralBoundaryTransfer.boundaryIndex]
  rw [hb] at h1 h2
  rw [hp]
  exact DimensionTwentySpectralPurityBound.spectral_purity_bound l ho hn ht h1 h2

theorem result : claim := by
  let v : Fin 4 × Fin 5 → ℂ := Pi.single (0, 0) 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    classical
    simp [v, dotProduct, Pi.single_apply]
  obtain ⟨hd, ht, ha, hp⟩ := normalized_ray v hv
  have heq : normalizedRay v = diagonal (fun ij : Fin 4 × Fin 5 =>
      if ij = (0, 0) then (3 / 22 : ℂ) else (1 / 22 : ℂ)) := by
    convert normalized_basis_diagonal ((0, 0) : Fin 4 × Fin 5) using 1 <;> norm_num [v]
  norm_num at hp
  have hattain : ∃ rho : Matrix (Fin 4 × Fin 5) (Fin 4 × Fin 5) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
        (rho * rho).trace.re = (7 / 121 : ℝ) :=
    ⟨normalizedRay v, ⟨hd, ht⟩, ha, hp⟩
  refine ⟨fun rho hd ha => density_bound rho hd.1 hd.2 ha, ?_,
    normalizedRay v, heq, ⟨hd, ht⟩, ha, hp⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · exact ⟨_, hattain⟩
  · rintro p ⟨rho, hd, ha, hp⟩
    rw [← hp]
    exact density_bound rho hd.1 hd.2 ha
  · intro w hw
    exact ⟨_, hattain, hw⟩

#print axioms spectral_reduction
#print axioms normalized_ray
#print axioms normalized_basis_diagonal
#print axioms result

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
