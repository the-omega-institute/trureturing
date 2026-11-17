/- GID: D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeInertiaBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CompressionKernel/NativeThreeInertiaBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian compression-kernel inertia above the native threshold. -/

import D5.S3.Quantum.Algebra.CommonCoefficientPlane

/-! Hermitian coefficient-kernel inertia for an injective rectangular triple. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Algebra.NativeThreeInertiaBridge

open D5.S3.Quantum.Algebra.CommonCoefficientPlane
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

private theorem dimension_le_of_positive_except {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (d : Fin 3 → ℝ) (j : Fin 3) (hd : ∀ r, r ≠ j → 0 < d r)
    (hPhi : compression X (Matrix.diagonal (fun r => (d r : ℂ))) = 0) : b ≤ a := by
  classical
  have hi : Function.Injective (X j).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change X j *ᵥ x = 0 at hx
    have he := compression_pairing X (Matrix.diagonal (fun r => (d r : ℂ))) x x
    rw [hPhi] at he
    simp only [Matrix.zero_mulVec, dotProduct_zero] at he
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq] at he
    let w (r : Fin 3) : ℂ :=
      if r = j then 0 else (d r : ℂ) * (star (X r *ᵥ x) ⬝ᵥ (X r *ᵥ x))
    have hw : ∀ r, 0 ≤ w r := by
      intro r
      by_cases hr : r = j
      · simp [w, hr]
      · simp only [w, ite_eq_right hr]
        exact mul_nonneg (by exact_mod_cast (hd r hr).le)
          (dotProduct_star_self_nonneg (X r *ᵥ x))
    have hs : ∑ r, w r = 0 := by
      trans ∑ r, (d r : ℂ) * (star (X r *ᵥ x) ⬝ᵥ (X r *ᵥ x))
      · apply Finset.sum_congr rfl
        intro r hr
        by_cases hrj : r = j
        · subst r; simp [w, hx]
        · simp [w, hrj]
      · exact he.symm
    have hz (r : Fin 3) : w r = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hw r)).mp hs r (Finset.mem_univ r)
    apply stack_injective_on_common_kernel X hinj x
    intro r
    by_cases hr : r = j
    · simpa [hr] using hx
    · have heq : (d r : ℂ) * (star (X r *ᵥ x) ⬝ᵥ (X r *ᵥ x)) = 0 := by
        simpa only [w, ite_eq_right hr] using hz r
      exact dotProduct_star_self_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left
        (by exact_mod_cast (hd r hr).ne'))
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim

private theorem compression_neg_eq_zero {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) :
    compression X (-T) = 0 := by
  rw [compression_eq_sum]
  change (∑ r, ∑ s, -(T r s) • ((X r)ᴴ * X s)) = 0
  simp only [neg_smul, Finset.sum_neg_distrib]
  rw [← compression_eq_sum, hPhi, neg_zero]

/-- A nonzero Hermitian form annihilated by the compression has one positive,
one negative and one zero eigenvalue at the strict native threshold. -/
theorem spectral_signs {a b : ℕ} (hab : a < b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian)
    (hPhi : compression X T = 0) (hne : T ≠ 0) :
    ∃ e : Fin 3 ≃ Fin 3,
      0 < hT.eigenvalues (e 0) ∧ hT.eigenvalues (e 1) < 0 ∧
      hT.eigenvalues (e 2) = 0 := by
  classical
  have hnotP : ¬ T.PosSemidef := fun h => hne (semidefinite_eq_zero X hX T h hPhi)
  have hnotN : ¬ (-T).PosSemidef := by
    intro h
    have he := semidefinite_eq_zero X hX (-T) h (compression_neg_eq_zero X T hPhi)
    exact hne (neg_eq_zero.mp he)
  obtain ⟨j, hj⟩ : ∃ j, hT.eigenvalues j < 0 := by
    by_contra h
    apply hnotP
    apply hT.posSemidef_iff_eigenvalues_nonneg.mpr
    intro j
    exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
  obtain ⟨i, hi⟩ : ∃ i, 0 < hT.eigenvalues i := by
    by_contra h
    have hnonpos : ∀ i, hT.eigenvalues i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hd : (Matrix.diagonal (fun i => (-(hT.eigenvalues i) : ℂ))).PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast neg_nonneg.mpr (hnonpos i)
    have hp := hd.mul_mul_conjTranspose_same
      (hT.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ)
    apply hnotN
    have hs := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [hs]
    convert hp using 1
    rw [Matrix.star_eq_conjTranspose]
    simp only [Function.comp_def]
    rw [show (Matrix.diagonal fun i => -(hT.eigenvalues i : ℂ)) =
        -(Matrix.diagonal fun i => (hT.eigenvalues i : ℂ)) by
      ext r s; by_cases hrs : r = s <;> simp [hrs]]
    rw [Matrix.mul_neg, Matrix.neg_mul]
    rfl
  have hij : i ≠ j := by intro he; subst j; linarith
  have hc : ({i, j} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by
    simp [hij]
  obtain ⟨k, _, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hki : k ≠ i := fun he => hkn (by simp [he])
  have hkj : k ≠ j := fun he => hkn (by simp [he])
  let f : Fin 3 → Fin 3 := ![i, j, k]
  have hf : Function.Injective f := by
    intro r s he
    fin_cases r <;> fin_cases s <;> simp_all [f]
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  let U : Matrix (Fin 3) (Fin 3) ℂ := hT.eigenvectorUnitary
  let Y := mix Uᴴ X
  have hU : IsUnit Uᴴ := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      (Unitary.isUnit_coe (U := star hT.eigenvectorUnitary))
  have hYinj : Function.Injective (stack Y).mulVecLin :=
    injective_stack_mix Uᴴ hU X hinj
  have hD : compression Y (Matrix.diagonal (fun r => (hT.eigenvalues r : ℂ))) = 0 := by
    rw [show Y = mix Uᴴ X from rfl, compression_mix, Matrix.conjTranspose_conjTranspose]
    have hs : Uᴴ * T * U = Matrix.diagonal (fun r => (hT.eigenvalues r : ℂ)) := by
      simpa [U, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
        Matrix.star_eq_conjTranspose] using hT.conjStarAlgAut_star_eigenvectorUnitary
    have hUU : U * Uᴴ = 1 := by
      simpa only [U, Matrix.star_eq_conjTranspose] using hT.eigenvectorUnitary.2.2
    have hs' : U * Matrix.diagonal (fun r => (hT.eigenvalues r : ℂ)) * Uᴴ = T := by
      rw [← hs]
      simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
      rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
    rw [hs', hPhi]
  have hknz : hT.eigenvalues k = 0 := by
    by_contra hknz
    by_cases hkpos : 0 < hT.eigenvalues k
    · have hpos : ∀ r, r ≠ j → 0 < hT.eigenvalues r := by
        intro r hr
        obtain ⟨s, rfl⟩ := e.surjective r
        fin_cases s
        · exact hi
        · exact (hr rfl).elim
        · exact hkpos
      have hdim := dimension_le_of_positive_except Y hYinj hT.eigenvalues j hpos hD
      omega
    · have hkneg : hT.eigenvalues k < 0 := lt_of_le_of_ne (le_of_not_gt hkpos) hknz
      have hpos : ∀ r, r ≠ i → 0 < -hT.eigenvalues r := by
        intro r hr
        obtain ⟨s, rfl⟩ := e.surjective r
        fin_cases s
        · exact (hr rfl).elim
        · exact neg_pos.mpr hj
        · exact neg_pos.mpr hkneg
      have hDn : compression Y
          (Matrix.diagonal (fun r => ((-hT.eigenvalues r : ℝ) : ℂ))) = 0 := by
        have hdiag : (Matrix.diagonal (fun r => ((-hT.eigenvalues r : ℝ) : ℂ))) =
            -(Matrix.diagonal (fun r => (hT.eigenvalues r : ℂ))) := by
          ext r s
          by_cases hrs : r = s <;> simp [Matrix.diagonal_apply, hrs]
        rw [hdiag]
        exact compression_neg_eq_zero Y _ hD
      have hdim := dimension_le_of_positive_except Y hYinj
        (fun r => -hT.eigenvalues r) i hpos hDn
      omega
  exact ⟨e, hi, hj, hknz⟩

end D5.S3.Quantum.Algebra.NativeThreeInertiaBridge
