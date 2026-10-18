/- GID: D5/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CoherenceBreakingAmendment
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: One permutation-phase unitary amends every incoherent channel of index at least two. -/

import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Matrix.MonomialDiagonalPreserving
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments

/-! # Amendment of incoherent channels with finite coherence-breaking index -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (IsKrausChannel krausApply)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
  (all_density_tomographically_complete)
open D5.S3.Quantum.Matrix.MonomialDiagonalPreserving
  (monomial monomial_apply monomial_eq_diagonal_mul)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumMoments
  (phase moment_four)

namespace D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment

/-- Each Kraus column has support in at most one basis direction. -/
def IsIncoherentKraus {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ s j, ∃ k, ∀ i, i ≠ k → K s i j = 0

/-- Every density matrix is mapped to a diagonal matrix. -/
def IsCoherenceBreaking {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ ρ, ρ.PosSemidef → ρ.trace = 1 → ∀ i j, i ≠ j → Φ ρ i j = 0

/-- The same conjugation is inserted between every pair of consecutive channels. -/
def amended {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :=
  krausApply K ∘ (LinearMap.mulLeftRight ℂ (U, Uᴴ) ∘ krausApply K)^[n - 1]

/-- The finite-index amendment conjecture, with a single unitary in every slot. -/
def claim : Prop :=
  ∀ (d r : ℕ) (K : Fin r → Matrix (Fin d) (Fin d) ℂ),
    IsKrausChannel K → IsIncoherentKraus K →
    ∀ n : ℕ, 2 ≤ n → IsCoherenceBreaking (krausApply K)^[n] →
      (∀ k, 1 ≤ k → k < n → ¬ IsCoherenceBreaking (krausApply K)^[k]) →
      ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ, ¬ IsCoherenceBreaking (amended K U n)

private def offDiag {d : ℕ} :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) where
  toFun X i j := if i = j then 0 else X i j
  map_add' X Y := by
    ext i j
    change (if i = j then 0 else X i j + Y i j) =
      (if i = j then 0 else X i j) + (if i = j then 0 else Y i j)
    by_cases h : i = j <;> simp [h]
  map_smul' c X := by
    ext i j
    change (if i = j then 0 else c * X i j) =
      c * (if i = j then 0 else X i j)
    by_cases h : i = j <;> simp [h]

private def residual {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) := offDiag ∘ₗ (MatrixMap.of_kraus K K)

private theorem residual_diagonal {d r : ℕ}
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : IsIncoherentKraus K)
    (a : Fin d) : residual K (single a a 1) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst j
    change (if i = i then 0 else _) = 0
    exact ite_eq_left rfl
  · change (if i = j then 0 else krausApply K (single a a 1) i j) = 0
    rw [ite_eq_right hij, krausApply.eq_1, MatrixMap.of_kraus]
    simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro s _
    have hs : (K s * single a a 1 * (K s)ᴴ : Matrix (Fin d) (Fin d) ℂ) i j =
        K s i a * star (K s j a) := by
      simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]
    rw [hs]
    obtain ⟨b, hb⟩ := hK s a
    by_cases hib : i = b
    · rw [hb j (by intro h; exact hij (hib.trans h.symm)), star_zero, mul_zero]
    · rw [hb i hib, zero_mul]

private theorem residual_projection {d r : ℕ}
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : IsIncoherentKraus K)
    (X : Matrix (Fin d) (Fin d) ℂ) : residual K (offDiag X) = residual K X := by
  have hd : residual K (diagonal (fun i => X i i)) = 0 := by
    rw [← Matrix.sum_single_eq_diagonal]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    simpa only [← map_smul, smul_single, smul_eq_mul, mul_one, smul_zero] using
      congrArg (fun Y => (X i i) • Y) (residual_diagonal K hK i)
  have hx : offDiag X + diagonal (fun i => X i i) = X := by
    ext i j
    change (if i = j then 0 else X i j) + (if i = j then X i i else 0) = X i j
    split_ifs with h
    · subst j; simp
    · simp
  have he := congrArg (residual K) hx
  simpa only [map_add, hd, add_zero] using he

private theorem density_ext {d : ℕ}
    (F : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (hF : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 → F ρ = 0) : F = 0 := by
  have hspan :=
    all_density_tomographically_complete d
  have hker : D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d ≤
      LinearMap.ker (F.restrictScalars ℝ) := by
    rw [← hspan.2]
    apply Submodule.span_le.mpr
    intro ρ hρ
    exact hF ρ hρ.1 hρ.2
  apply LinearMap.ext
  intro X
  have hre : F (realPart X : Matrix (Fin d) (Fin d) ℂ) = 0 :=
    hker (realPart X).property
  have him : F (imaginaryPart X : Matrix (Fin d) (Fin d) ℂ) = 0 :=
    hker (imaginaryPart X).property
  calc
    F X = F ((realPart X : Matrix (Fin d) (Fin d) ℂ) +
        Complex.I • (imaginaryPart X : Matrix (Fin d) (Fin d) ℂ)) :=
      congrArg F (realPart_add_I_smul_imaginaryPart X).symm
    _ = 0 := by rw [map_add, map_smul, hre, him, smul_zero, add_zero]

private theorem monomial_action {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) X i j =
      ω (σ.symm i) * star (ω (σ.symm j)) * X (σ.symm i) (σ.symm j) := by
  rw [LinearMap.mulLeftRight_apply]
  simp only [Matrix.mul_apply, monomial_apply, Matrix.conjTranspose_apply,
    Function.comp_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_zero, apply_ite, star_zero]
  ring

private theorem monomial_unitary {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ)
    (hω : ∀ c, ω c * star (ω c) = 1) :
    monomial σ.symm (ω ∘ σ.symm) ∈ unitaryGroup (Fin d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change monomial σ.symm (ω ∘ σ.symm) * (monomial σ.symm (ω ∘ σ.symm))ᴴ = 1
  have he : LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)
        (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    ext i j
    rw [monomial_action]
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.one_apply_eq, mul_one] using hω (σ.symm i)
    · simp [hij, σ.symm.injective.ne hij]
  change monomial σ.symm (ω ∘ σ.symm) * 1 * (monomial σ.symm (ω ∘ σ.symm))ᴴ = 1 at he
  simpa only [Matrix.mul_one, monomial_eq_diagonal_mul] using he

private theorem monomial_projection {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    offDiag (LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) X) =
      LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) (offDiag X) := by
  ext i j
  change (if i = j then 0 else LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) X i j) = _
  rw [monomial_action, monomial_action]
  change (if i = j then 0 else _) =
    _ * _ * (if σ.symm i = σ.symm j then 0 else _)
  by_cases hij : i = j
  · subst j; simp
  · simp [hij, σ.symm.injective.ne hij]

private theorem monomial_single {d : ℕ} (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ)
    (a b : Fin d) : LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) (single a b 1) =
      (ω a * star (ω b)) • single (σ a) (σ b) 1 := by
  ext i j
  rw [monomial_action]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hi : i = σ a
  · subst i
    by_cases hj : j = σ b
    · subst j; simp
    · simp [Ne.symm hj, Equiv.eq_symm_apply]
  · simp [Ne.symm hi, Equiv.eq_symm_apply]

private theorem composite_formula {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hK : IsIncoherentKraus K) (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ)
    (m : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) :
    offDiag (krausApply K ((LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) ∘ krausApply K)^[m] X)) =
      ((residual K * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)) ^ m * residual K) X := by
  have hbridge (Y : Matrix (Fin d) (Fin d) ℂ) :
      residual K (LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) (krausApply K Y)) =
        residual K (LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) (residual K Y)) := by
    rw [← residual_projection K hK (LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) (krausApply K Y)),
      monomial_projection]
    rfl
  change residual K ((LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) ∘ krausApply K)^[m] X) =
    ((residual K * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)) ^ m) (residual K X)
  rw [Module.End.pow_apply]
  exact (show Function.Semiconj (residual K)
    (LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) ∘ krausApply K)
    (residual K * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ) :
      Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) from hbridge).iterate_right m X

private theorem breaking_trace_zero {d r : ℕ}
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : IsIncoherentKraus K)
    (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hcb : IsCoherenceBreaking (amended K (monomial σ.symm (ω ∘ σ.symm)) n)) :
    LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ)
      (residual K * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)) = 0 := by
  have hz : (residual K * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)) ^ (n - 1) *
        residual K = 0 := by
    apply density_ext
    intro ρ hρ ht
    rw [← composite_formula K hK σ ω]
    ext i j
    change (if i = j then 0 else amended K (monomial σ.symm (ω ∘ σ.symm)) n ρ i j) = 0
    split_ifs with hij
    · rfl
    · exact hcb ρ hρ ht i j hij
  apply IsNilpotent.eq_zero
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  refine ⟨n, ?_⟩
  conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  rw [← mul_assoc, hz, zero_mul]

private theorem character_sum {d : ℕ} (p q k l : Fin d) (hkl : k ≠ l) :
    (∑ w : Fin d → Fin 4,
      phase (w p) * star (phase (w q)) * star (phase (w k)) * phase (w l)) =
      if p = k ∧ q = l then (4 : ℂ) ^ d else 0 := by
  calc
    _ = ∑ w : Fin d → Fin 4,
        (starRingEnd ℂ) (phase (w q)) * phase (w p) *
          (starRingEnd ℂ) (phase (w k)) * phase (w l) := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [moment_four]; simp [hkl, and_comm, mul_ite]

private theorem phase_trace {d : ℕ}
    (F : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (σ : Equiv.Perm (Fin d)) (ω : Fin d → ℂ) :
    LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ) (F * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)) =
      ∑ p, ∑ q, (ω p * star (ω q)) * F (single (σ p) (σ q) 1) p q := by
  calc
    _ = ∑ p, ∑ q, (F * LinearMap.mulLeftRight ℂ
      (monomial σ.symm (ω ∘ σ.symm), (monomial σ.symm (ω ∘ σ.symm))ᴴ)) (single p q 1) p q := by
      rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d))]
      simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type,
        Matrix.stdBasis, ← Matrix.single_eq_of_single_single]
    _ = _ := by
      simp only [Module.End.mul_apply, monomial_single, map_smul, Matrix.smul_apply, smul_eq_mul]

private theorem nonzero_trace {d : ℕ}
    (F : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))
    (σ : Equiv.Perm (Fin d)) (k l : Fin d) (hkl : k ≠ l)
    (hentry : F (single (σ k) (σ l) 1) k l ≠ 0) :
    ∃ w : Fin d → Fin 4,
      LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ)
        (F * LinearMap.mulLeftRight ℂ
          (monomial σ.symm ((fun c => phase (w c)) ∘ σ.symm),
            (monomial σ.symm ((fun c => phase (w c)) ∘ σ.symm))ᴴ)) ≠ 0 := by
  have havg :
      (∑ w : Fin d → Fin 4, star (phase (w k)) * phase (w l) *
        LinearMap.trace ℂ (Matrix (Fin d) (Fin d) ℂ)
          (F * LinearMap.mulLeftRight ℂ
          (monomial σ.symm ((fun c => phase (w c)) ∘ σ.symm),
            (monomial σ.symm ((fun c => phase (w c)) ∘ σ.symm))ᴴ))) =
        (4 : ℂ) ^ d * F (single (σ k) (σ l) 1) k l := by
    simp_rw [phase_trace, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ p, ∑ q, (∑ w : Fin d → Fin 4,
          phase (w p) * star (phase (w q)) * star (phase (w k)) * phase (w l)) *
            F (single (σ p) (σ q) 1) p q := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by
        simp_rw [character_sum _ _ _ _ hkl]
        simp [ite_and]
  by_contra h
  push Not at h
  simp_rw [h, mul_zero] at havg
  have hn : (4 : ℂ) ^ d * F (single (σ k) (σ l) 1) k l ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hentry
  exact hn (by simpa using havg.symm)


/-- Every incoherent channel with finite coherence-breaking index at least two is amendable. -/
theorem result : claim := by
  intro d r K _hchannel hK n hn _hpower hminimal
  have hnot : ¬ IsCoherenceBreaking (krausApply K) := by
    exact hminimal 1 (by omega) (by omega)
  have hnonzero : residual K ≠ 0 := by
    intro hz
    apply hnot
    intro ρ _ _ i j hij
    have he := congrArg (fun F : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) => F ρ i j) hz
    change (if i = j then 0 else krausApply K ρ i j) = 0 at he
    rw [ite_eq_right hij] at he
    exact he
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin d, residual K (single a b 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hnonzero
    apply (Matrix.stdBasis ℂ (Fin d) (Fin d)).ext
    rintro ⟨a, b⟩
    simpa only [Matrix.stdBasis_eq_single, LinearMap.zero_apply] using h a b
  have habne : a ≠ b := by
    rintro rfl
    exact hab (residual_diagonal K hK a)
  obtain ⟨k, l, hentry⟩ : ∃ k l : Fin d, residual K (single a b 1) k l ≠ 0 := by
    by_contra h
    push Not at h
    apply hab
    ext i j
    exact h i j
  have hkl : k ≠ l := by
    rintro rfl
    apply hentry
    change (if k = k then 0 else _) = 0
    exact ite_eq_left rfl
  obtain ⟨σ, hσk, hσl⟩ : ∃ σ : Equiv.Perm (Fin d), σ k = a ∧ σ l = b :=
    (MulAction.is_two_pretransitive_iff.mp
      (Equiv.Perm.isMultiplyPretransitive (Fin d) 2)) hkl habne
  obtain ⟨w, hw⟩ := nonzero_trace (residual K) σ k l hkl (by simpa [hσk, hσl] using hentry)
  refine ⟨monomial σ.symm ((fun c => phase (w c)) ∘ σ.symm),
    monomial_unitary σ _ (fun c => (by
      simp only [phase, Complex.star_def, map_pow, ← mul_pow, Complex.conj_I,
        mul_neg, Complex.I_mul_I, neg_neg, one_pow])), ?_⟩
  intro hcb
  exact hw (breaking_trace_zero K hK σ _ n (by omega) hcb)

end D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
