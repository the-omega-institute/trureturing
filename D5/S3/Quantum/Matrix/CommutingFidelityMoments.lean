/- GID: D5/S3/Quantum/Matrix/CommutingFidelityMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CommutingFidelityMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Commuting positive matrices reduce actual resolvent sandwiches and squared normalized fidelity to their common spectrum. -/

import D5.S3.Quantum.Matrix.FixedSumResolventKernel
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import D5.S3.Quantum.CommutingMidpoint.Fidelity
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Matrix.CommutingFidelityMoments

open _root_.Matrix Set MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Matrix.FixedSumResolventKernel
open D5.S3.Quantum.CommutingMidpoint (rootFidelity)

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma simultaneous_spectrum (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : Commute A B) :
    ∃ (U : unitary (Matrix n n ℂ)) (a b : n → ℝ),
      (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧
      (Unitary.conjStarAlgAut ℂ _ (star U)) A = diagonal (fun i => (a i : ℂ)) ∧
      (Unitary.conjStarAlgAut ℂ _ (star U)) B = diagonal (fun i => (b i : ℂ)) := by
  let X := A + Complex.I • B
  have hAs : star A = A := hA.isHermitian.eq
  have hBs : star B = B := hB.isHermitian.eq
  letI : IsStarNormal X := ⟨by
    change star X * X = X * star X
    simp only [X, star_add, star_smul, hAs, hBs, Complex.star_def, Complex.conj_I,
      add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hAB.eq]
    module⟩
  obtain ⟨V, hV, d, hd⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal X
  let U : unitary (Matrix n n ℂ) := ⟨V, hV⟩
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star U)
  have hφAs : star (φ A) = φ A := by rw [← map_star, hAs]
  have hφBs : star (φ B) = φ B := by rw [← map_star, hBs]
  have he : φ A + Complex.I • φ B = diagonal d := by
    rw [← map_smul, ← map_add]
    exact hd
  have hes : φ A - Complex.I • φ B = diagonal (fun i => star (d i)) := by
    simpa only [star_add, star_smul, hφAs, hφBs, Complex.star_def, Complex.conj_I,
      neg_smul, ← sub_eq_add_neg, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Pi.star_apply] using congrArg star he
  have heA : φ A = diagonal (fun i => ((d i).re : ℂ)) := by
    ext i k
    have h := congrFun (congrFun he i) k
    have hs := congrFun (congrFun hes i) k
    by_cases hik : i = k
    · subst k
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_eq] at h hs ⊢
      apply Complex.ext
      · have h1 := congrArg Complex.re h
        have h2 := congrArg Complex.re hs
        simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, zero_mul, one_mul, Complex.star_def, Complex.conj_re,
          Complex.ofReal_re] at h1 h2 ⊢
        linarith
      · have h1 := congrArg Complex.im h
        have h2 := congrArg Complex.im hs
        simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, zero_mul, one_mul, Complex.star_def, Complex.conj_im,
          Complex.ofReal_im] at h1 h2 ⊢
        linarith
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_ne hik] at h hs ⊢
      linear_combination (1 / 2 : ℂ) * h + (1 / 2 : ℂ) * hs
  have heB : φ B = diagonal (fun i => ((d i).im : ℂ)) := by
    ext i k
    have h := congrFun (congrFun he i) k
    have hs := congrFun (congrFun hes i) k
    by_cases hik : i = k
    · subst k
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_eq] at h hs ⊢
      apply Complex.ext
      · have h1 := congrArg Complex.im h
        have h2 := congrArg Complex.im hs
        simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, zero_mul, one_mul, Complex.star_def, Complex.conj_im,
          Complex.ofReal_re] at h1 h2 ⊢
        linarith
      · have h1 := congrArg Complex.re h
        have h2 := congrArg Complex.re hs
        simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, zero_mul, one_mul, Complex.star_def, Complex.conj_re,
          Complex.ofReal_im] at h1 h2 ⊢
        linarith
    · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_ne hik] at h hs ⊢
      have hz : φ A i k = 0 := by rw [heA, Matrix.diagonal_apply_ne hik]
      rw [hz, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero
  refine ⟨U, fun i => (d i).re, fun i => (d i).im, ?_, ?_, heA, heB⟩
  · have hp : (φ A).PosSemidef := nonneg_iff_posSemidef.mp (map_nonneg φ hA.nonneg)
    rw [heA] at hp
    intro i
    have hh := hp.diag_nonneg (i := i)
    simpa using (Complex.nonneg_iff.mp hh).1
  · have hp : (φ B).PosSemidef := nonneg_iff_posSemidef.mp (map_nonneg φ hB.nonneg)
    rw [heB] at hp
    intro i
    have hh := hp.diag_nonneg (i := i)
    simpa using (Complex.nonneg_iff.mp hh).1

private lemma trace_conj (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    trace ((Unitary.conjStarAlgAut ℂ _ U) X) = trace X := by
  change trace ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) = _
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private lemma sqrt_diagonal (a : n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    CFC.sqrt (diagonal (fun i => (a i : ℂ))) =
      diagonal (fun i => (Real.sqrt (a i) : ℂ)) := by
  have hp : (diagonal (fun i => (a i : ℂ))).PosSemidef :=
    PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (ha i))
  rw [CFC.sqrt_eq_real_sqrt _ hp.nonneg, cfcₙ_eq_cfc]
  exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    Real.sqrt a

private lemma map_sqrt (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ)
    (hX : X.PosSemidef) :
    (Unitary.conjStarAlgAut ℂ _ U) (CFC.sqrt X) =
      CFC.sqrt ((Unitary.conjStarAlgAut ℂ _ U) X) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  simpa only [CFC.sqrt] using
    (NonUnitalStarAlgHomClass.map_cfcₙ (R := ℝ≥0) φ NNReal.sqrt X
      (ha := hX.nonneg) (hφa := map_nonneg φ hX.nonneg))

private lemma root_fidelity_spectral (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    (heB : (Unitary.conjStarAlgAut ℂ _ U) B = diagonal (fun i => (b i : ℂ))) :
    rootFidelity A B = ∑ i, Real.sqrt (a i * b i) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hroot := (CFC.sqrt_nonneg A).posSemidef
  have hsand : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    simpa only [hroot.isHermitian.eq] using hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  have he : φ (CFC.sqrt A * B * CFC.sqrt A) = diagonal (fun i => (a i * b i : ℝ)) := by
    simp only [map_mul, map_sqrt U A hA, heA, heB, sqrt_diagonal a ha,
      diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    calc
      Real.sqrt (a i) * b i * Real.sqrt (a i) =
          (Real.sqrt (a i) * Real.sqrt (a i)) * b i := by ring
      _ = a i * b i := by rw [Real.mul_self_sqrt (ha i)]
  unfold rootFidelity
  rw [← trace_conj U, map_sqrt U _ hsand, he,
    sqrt_diagonal (fun i => a i * b i) (fun i => mul_nonneg (ha i) (hb i)),
    trace_diagonal, Complex.re_sum]
  simp

/-- Actual matrix shifted response, using the matrix nonsingular inverse. -/
def response (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  A * ((s : ℂ) • 1 + A)⁻¹

/-- Positive-square-root sandwich of the two actual shifted responses. -/
def sandwich (A B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  CFC.sqrt (response A s) * response B s * CFC.sqrt (response A s)

/-- Integrated trace moment of the actual resolvent sandwich. -/
def gamma (j : ℕ) (A B : Matrix n n ℂ) : ℝ :=
  (∫ s in Ioi 0, (trace (sandwich A B s ^ j)).re) / j

/-- Squared Uhlmann fidelity after normalizing the two traces separately. -/
def squaredNormalizedFidelity (A B : Matrix n n ℂ) : ℝ :=
  rootFidelity ((trace A).re⁻¹ • A) ((trace B).re⁻¹ • B) ^ 2

private lemma map_inv (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U) X⁻¹ = ((Unitary.conjStarAlgAut ℂ _ U) X)⁻¹ := by
  simp only [Matrix.nonsing_inv_eq_ringInverse, map_ringInverse]

private lemma response_spectral (A : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    {s : ℝ} (hs : 0 < s) :
    (Unitary.conjStarAlgAut ℂ _ U) (response A s) =
      diagonal (fun i => (a i / (s + a i) : ℝ)) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hshift : φ ((s : ℂ) • 1 + A) = diagonal (fun i => (s + a i : ℝ)) := by
    rw [map_add, map_smul, map_one, heA]
    ext i k
    by_cases h : i = k <;> simp [h, Matrix.diagonal_apply, Matrix.one_apply]
  have hinv : (diagonal (fun i => (s + a i : ℝ)) : Matrix n n ℂ)⁻¹ =
      diagonal (fun i => ((s + a i)⁻¹ : ℝ)) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    ext i k
    by_cases h : i = k
    · subst k
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      push_cast
      have hn : (s + a i : ℂ) ≠ 0 := by exact_mod_cast (add_pos_of_pos_of_nonneg hs (ha i)).ne'
      exact inv_mul_cancel₀ hn
    · simp [Matrix.diagonal_apply_ne h, Matrix.one_apply_ne h]
  rw [response, map_mul, map_inv, hshift, hinv, heA, diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  rfl

private lemma response_posSemidef (A : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    {s : ℝ} (hs : 0 < s) : (response A s).PosSemidef := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hp : 0 ≤ φ (response A s) := by
    rw [response_spectral A U a ha heA hs]
    exact (PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr
      (div_nonneg (ha i) (add_pos_of_pos_of_nonneg hs (ha i)).le))).nonneg
  have hh := map_nonneg φ.symm hp
  simpa only [StarAlgEquiv.symm_apply_apply] using nonneg_iff_posSemidef.mp hh

private lemma sandwich_spectral (A B : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    (heB : (Unitary.conjStarAlgAut ℂ _ U) B = diagonal (fun i => (b i : ℂ)))
    {s : ℝ} (hs : 0 < s) :
    (Unitary.conjStarAlgAut ℂ _ U) (sandwich A B s) =
      diagonal (fun i => (a i * b i / ((s + a i) * (s + b i)) : ℝ)) := by
  have hq (i : n) : 0 ≤ a i / (s + a i) :=
    div_nonneg (ha i) (add_pos_of_pos_of_nonneg hs (ha i)).le
  simp only [sandwich, map_mul,
    map_sqrt U _ (response_posSemidef A U a ha heA hs),
    response_spectral A U a ha heA hs, response_spectral B U b hb heB hs,
    sqrt_diagonal _ hq, diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  calc
    Real.sqrt (a i / (s + a i)) * (b i / (s + b i)) * Real.sqrt (a i / (s + a i)) =
        (Real.sqrt (a i / (s + a i)) * Real.sqrt (a i / (s + a i))) * (b i / (s + b i)) := by ring
    _ = (a i / (s + a i)) * (b i / (s + b i)) := by rw [Real.mul_self_sqrt (hq i)]
    _ = _ := div_mul_div_comm _ _ _ _

private lemma moment_spectral (A B : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    (heB : (Unitary.conjStarAlgAut ℂ _ U) B = diagonal (fun i => (b i : ℂ)))
    (j : ℕ) {s : ℝ} (hs : 0 < s) :
    (trace (sandwich A B s ^ j)).re =
      ∑ i, (a i * b i / ((s + a i) * (s + b i))) ^ j := by
  rw [← trace_conj U, map_pow, sandwich_spectral A B U a b ha hb heA heB hs,
    diagonal_pow, trace_diagonal, Complex.re_sum]
  simp

private lemma gamma_spectral (A B : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    (heB : (Unitary.conjStarAlgAut ℂ _ U) B = diagonal (fun i => (b i : ℂ)))
    {j : ℕ} (hj : 1 ≤ j) : gamma j A B = ∑ i, scalarMoment j (a i) (b i) := by
  unfold gamma scalarMoment
  rw [← Finset.sum_div]
  congr 1
  calc
    _ = ∫ s in Ioi 0, ∑ i, (a i * b i / ((s + a i) * (s + b i))) ^ j := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact moment_spectral A B U a b ha hb heA heB j hs
    _ = _ := integral_finsetSum _ (fun i _ => integrable_scalar (ha i) (hb i) hj)

private lemma trace_spectral (A : Matrix n n ℂ)
    (U : unitary (Matrix n n ℂ)) (a : n → ℝ)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ))) :
    (trace A).re = ∑ i, a i := by
  rw [← trace_conj U, heA, trace_diagonal, Complex.re_sum]
  simp

private lemma normalized_fidelity_spectral (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : unitary (Matrix n n ℂ)) (a b : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (heA : (Unitary.conjStarAlgAut ℂ _ U) A = diagonal (fun i => (a i : ℂ)))
    (heB : (Unitary.conjStarAlgAut ℂ _ U) B = diagonal (fun i => (b i : ℂ)))
    (hα : 0 < (trace A).re) (hβ : 0 < (trace B).re) :
    squaredNormalizedFidelity A B =
      (∑ i, Real.sqrt (a i * b i)) ^ 2 / ((trace A).re * (trace B).re) := by
  let α := (trace A).re
  let β := (trace B).re
  let φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  have hAn : φ (α⁻¹ • A) = diagonal (fun i => (a i / α : ℝ)) := by
    rw [φ.toAlgEquiv.toLinearMap.map_smul_of_tower α⁻¹ A, heA, ← diagonal_smul]
    congr 1
    funext i
    simp [div_eq_mul_inv, mul_comm]
  have hBn : φ (β⁻¹ • B) = diagonal (fun i => (b i / β : ℝ)) := by
    rw [φ.toAlgEquiv.toLinearMap.map_smul_of_tower β⁻¹ B, heB, ← diagonal_smul]
    congr 1
    funext i
    simp [div_eq_mul_inv, mul_comm]
  have hroot := root_fidelity_spectral (α⁻¹ • A) (β⁻¹ • B)
    (hA.smul (inv_nonneg.mpr hα.le)) (hB.smul (inv_nonneg.mpr hβ.le)) U
    (fun i => a i / α) (fun i => b i / β)
    (fun i => div_nonneg (ha i) hα.le) (fun i => div_nonneg (hb i) hβ.le) hAn hBn
  have he (i : n) : Real.sqrt (a i / α * (b i / β)) =
      Real.sqrt (a i * b i) / Real.sqrt (α * β) := by
    rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg (ha i) (hb i))]
  simp_rw [he] at hroot
  rw [← Finset.sum_div] at hroot
  unfold squaredNormalizedFidelity
  rw [hroot, div_pow, Real.sq_sqrt (mul_pos hα hβ).le]

/-- The complete commuting PSD fidelity-moment inequality in arbitrary finite dimension.
The two traces are normalized independently; zero eigenvalues are permitted. -/
theorem commuting_fidelity_moment (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAn : A ≠ 0) (hBn : B ≠ 0)
    (hAB : Commute A B) {j : ℕ} (hj : 1 ≤ j) :
    scalarMoment j (trace A).re (trace B).re * squaredNormalizedFidelity A B ^ j ≤
      gamma j A B := by
  obtain ⟨U, a, b, ha, hb, heA, heB⟩ := simultaneous_spectrum A B hA hB hAB
  have hα : 0 < (trace A).re := by
    have hn := (Complex.nonneg_iff.mp hA.trace_nonneg).1
    apply lt_of_le_of_ne hn
    intro hz
    apply hAn
    apply hA.trace_eq_zero_iff.mp
    exact Complex.ext hz.symm (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
  have hβ : 0 < (trace B).re := by
    have hn := (Complex.nonneg_iff.mp hB.trace_nonneg).1
    apply lt_of_le_of_ne hn
    intro hz
    apply hBn
    apply hB.trace_eq_zero_iff.mp
    exact Complex.ext hz.symm (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm
  rw [gamma_spectral A B (star U) a b ha hb heA heB hj,
    normalized_fidelity_spectral A B hA hB (star U) a b ha hb heA heB hα hβ]
  simp only [trace_spectral A (star U) a heA, trace_spectral B (star U) b heB]
  exact scalar_fidelity_moment a b ha hb
    (by rwa [← trace_spectral A (star U) a heA])
    (by rwa [← trace_spectral B (star U) b heB]) hj

end D5.S3.Quantum.Matrix.CommutingFidelityMoments
