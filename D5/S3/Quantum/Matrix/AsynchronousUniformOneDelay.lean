/- GID: D5/S3/Quantum/Matrix/AsynchronousUniformOneDelay
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AsynchronousUniformOneDelay
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact square-root radius for uniform contributing delays and arbitrary history lengths. -/

import D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius

/-! The literal history operator with unit remote delays has a square-root spectral law. -/

noncomputable section
open Matrix
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator

namespace D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay

private theorem newest_row {ℓ : ℕ} {n : Fin ℓ → ℕ}
    (N : Matrix (Vtx n) (Vtx n) ℝ) (δ : Fin ℓ → Fin ℓ → ℕ)
    (hN : ∀ p q, p.1 = q.1 → N p q = 0)
    (hδ : ∀ i j, i ≠ j → δ i j = 1) (K : ℕ) (hK : 1 ≤ K)
    (H : Fin (K + 1) × Vtx n → ℂ) (p : Vtx n) :
    (((asyncMatrix N δ K).map (algebraMap ℝ ℂ)).mulVec H) (0,p) =
      ∑ q, (N p q : ℂ) * H (⟨1, by omega⟩,q) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases he : p.1 = q.1
  · simp [asyncMatrix, Matrix.map_apply, hN p q he]
  · have hd : δ q.1 p.1 = 1 := hδ _ _ (Ne.symm he)
    let slot : Fin (K + 1) := ⟨1, by omega⟩
    rw [Fintype.sum_eq_single slot]
    · simp [asyncMatrix, Matrix.map_apply, hd, slot]
    · intro s hs
      have hv : s.val ≠ 1 := fun h => hs (Fin.ext h)
      simp [asyncMatrix, Matrix.map_apply, hd, hv]

private theorem nonzero_spectrum {ℓ : ℕ} {n : Fin ℓ → ℕ}
    (N : Matrix (Vtx n) (Vtx n) ℝ) (δ : Fin ℓ → Fin ℓ → ℕ)
    (hN : ∀ p q, p.1 = q.1 → N p q = 0)
    (hδ : ∀ i j, i ≠ j → δ i j = 1) (K : ℕ) (hK : 1 ≤ K)
    (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ ((asyncMatrix N δ K).map (algebraMap ℝ ℂ)) ↔
      z ^ 2 ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)) := by
  classical
  let A := N.map (algebraMap ℝ ℂ)
  let B := (asyncMatrix N δ K).map (algebraMap ℝ ℂ)
  constructor
  · intro hs
    have hs' : z ∈ spectrum ℂ B.toLin' := by rwa [Matrix.spectrum_toLin']
    obtain ⟨H, hH⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hs').exists_hasEigenvector
    have he : B.mulVec H = z • H := by
      simpa only [Matrix.toLin'_apply] using hH.apply_eq_smul
    let u : Vtx n → ℂ := fun p => H (0,p)
    have hist := history_formula N δ K H z hz he
    have hu : u ≠ 0 := by
      intro hu0
      apply hH.2
      funext s
      rw [hist s.1.val s.1.isLt]
      change z⁻¹ ^ s.1.val * u s.2 = 0
      simp [hu0]
    apply D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
      A (z ^ 2) u hu
    funext p
    have hr := congrFun he (0,p)
    rw [newest_row N δ hN hδ K hK] at hr
    simp_rw [hist 1 (by omega)] at hr
    have hh : z⁻¹ * (A.mulVec u) p = z * u p := by
      simpa [A, u, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
        mul_left_comm] using hr
    change (A.mulVec u) p = z ^ 2 * u p
    calc
      _ = z * (z⁻¹ * (A.mulVec u) p) := by simp [← mul_assoc, hz]
      _ = z * (z * u p) := by rw [hh]
      _ = _ := by ring
  · intro hs
    have hs' : z ^ 2 ∈ spectrum ℂ A.toLin' := by rwa [Matrix.spectrum_toLin']
    obtain ⟨u, hu⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hs').exists_hasEigenvector
    have he : A.mulVec u = z ^ 2 • u := by
      simpa only [Matrix.toLin'_apply] using hu.apply_eq_smul
    let H : Fin (K + 1) × Vtx n → ℂ := fun s => z⁻¹ ^ s.1.val * u s.2
    have hH : H ≠ 0 := by
      intro hh
      apply hu.2
      funext p
      have hp := congrFun hh (0,p)
      simpa [H] using hp
    apply D5.S3.Combinatorics.NonBacktracking.LaplacianGapMinDegree.eigenpair_mem_spectrum
      B z H hH
    funext s
    rcases s with ⟨r,p⟩
    by_cases hr : r.val = 0
    · have hr0 : r = 0 := Fin.ext hr
      subst r
      rw [newest_row N δ hN hδ K hK]
      have hsum : (∑ q, (N p q : ℂ) * H (⟨1, by omega⟩,q)) =
          z⁻¹ * (A.mulVec u) p := by
        simp [H, A, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      rw [hsum, he]
      change z⁻¹ * (z ^ 2 * u p) = z * (z⁻¹ ^ 0 * u p)
      simp [pow_two, ← mul_assoc, hz]
    · rw [shift_row N δ K H r p hr]
      change z⁻¹ ^ (r.val - 1) * u p = z * (z⁻¹ ^ r.val * u p)
      have hrp : r.val = (r.val - 1) + 1 := by omega
      conv_rhs => rw [hrp, pow_succ]
      field_simp
      <;> ring

private theorem radius_of_nonzero_square_spectrum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hsp : ∀ z : ℂ, z ≠ 0 →
      (z ∈ spectrum ℂ B ↔ z ^ 2 ∈ spectrum ℂ A))
    (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hradius : spectralRadius ℂ A = ENNReal.ofReal lam) :
    spectralRadius ℂ B = ENNReal.ofReal (Real.sqrt lam) ∧
      ENNReal.ofReal (Real.sqrt lam) < 1 := by
  classical
  have hs0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg lam
  have hs2 : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hl0.le
  have norm_le (w : ℂ) (hw : w ∈ spectrum ℂ A) : ‖w‖ ≤ lam := by
    have h : (‖w‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal lam := by
      rw [← hradius, spectralRadius_eq_of_unital]
      exact le_iSup₂
        (f := fun w (_ : w ∈ spectrum ℂ A) => (‖w‖₊ : ℝ≥0∞)) w hw
    rw [← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff hl0.le).mp h
  have hupper : spectralRadius ℂ B ≤ ENNReal.ofReal (Real.sqrt lam) := by
    rw [spectralRadius_eq_of_unital]
    apply iSup₂_le
    intro z hzspec
    by_cases hz : z = 0
    · subst z; simp
    have hzsq : z ^ 2 ∈ spectrum ℂ A := (hsp z hz).mp hzspec
    have hpow : ‖z‖ ^ 2 ≤ lam := by simpa only [norm_pow] using norm_le (z ^ 2) hzsq
    have hzle : ‖z‖ ≤ Real.sqrt lam := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hs0
      rwa [hs2]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hzle
  obtain ⟨w, hw, hwmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A)
  have hwlam : ‖w‖ = lam := by
    have h : (‖w‖₊ : ℝ≥0∞) = ENNReal.ofReal lam := hwmax.trans hradius
    rw [← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg w) hl0.le).mp h
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwlam
    linarith
  obtain ⟨z, hzpow⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < 2)
  have hzne : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hzpow
    exact hwne hzpow.symm
  have hzmem : z ∈ spectrum ℂ B := (hsp z hzne).mpr (by rwa [hzpow])
  have hzsqrt : ‖z‖ = Real.sqrt lam := by
    apply (pow_left_inj₀ (norm_nonneg z) hs0 (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [hs2, ← norm_pow, hzpow, hwlam]
  have hlower : ENNReal.ofReal (Real.sqrt lam) ≤ spectralRadius ℂ B := by
    rw [spectralRadius_eq_of_unital]
    have h := le_iSup₂
      (f := fun z (_ : z ∈ spectrum ℂ B) => (‖z‖₊ : ℝ≥0∞)) z hzmem
    rw [← ENNReal.ofReal_coe_nnreal] at h
    simpa [hzsqrt] using h
  refine ⟨hupper.antisymm hlower, ?_⟩
  rw [ENNReal.ofReal_lt_one]
  nlinarith

/-- Unit remote delays give the exact square-root radius for every admissible history length. -/
theorem whole_uniform_one_delay {ℓ : ℕ} (hℓ : 0 < ℓ) (n : Fin ℓ → ℕ)
    (hn : ∀ i, 0 < n i) (N : Matrix (Vtx n) (Vtx n) ℝ)
    (δ : Fin ℓ → Fin ℓ → ℕ) (hN : ∀ p q, p.1 = q.1 → N p q = 0)
    (hδ : ∀ i j, i ≠ j → 1 ≤ δ i j ∧ δ i j ≤ 1)
    (K : ℕ) (hK : 1 ≤ K) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hradius : radius N = ENNReal.ofReal lam) :
    radius (asyncMatrix N δ K) = ENNReal.ofReal (Real.sqrt lam) ∧
      ENNReal.ofReal (Real.sqrt lam) < 1 := by
  classical
  let i : Fin ℓ := ⟨0, hℓ⟩
  letI : Nonempty (Vtx n) := ⟨⟨i, ⟨0, hn i⟩⟩⟩
  have hδ' : ∀ i j, i ≠ j → δ i j = 1 := by
    intro i j hij
    exact le_antisymm (hδ i j hij).2 (hδ i j hij).1
  exact radius_of_nonzero_square_spectrum (N.map (algebraMap ℝ ℂ))
    ((asyncMatrix N δ K).map (algebraMap ℝ ℂ))
    (nonzero_spectrum N δ hN hδ' K hK) lam hl0 hl1 hradius

end D5.S3.Quantum.Matrix.AsynchronousUniformOneDelay
