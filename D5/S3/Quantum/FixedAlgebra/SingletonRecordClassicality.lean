/- GID: D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality
   generality: G
   mirror-B: D5/B/S3/Quantum/FixedAlgebra/SingletonRecordClassicality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Singleton normalized records leave a diagonal classical observable algebra. -/

import Mathlib

namespace D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexOrder

/- The record Gram matrix and its reduced channel are built directly from the source
   environment-record amplitudes. No fixed-point algebra is used in their definitions. -/
def recordGram {d e : Nat} (record : Fin d → Fin e → ℂ) (i j : Fin d) : ℂ :=
  ∑ a, record i a * star (record j a)

def recordChannel {d e : Nat} (record : Fin d → Fin e → ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => recordGram record i j * rho i j

noncomputable def diagonalRangeEquiv (d : Nat) :
    (Matrix.diagonalAlgHom ℂ : (Fin d → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ).range
      ≃ₐ[ℂ] (Fin d → ℂ) := by
  let f := (Matrix.diagonalAlgHom ℂ :
    (Fin d → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ).rangeRestrict
  apply (AlgEquiv.ofBijective f ?_).symm
  constructor
  · intro a b h
    apply Matrix.diagonal_injective
    simpa [f, Matrix.diagonalAlgHom_apply] using congrArg Subtype.val h
  · intro z
    rcases z.property with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

private theorem gram_self_of_normalized {d e : Nat} (record : Fin d → Fin e → ℂ)
    (hNormalized : ∀ i, ∑ a, ‖record i a‖ ^ 2 = 1) (i : Fin d) :
    recordGram record i i = 1 := by
  rw [recordGram]
  calc
    ∑ a, record i a * star (record i a) =
        ∑ a, (‖record i a‖ ^ 2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro a ha
      change record i a * (starRingEnd ℂ) (record i a) = _
      rw [RCLike.mul_conj]
      norm_cast
    _ = (↑(∑ a, ‖record i a‖ ^ 2) : ℂ) := by norm_cast
    _ = 1 := by rw [hNormalized i]; norm_num

private theorem record_channel_fixed_iff_diagonal {d e : Nat}
    (record : Fin d → Fin e → ℂ)
    (hNormalized : ∀ i, ∑ a, ‖record i a‖ ^ 2 = 1)
    (hDistinct : ∀ i j, i ≠ j → recordGram record i j ≠ 1)
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    recordChannel record rho = rho ↔
      ∃ p : Fin d → ℂ, rho = Matrix.diagonal p := by
  constructor
  · intro hFixed
    let p : Fin d → ℂ := fun i => rho i i
    refine ⟨p, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [p]
    · have hEntry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hFixed
      have hProduct : (recordGram record i j - 1) * rho i j = 0 := by
        calc
          (recordGram record i j - 1) * rho i j =
              recordGram record i j * rho i j - rho i j := by ring
          _ = 0 := sub_eq_zero.mpr hEntry
      have hGram : recordGram record i j - 1 ≠ 0 :=
        sub_ne_zero.mpr (hDistinct i j hij)
      have hZero : rho i j = 0 := (mul_eq_zero.mp hProduct).resolve_left hGram
      simp [hij, hZero]
  · rintro ⟨p, rfl⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [recordChannel, Matrix.diagonal_apply_eq]
      rw [gram_self_of_normalized record hNormalized i]
      simp
    · simp [recordChannel, hij]

private theorem diagonal_probability_representation {d : Nat}
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hPos : rho.PosSemidef) (hTrace : Matrix.trace rho = 1)
    (p : Fin d → ℂ) (hRho : rho = Matrix.diagonal p) :
    ∃ q : Fin d → ℝ,
      rho = Matrix.diagonal (fun i => (q i : ℂ)) ∧
      (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 := by
  let q : Fin d → ℝ := fun i => (p i).re
  have him : ∀ i, (p i).im = 0 := by
    intro i
    have hHerm := hPos.isHermitian
    have hdiag : star (rho i i) = rho i i := by
      have := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i i) hHerm
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [hRho, Matrix.diagonal_apply_eq] at hdiag
    have := congrArg Complex.im hdiag
    have hEq : -(p i).im = (p i).im := by
      simpa only [Complex.star_def, Complex.conj_im] using this
    linarith
  have hdiag_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    have hnon := hPos.diag_nonneg (i := i)
    have hnon' := (Complex.nonneg_iff.mp hnon).1
    simpa [q, hRho, Matrix.diagonal_apply_eq] using hnon'
  have hRhoQ : rho = Matrix.diagonal (fun i => (q i : ℂ)) := by
    rw [hRho]
    apply congrArg Matrix.diagonal
    funext i
    apply Complex.ext
    · rfl
    · simpa [q] using him i
  have hsum : ∑ i, q i = 1 := by
    have hTrace' : ∑ i, p i = 1 := by
      rw [← Matrix.trace_diagonal p, ← hRho]
      exact hTrace
    have hre := congrArg Complex.re hTrace'
    simpa [q] using hre
  exact ⟨q, hRhoQ, hdiag_nonneg, hsum⟩

/-- Singleton normalized record classes leave a commutative diagonal observable algebra,
and every positive trace-one fixed matrix is exactly a probability vector. -/
theorem singleton_record_classicality {d e : Nat}
    (record : Fin d → Fin e → ℂ)
    (hNormalized : ∀ i, ∑ a, ‖record i a‖ ^ 2 = 1)
    (hDistinct : ∀ i j, i ≠ j → recordGram record i j ≠ 1) :
    (∀ i j, recordGram record i j = 1 ↔ i = j) ∧
    (∀ rho : Matrix (Fin d) (Fin d) ℂ,
      recordChannel record rho = rho ↔
        rho ∈ (Matrix.diagonalAlgHom ℂ :
          (Fin d → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ).range) ∧
    (∀ p : Fin d → ℂ,
      recordChannel record (Matrix.diagonal p) = Matrix.diagonal p ∧
      diagonalRangeEquiv d
          ⟨Matrix.diagonal p, ⟨p, by simp [Matrix.diagonalAlgHom_apply]⟩⟩ = p) ∧
    (∀ x y : (Matrix.diagonalAlgHom ℂ :
        (Fin d → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ).range, x * y = y * x) ∧
    (∀ rho : Matrix (Fin d) (Fin d) ℂ,
      rho.PosSemidef → Matrix.trace rho = 1 →
      recordChannel record rho = rho →
      ∃ p : Fin d → ℝ,
        rho = Matrix.diagonal (fun i => (p i : ℂ)) ∧
        (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) := by
  have hSelf : ∀ i, recordGram record i i = 1 :=
    fun i => gram_self_of_normalized record hNormalized i
  have hClass : ∀ i j, recordGram record i j = 1 ↔ i = j := by
    intro i j
    constructor
    · intro h
      by_contra hij
      exact hDistinct i j hij h
    · intro hij
      subst hij
      exact hSelf i
  have hFixed : ∀ rho : Matrix (Fin d) (Fin d) ℂ,
      recordChannel record rho = rho ↔
        rho ∈ (Matrix.diagonalAlgHom ℂ :
          (Fin d → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ).range := by
    intro rho
    rw [record_channel_fixed_iff_diagonal record hNormalized hDistinct rho]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, by simpa [Matrix.diagonalAlgHom_apply] using hp.symm⟩
    · rintro ⟨p, hp⟩
      exact ⟨p, by simpa [Matrix.diagonalAlgHom_apply] using hp.symm⟩
  refine ⟨hClass, hFixed, ?_, ?_, ?_⟩
  · intro p
    constructor
    · ext i j
      by_cases hij : i = j
      · subst hij
        simp only [recordChannel, Matrix.diagonal_apply_eq]
        rw [gram_self_of_normalized record hNormalized i]
        simp
      · simp [recordChannel, hij]
    · let f := (Matrix.diagonalAlgHom ℂ :
        (Fin d → ℂ) →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ).rangeRestrict
      have hf : Function.Bijective f := by
        constructor
        · intro a b h
          apply Matrix.diagonal_injective
          simpa [f, Matrix.diagonalAlgHom_apply] using congrArg Subtype.val h
        · intro z
          rcases z.property with ⟨a, ha⟩
          exact ⟨a, Subtype.ext ha⟩
      change (AlgEquiv.ofBijective f hf).symm
          ⟨Matrix.diagonal p, ⟨p, by simp [Matrix.diagonalAlgHom_apply]⟩⟩ = p
      apply (AlgEquiv.ofBijective f hf).injective
      simp only [AlgEquiv.apply_symm_apply]
      apply Subtype.ext
      change Matrix.diagonal p = (Matrix.diagonalAlgHom ℂ) p
      rw [Matrix.diagonalAlgHom_apply]
  · intro x y
    rcases x.property with ⟨px, hpx⟩
    rcases y.property with ⟨py, hpy⟩
    have hx : (x : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal px := by
      simpa [Matrix.diagonalAlgHom_apply] using hpx.symm
    have hy : (y : Matrix (Fin d) (Fin d) ℂ) = Matrix.diagonal py := by
      simpa [Matrix.diagonalAlgHom_apply] using hpy.symm
    apply Subtype.ext
    change (x : Matrix (Fin d) (Fin d) ℂ) * (y : Matrix (Fin d) (Fin d) ℂ) =
      (y : Matrix (Fin d) (Fin d) ℂ) * (x : Matrix (Fin d) (Fin d) ℂ)
    rw [hx, hy]
    ext i j
    by_cases hij : i = j <;> simp [hij,
      mul_comm]
  · intro rho hPos hTrace hFixedRho
    rcases (record_channel_fixed_iff_diagonal record hNormalized hDistinct rho).mp hFixedRho with
      ⟨p, hp⟩
    exact diagonal_probability_representation rho hPos hTrace p hp

#print axioms singleton_record_classicality

end D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality
