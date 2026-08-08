/- GID: D5/S3/QuantumBounds/CHSHSpectrum
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/CHSHSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute the CHSH cubic coefficient and constrain its real spectrum. -/

/- Library-search audit trail (2026-08-08):
   * Local mathlib searches for `spectrum.*pow`, `pow.*spectrum`, `spectral.*mapping`,
     `IsHermitian.*spectrum`, and `spectrum_real_eq_range_eigenvalues` found
     `spectrum.pow_mem_pow`, `spectrum.map_pow`,
     `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, and
     `Matrix.IsHermitian.eigenvalues_mem_spectrum_real`. The proof uses the one-way power lemma,
     which is sufficient for the required spectral inclusion.
   * Searches for scalar shifts and cosets found `spectrum.add_mem_add_iff` and
     `spectrum.singleton_add_eq`; the former transports the spectrum of `4I + C` back to that of
     `C` without a characteristic-polynomial expansion.
   * `Matrix.mem_spectrum_iff_isRoot_charpoly` and the polynomial spectral mapping theorem were
     inspected but are not needed. Searches for an existing CHSH cubic-coefficient or four-point
     spectrum theorem found none.
   * The real-algebra proof reuses `field_simp`, `ring`, `Real.sq_sqrt`, and
     `eq_or_eq_neg_of_sq_eq_sq`. The CHSH square itself is not reproved: it is supplied by the
     repository theorem `LandauIdentity.landau_identity` imported below.
-/

import D5.S3.QuantumBounds.LandauIdentity

namespace D5.S3.QuantumBounds.CHSHSpectrum

open Matrix Set
open scoped Kronecker

/-- After pairing the two vertices with magnitude `a` and the two with magnitude `b`, the
Vandermonde gap coefficient is the stated rational function of the commutator parameter `N`. -/
theorem chsh_cubic_coefficient (N a b : ℝ)
    (hNpos : 0 < N) (hNlt : N < 4)
    (ha : a ^ 2 = 4 + N) (hb : b ^ 2 = 4 - N) :
    2 / (16 * N ^ 2 * a ^ 2) + 2 / (16 * N ^ 2 * b ^ 2) =
      1 / (N ^ 2 * (16 - N ^ 2)) := by
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hPlusNe : 4 + N ≠ 0 := ne_of_gt (by linarith)
  have hMinusNe : 4 - N ≠ 0 := ne_of_gt (by linarith)
  have hDiscNe : 16 - N ^ 2 ≠ 0 := by nlinarith
  rw [ha, hb]
  field_simp
  ring

private theorem spectrum_subset_four_points {n : Type*} [Fintype n] [DecidableEq n]
    (N : ℝ) (hNpos : 0 < N) (hNlt : N < 4)
    (S C : Matrix n n ℂ) (hS : S.IsHermitian)
    (hSquare : S ^ 2 = 4 + C)
    (hC : spectrum ℝ C ⊆ {N, -N}) :
    spectrum ℝ S ⊆
      {Real.sqrt (4 + N), -Real.sqrt (4 + N),
        Real.sqrt (4 - N), -Real.sqrt (4 - N)} := by
  rw [hS.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  have hx : hS.eigenvalues i ∈ spectrum ℝ S := hS.eigenvalues_mem_spectrum_real i
  have hxSquare : hS.eigenvalues i ^ 2 ∈ spectrum ℝ (S ^ 2) :=
    spectrum.pow_mem_pow S 2 hx
  rw [hSquare] at hxSquare
  have hxC : hS.eigenvalues i ^ 2 - 4 ∈ spectrum ℝ C := by
    apply (spectrum.add_mem_add_iff
      (a := C) (r := hS.eigenvalues i ^ 2 - 4) (s := 4)).mp
    have hFour : algebraMap ℝ (Matrix n n ℂ) 4 = 4 := by
      ext i j
      simp [Algebra.algebraMap_eq_smul_one, Matrix.ofNat_apply, Matrix.one_apply]
    rw [hFour]
    simpa only [sub_add_cancel] using hxSquare
  have hxCases : hS.eigenvalues i ^ 2 - 4 = N ∨
      hS.eigenvalues i ^ 2 - 4 = -N := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hC hxC
  have hPlusSq : (Real.sqrt (4 + N)) ^ 2 = 4 + N := by
    rw [Real.sq_sqrt (by linarith)]
  have hMinusSq : (Real.sqrt (4 - N)) ^ 2 = 4 - N := by
    rw [Real.sq_sqrt (by linarith)]
  rcases hxCases with hxPlus | hxMinus
  · have hxRoot : hS.eigenvalues i = Real.sqrt (4 + N) ∨
        hS.eigenvalues i = -Real.sqrt (4 + N) := by
      apply eq_or_eq_neg_of_sq_eq_sq
      nlinarith
    rcases hxRoot with h | h
    · simp [h]
    · simp [h]
  · have hxRoot : hS.eigenvalues i = Real.sqrt (4 - N) ∨
        hS.eigenvalues i = -Real.sqrt (4 - N) := by
      apply eq_or_eq_neg_of_sq_eq_sq
      nlinarith
    rcases hxRoot with h | h
    · simp [h]
    · simp [h]

private theorem hermitian_kronecker {m n : Type*}
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  change (A ⊗ₖ B)ᴴ = A ⊗ₖ B
  rw [Matrix.conjTranspose_kronecker, hA, hB]

/-- For four finite-dimensional Hermitian involutions, Landau's identity and a two-point real
spectrum bound on its commutator term constrain the CHSH real spectrum to four square roots. -/
theorem chsh_spectrum {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (N : ℝ) (hNpos : 0 < N) (hNlt : N < 4)
    (A₀ A₁ : Matrix m m ℂ) (B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian ∧ A₀ ^ 2 = 1)
    (hA₁ : A₁.IsHermitian ∧ A₁ ^ 2 = 1)
    (hB₀ : B₀.IsHermitian ∧ B₀ ^ 2 = 1)
    (hB₁ : B₁.IsHermitian ∧ B₁ ^ 2 = 1)
    (hC : spectrum ℝ
      (-((A₀ * A₁ - A₁ * A₀) ⊗ₖ (B₀ * B₁ - B₁ * B₀))) ⊆ {N, -N}) :
    let S := A₀ ⊗ₖ B₀ + A₀ ⊗ₖ B₁ + A₁ ⊗ₖ B₀ - A₁ ⊗ₖ B₁
    spectrum ℝ S ⊆
      {Real.sqrt (4 + N), -Real.sqrt (4 + N),
        Real.sqrt (4 - N), -Real.sqrt (4 - N)} := by
  dsimp only
  have hS :
      (A₀ ⊗ₖ B₀ + A₀ ⊗ₖ B₁ + A₁ ⊗ₖ B₀ - A₁ ⊗ₖ B₁).IsHermitian :=
    (((hermitian_kronecker hA₀.1 hB₀.1).add
      (hermitian_kronecker hA₀.1 hB₁.1)).add
      (hermitian_kronecker hA₁.1 hB₀.1)).sub
      (hermitian_kronecker hA₁.1 hB₁.1)
  have hSquare :=
    D5.S3.QuantumBounds.LandauIdentity.landau_identity
      A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
  dsimp only at hSquare
  apply spectrum_subset_four_points N hNpos hNlt _ _ hS _ hC
  simpa using hSquare

end D5.S3.QuantumBounds.CHSHSpectrum
