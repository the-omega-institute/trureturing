/- GID: D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/SharedEnergyCopyThreshold
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sparse three-level density matrices and their shared-energy relations. -/

import D5.S3.Quantum.Fibers.RealCopyConjugation
import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Sparse density states in the fixed three-level energy basis. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open Matrix
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.RealCopyConjugation
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The sparse Hermitian family in the fixed energy basis. -/
def sparseMatrix (u : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/3, 0, (1/12) * star u;
     0, 1/3, 1/12;
     (1/12) * u, 1/12, 1/3]

private theorem sparse_hermitian (u : ℂ) : (sparseMatrix u).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sparseMatrix, conjTranspose_apply, star_mul] <;> ring

private theorem sparse_trace (u : ℂ) : trace (sparseMatrix u) = 1 := by
  norm_num [sparseMatrix, trace, Fin.sum_univ_succ]

private theorem sparse_det_shift (u z : ℂ) (hu : u * star u = 1) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - sparseMatrix u).det =
      (z - 1/3) * ((z - 1/3)^2 - 2/144) := by
  simp only [sparseMatrix, Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  norm_num
  simp only [Complex.star_def] at hu
  linear_combination (-(z-1/3)/144) * hu

private theorem sparse_spectrum (u : ℂ) (hu : u * star u = 1) :
    spectrum ℂ (sparseMatrix u) =
      {1/3, 1/3 - (Real.sqrt 2 : ℂ)/12, 1/3 + (Real.sqrt 2 : ℂ)/12} := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  have he : algebraMap ℂ (Matrix (Fin 3) (Fin 3) ℂ) z = z • 1 := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, Matrix.one_apply]
  rw [he, sparse_det_shift u z hu, isUnit_iff_ne_zero, not_not]
  have hf : (z - 1/3) * ((z - 1/3)^2 - 2/144) =
      (z - 1/3) * (z - (1/3 - (Real.sqrt 2 : ℂ)/12)) *
        (z - (1/3 + (Real.sqrt 2 : ℂ)/12)) := by
    linear_combination ((z - 1/3)/144) * hs
  rw [hf]
  simp only [mul_eq_zero, sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem sparse_posDef (u : ℂ) (hu : u * star u = 1) :
    (sparseMatrix u).PosDef := by
  have hH := sparse_hermitian u
  apply hH.posDef_iff_eigenvalues_pos.mpr
  intro i
  have he : (hH.eigenvalues i : ℂ) ∈ spectrum ℂ (sparseMatrix u) :=
    spectrum.algebraMap_mem ℂ (hH.eigenvalues_mem_spectrum_real i)
  rw [sparse_spectrum u hu] at he
  have hsmall : Real.sqrt 2 < 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rcases he with he | he | he
  · have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  · have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  · have hr := congrArg Complex.re he
    norm_num at hr
    nlinarith [Real.sqrt_nonneg 2]

/-- Every unit phase gives a literal positive definite trace-one matrix with the
same exact three-point spectrum. -/
theorem sparse_density_spectrum (u : ℂ) (hu : u * star u = 1) :
    (sparseMatrix u).PosDef ∧ trace (sparseMatrix u) = 1 ∧
      spectrum ℂ (sparseMatrix u) =
        {1/3, 1/3 - (Real.sqrt 2 : ℂ)/12, 1/3 + (Real.sqrt 2 : ℂ)/12} :=
  ⟨sparse_posDef u hu, sparse_trace u, sparse_spectrum u hu⟩

/-- Native normalized states, rather than independent coordinate tables. -/
def sparseState (u : ℂ) (hu : u * star u = 1) : DensityState (Fin 3) :=
  ⟨CStarMatrix.ofMatrix (sparseMatrix u),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (sparse_density_spectrum u hu).1.posSemidef.nonneg,
    (sparse_density_spectrum u hu).2.1⟩

/-- The phase used in the sparse second state. -/
def phase (m : ℕ) : Circle := Circle.exp (Real.pi / ((m : ℝ) - 1))

private theorem unit_phase (u : Circle) : (u : ℂ) * star (u : ℂ) = 1 := by
  simp only [Complex.star_def, Complex.mul_conj, Circle.normSq_coe,
    Complex.ofReal_one]

/-- The first literal matrix in the sparse pair. -/
def rho : DensityState (Fin 3) := sparseState 1 (by simp)

/-- The second literal matrix in the sparse pair. -/
def sigma (m : ℕ) : DensityState (Fin 3) := sparseState (phase m) (unit_phase _)

private theorem phase_pow (m : ℕ) (hm : 2 ≤ m) : (phase m : ℂ) ^ (m-1) = -1 := by
  rw [phase, ← Circle.coe_pow, ← Circle.exp_natCast_mul]
  have h : ((m-1 : ℕ) : ℝ) * (Real.pi / ((m : ℝ)-1)) = Real.pi := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hn : (m : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (m : ℤ) - 1 ≠ 0 by omega)
    field_simp
  rw [h, Circle.coe_exp, Complex.exp_pi_mul_I]

private theorem supported_kernel_iff (m k₁ k₂ : ℤ) :
    (m-1)*k₁ + m*k₂ = 0 ↔ ∃ ell : ℤ, k₁ = ell*m ∧ k₂ = ell*(-(m-1)) := by
  open D5.S3.Arith.Lattices.CofactorKernel in
    constructor
    · intro hk
      let A : Matrix (Fin 1) (Fin 2) ℤ := !![m-1, m]
      let v : Fin 2 → ℤ := ![m, -(m-1)]
      have hdet : (augment A).det ≠ 0 := by
        have he : augment A = !![1, 1; m-1, m] := by
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        rw [he, Matrix.det_fin_two]
        change 1*m - 1*(m-1) ≠ 0
        omega
      have hv : A *ᵥ v = 0 := by
        ext i
        fin_cases i
        simp [A, v, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        ring
      have hsum : ∑ j, v j ≠ 0 := by simp [v, Fin.sum_univ_succ]
      have hgc : Finset.univ.gcd v = 1 := by
        have h₀ : Finset.univ.gcd v ∣ v 0 := Finset.gcd_dvd (Finset.mem_univ _)
        have h₁ : Finset.univ.gcd v ∣ v 1 := Finset.gcd_dvd (Finset.mem_univ _)
        have hd : Finset.univ.gcd v ∣ 1 := by
          convert dvd_add h₀ h₁ using 1; simp [v]
        have hn := normalize_eq_one.mpr (isUnit_iff_dvd_one.mpr hd)
        simpa only [Finset.normalize_gcd] using hn
      have hx : A *ᵥ ![k₁,k₂] = 0 := by
        ext i
        fin_cases i
        simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hk
      obtain ⟨ell, he⟩ := primitive_kernel_span A hdet v hv hsum hgc ![k₁,k₂] hx
      exact ⟨ell, by simpa [v] using he 0, by simpa [v] using he 1⟩
    · rintro ⟨ell, rfl, rfl⟩
      ring

private theorem supported_kernel_length (m ell : ℤ) (hm : 2 ≤ m) (he : ell ≠ 0) :
    2*m-1 ≤ |ell*m| + |ell*(-(m-1))| := by
  have h : 1 ≤ |ell| := by have := abs_pos.mpr he; omega
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by omega : 0 ≤ m),
    abs_of_nonneg (by omega : 0 ≤ m-1)]
  nlinarith

/-- The phase-sensitive zero-weight monomial, with all zero exponents interpreted
by ordinary natural powers. -/
def starMonomial (m : ℕ) (X : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  X 2 1 ^ m * X 0 2 ^ (m-1)

/-- The actual sparse positive states have opposite nonzero values of the first
supported primitive relation. The integer-kernel statement includes every sign. -/
theorem sparse_pair_data (m : ℕ) (hm : 2 ≤ m) :
    (stateMatrix rho).PosDef ∧ (stateMatrix (sigma m)).PosDef ∧
    starMonomial m (stateMatrix rho) = (1/12 : ℂ) ^ (2*m-1) ∧
    starMonomial m (stateMatrix (sigma m)) = -(1/12 : ℂ) ^ (2*m-1) ∧
    (∀ k₁ k₂ : ℤ, ((m : ℤ)-1)*k₁ + (m : ℤ)*k₂ = 0 ↔
      ∃ ell : ℤ, k₁ = ell*(m : ℤ) ∧ k₂ = ell*(-((m : ℤ)-1))) ∧
    (∀ ell : ℤ, ell ≠ 0 → (2*(m : ℤ)-1) ≤
      |ell*(m : ℤ)| + |ell*(-((m : ℤ)-1))|) := by
  refine ⟨(sparse_density_spectrum 1 (by simp)).1,
    (sparse_density_spectrum (phase m) (unit_phase _)).1, ?_, ?_,
    fun k₁ k₂ => supported_kernel_iff _ _ _,
    fun ell he => supported_kernel_length _ ell (by exact_mod_cast hm) he⟩
  · change (1/12 : ℂ)^m * ((1/12 : ℂ) * star (1 : ℂ))^(m-1) = _
    simp only [star_one, mul_one, ← pow_add]
    congr 1
    omega
  · change (1/12 : ℂ)^m * ((1/12 : ℂ) * star (phase m : ℂ))^(m-1) = _
    rw [mul_pow, ← mul_assoc, ← pow_add]
    have he : star (phase m : ℂ)^(m-1) = -1 := by
      rw [← star_pow, phase_pow m hm]
      simp
    rw [he, mul_neg_one]
    congr 2
    omega

/-- Integer energy labels in the fixed basis. -/
def energy (m : ℕ) : Fin 3 → ℤ := ![0, 1, m]

/-- Labelled ordered-coordinate exponents. Equal numerical gaps keep their labels. -/
abbrev Exponent := Fin 3 → Fin 3 → ℕ

/-- Total polynomial degree. -/
def degree (alpha : Exponent) : ℕ := ∑ i, ∑ j, alpha i j

/-- The actual integer weight of a labelled monomial. -/
def weight (m : ℕ) (alpha : Exponent) : ℤ :=
  ∑ i, ∑ j, (alpha i j : ℤ) * (energy m i - energy m j)

/-- A polynomial monomial in all nine actual matrix entries. -/
def monomial (X : Matrix (Fin 3) (Fin 3) ℂ) (alpha : Exponent) : ℂ :=
  ∏ i, ∏ j, X i j ^ alpha i j

/-- Every supported low-degree zero-weight monomial is independent of the unit
phase. Monomials containing one of the actual zero coordinates vanish on both
matrices; their zero powers remain one. -/
theorem sparse_low_monomials (m : ℕ) (hm : 2 ≤ m) (alpha : Exponent)
    (hd : degree alpha < 2*m-1) (hw : weight m alpha = 0)
    (u : ℂ) (hu : u * star u = 1) :
    monomial (sparseMatrix 1) alpha = monomial (sparseMatrix u) alpha := by
  by_cases hz : alpha 0 1 = 0 ∧ alpha 1 0 = 0
  · obtain ⟨hz₀,hz₁⟩ := hz
    let k₁ : ℤ := (alpha 2 1 : ℤ) - alpha 1 2
    let k₂ : ℤ := (alpha 2 0 : ℤ) - alpha 0 2
    have hk : ((m : ℤ)-1)*k₁ + (m : ℤ)*k₂ = 0 := by
      simp [weight, energy, Fin.sum_univ_succ, hz₀, hz₁] at hw
      dsimp [k₁, k₂]
      linear_combination hw
    obtain ⟨ell, he₁, he₂⟩ := (supported_kernel_iff (m : ℤ) k₁ k₂).mp hk
    have hnorm : |k₁| + |k₂| ≤ (degree alpha : ℤ) := by
      have h₁ : |k₁| ≤ (alpha 2 1 : ℤ) + alpha 1 2 := by
        dsimp [k₁]
        exact abs_le.mpr ⟨by omega, by omega⟩
      have h₂ : |k₂| ≤ (alpha 2 0 : ℤ) + alpha 0 2 := by
        dsimp [k₂]
        exact abs_le.mpr ⟨by omega, by omega⟩
      simp [degree, Fin.sum_univ_succ]
      omega
    have hlt : (degree alpha : ℤ) < 2*(m : ℤ)-1 := by
      have h : degree alpha + 1 < 2*m := by omega
      have h' : (degree alpha : ℤ) + 1 < 2*(m : ℤ) := by exact_mod_cast h
      omega
    have hell : ell = 0 := by
      by_contra hne
      have hlen := supported_kernel_length (m : ℤ) ell (by exact_mod_cast hm) hne
      rw [← he₁, ← he₂] at hlen
      omega
    have ha : alpha 2 1 = alpha 1 2 := by simp [hell, k₁] at he₁; omega
    have hb : alpha 2 0 = alpha 0 2 := by simp [hell, k₂] at he₂; omega
    have hp : star u ^ alpha 0 2 * u ^ alpha 0 2 = 1 := by
      rw [← mul_pow, mul_comm, hu, one_pow]
    simp [monomial, sparseMatrix, Fin.prod_univ_succ, hz₀, hz₁, ha, hb, mul_pow]
    simp only [Complex.star_def] at hp
    have hc := congrArg (fun z : ℂ =>
      ((1/3 : ℂ)^(alpha 0 0) * (1/3 : ℂ)^(alpha 1 1) *
        (1/3 : ℂ)^(alpha 2 2) * ((1/12 : ℂ)^(alpha 0 2))^2 *
        ((1/12 : ℂ)^(alpha 1 2))^2) * z) hp
    simp only [one_div, mul_one, pow_two] at hc
    convert hc.symm using 1 <;> (try simp only [one_div, inv_pow]; ring)
  · by_cases hz₀ : alpha 0 1 = 0
    · have hz₁ : alpha 1 0 ≠ 0 := fun h => hz ⟨hz₀,h⟩
      simp [monomial, sparseMatrix, Fin.prod_univ_succ, zero_pow hz₁]
    · simp [monomial, sparseMatrix, Fin.prod_univ_succ, zero_pow hz₀]

#print axioms sparse_low_monomials
#print axioms sparse_density_spectrum
#print axioms sparse_pair_data

end D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
