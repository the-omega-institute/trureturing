/- GID: D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/SharedEnergyCopyThreshold
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sparse three-level density matrices and their shared-energy relations. -/

import D5.S3.Quantum.Fibers.RealCopyConjugation
import D5.S3.Quantum.Foundation.EffectProbabilityExtension
import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Sparse density states in the fixed three-level energy basis. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Kronecker

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

/-- A single labelled occurrence of an ordered matrix coordinate. -/
def coordinateExponent (i j : Fin 3) : Exponent :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- The full labelled exponent of a native tensor matrix entry. -/
def tensorExponent : (n : ℕ) → CopyIndex (Fin 3) n → CopyIndex (Fin 3) n → Exponent
  | 0, _, _ => 0
  | 1, I, J => coordinateExponent I J
  | n + 2, I, J => coordinateExponent I.1 J.1 + tensorExponent (n+1) I.2 J.2

/-- Total energy of a native product-basis word. -/
def totalEnergy (m : ℕ) : (n : ℕ) → CopyIndex (Fin 3) n → ℤ
  | 0, _ => 0
  | 1, I => energy m I
  | n + 2, I => energy m I.1 + totalEnergy m (n+1) I.2

private theorem coordinate_degree (i j : Fin 3) : degree (coordinateExponent i j) = 1 := by
  classical
  simp [degree, coordinateExponent, ite_and]

private theorem coordinate_weight (m : ℕ) (i j : Fin 3) :
    weight m (coordinateExponent i j) = energy m i - energy m j := by
  classical
  simp [weight, coordinateExponent, ite_and, apply_ite]

private theorem coordinate_monomial (X : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    monomial X (coordinateExponent i j) = X i j := by
  classical
  simp [monomial, coordinateExponent, ite_and, apply_ite]

private theorem degree_add (a b : Exponent) : degree (a+b) = degree a + degree b := by
  simp [degree, Finset.sum_add_distrib]

private theorem weight_add (m : ℕ) (a b : Exponent) :
    weight m (a+b) = weight m a + weight m b := by
  simp [weight, Nat.cast_add, add_mul, Finset.sum_add_distrib]

private theorem monomial_add (X : Matrix (Fin 3) (Fin 3) ℂ) (a b : Exponent) :
    monomial X (a+b) = monomial X a * monomial X b := by
  simp [monomial, pow_add, Finset.prod_mul_distrib]

private theorem tensor_degree : ∀ (n : ℕ) (I J : CopyIndex (Fin 3) n),
    degree (tensorExponent n I J) = n
  | 0, _, _ => by simp [tensorExponent, degree]
  | 1, I, J => coordinate_degree I J
  | n+2, I, J => by
    rw [tensorExponent, degree_add, coordinate_degree, tensor_degree]
    omega

private theorem tensor_weight (m : ℕ) : ∀ (n : ℕ) (I J : CopyIndex (Fin 3) n),
    weight m (tensorExponent n I J) = totalEnergy m n I - totalEnergy m n J
  | 0, _, _ => by simp [tensorExponent, weight, totalEnergy]
  | 1, I, J => coordinate_weight m I J
  | n+2, I, J => by
    rw [tensorExponent, weight_add, coordinate_weight, tensor_weight]
    simp only [totalEnergy]
    ring

private theorem tensor_entry (r : DensityState (Fin 3)) :
    ∀ (n : ℕ) (I J : CopyIndex (Fin 3) n),
    stateMatrix (copies r n) I J = monomial (stateMatrix r) (tensorExponent n I J)
  | 0, I, J => by
    have : I = J := @Subsingleton.elim PUnit _ I J
    simp [copies, stateMatrix, tensorExponent, monomial, this]
  | 1, I, J => (coordinate_monomial _ I J).symm
  | n+2, I, J => by
    change stateMatrix r I.1 J.1 * stateMatrix (copies r (n+1)) I.2 J.2 = _
    rw [tensorExponent, monomial_add, coordinate_monomial, tensor_entry]

private theorem degree_zero (alpha : Exponent) : degree alpha = 0 ↔ alpha = 0 := by
  simp [degree, Finset.sum_eq_zero_iff, funext_iff]

private theorem exponent_words : ∀ n (alpha : Exponent), degree alpha = n →
    ∃ I J : CopyIndex (Fin 3) n, tensorExponent n I J = alpha
  | 0, alpha, hd => by
    refine ⟨PUnit.unit, PUnit.unit, ?_⟩
    simpa only [tensorExponent] using ((degree_zero alpha).mp hd).symm
  | n+1, alpha, hd => by
    obtain ⟨i, j, hij⟩ : ∃ i j, alpha i j ≠ 0 := by
      by_contra! h
      have hz : alpha = 0 := funext fun a => funext fun b => h a b
      simp [hz, degree] at hd
    let beta := alpha - coordinateExponent i j
    have hle : coordinateExponent i j ≤ alpha := by
      intro a b
      simp only [coordinateExponent]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        omega
      · exact Nat.zero_le _
    have hadd : coordinateExponent i j + beta = alpha := add_tsub_cancel_of_le hle
    have hb : degree beta = n := by
      have he := congrArg degree hadd
      rw [degree_add, coordinate_degree, hd] at he
      omega
    cases n with
    | zero =>
      have hz := (degree_zero beta).mp hb
      refine ⟨i, j, ?_⟩
      simpa only [tensorExponent, hz, add_zero] using hadd
    | succ k =>
      obtain ⟨I, J, hIJ⟩ := exponent_words (k+1) beta hb
      refine ⟨(i, I), (j, J), ?_⟩
      simpa only [tensorExponent, hIJ] using hadd

/-- The full projection onto one total energy, with all its degeneracy retained. -/
def energyProjector (m n : ℕ) (e : ℤ) :
    Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ :=
  Matrix.diagonal (fun I => if totalEnergy m n I = e then 1 else 0)

/-- Complete total-energy pinching on arbitrary complex matrices. -/
def energyPinch (m n : ℕ)
    (X : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ) :
    Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ :=
  ∑ e ∈ Finset.univ.image (totalEnergy m n),
    energyProjector m n e * X * energyProjector m n e

/-- Complete pinching of the native tensor copies. -/
def pinchedCopies (m n : ℕ) (r : DensityState (Fin 3)) :
    Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ :=
  energyPinch m n (stateMatrix (copies r n))

private theorem energy_pinch_apply (m n : ℕ)
    (X : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ)
    (I J : CopyIndex (Fin 3) n) : energyPinch m n X I J =
      if totalEnergy m n I = totalEnergy m n J then X I J else 0 := by
  simp only [energyPinch, Matrix.sum_apply]
  rw [Finset.sum_eq_single (totalEnergy m n I)]
  · simp [energyProjector, Matrix.mul_diagonal, Matrix.diagonal_mul, eq_comm]
  · intro e he hne
    simp [energyProjector, Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_image.mpr ⟨I, Finset.mem_univ _, rfl⟩)).elim

private theorem pinched_apply (m n : ℕ) (r : DensityState (Fin 3))
    (I J : CopyIndex (Fin 3) n) : pinchedCopies m n r I J =
      if totalEnergy m n I = totalEnergy m n J then stateMatrix (copies r n) I J else 0 :=
  energy_pinch_apply m n _ I J

private theorem energy_pinch_positive (m n : ℕ)
    (X : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ) (hX : X.PosSemidef) :
    (energyPinch m n X).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e he
  have hp : (energyProjector m n e).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro I
    change (0 : ℂ) ≤ if totalEnergy m n I = e then 1 else 0
    split_ifs <;> simp
  simpa only [hp.isHermitian.eq] using
    hX.mul_mul_conjTranspose_same (energyProjector m n e)

private theorem pinched_positive (m n : ℕ) (r : DensityState (Fin 3)) :
    (pinchedCopies m n r).PosSemidef :=
  energy_pinch_positive m n _ (density_posSemidef (copies r n))

private theorem energy_pinch_one (m n : ℕ) :
    energyPinch m n 1 = 1 := by
  ext I J
  by_cases h : I = J <;> simp [energy_pinch_apply, Matrix.one_apply, h]

private theorem energy_pinch_sub (m n : ℕ)
    (X Y : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ) :
    energyPinch m n (X-Y) = energyPinch m n X - energyPinch m n Y := by
  ext I J
  simp only [energy_pinch_apply, Matrix.sub_apply]
  split_ifs <;> simp

private theorem energy_pinch_pairing (m n : ℕ)
    (F X : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ) :
    Matrix.trace (F * energyPinch m n X) = Matrix.trace (energyPinch m n F * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, energy_pinch_apply]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases h : totalEnergy m n I = totalEnergy m n J
  · simp only [h, ite_true]
  · simp [h, Ne.symm h]

private theorem pinched_trace (m n : ℕ) (r : DensityState (Fin 3)) :
    Matrix.trace (pinchedCopies m n r) = 1 := by
  have h : Matrix.trace (pinchedCopies m n r) = Matrix.trace (stateMatrix (copies r n)) := by
    simp only [Matrix.trace, Matrix.diag, pinched_apply, ite_true]
  exact h.trans (copies r n).2.2

/-- Every actual tensor entry has the indicated labelled exponent, total degree
and weight. Its total-energy pinching retains exactly the zero-weight entries. -/
theorem tensor_monomial_bridge (m n : ℕ) (r : DensityState (Fin 3))
    (I J : CopyIndex (Fin 3) n) :
    degree (tensorExponent n I J) = n ∧
    weight m (tensorExponent n I J) = totalEnergy m n I - totalEnergy m n J ∧
    stateMatrix (copies r n) I J = monomial (stateMatrix r) (tensorExponent n I J) ∧
    (pinchedCopies m n r I J = if weight m (tensorExponent n I J) = 0 then
      monomial (stateMatrix r) (tensorExponent n I J) else 0) ∧
    (pinchedCopies m n r).PosSemidef ∧ Matrix.trace (pinchedCopies m n r) = 1 := by
  refine ⟨tensor_degree n I J, tensor_weight m n I J, tensor_entry r n I J, ?_,
    pinched_positive m n r, pinched_trace m n r⟩
  simp only [pinched_apply, tensor_weight, sub_eq_zero, tensor_entry]

/-- Every labelled exponent is realized by actual native tensor words. The same
words work for all density states, including zero entries and deficient rank. -/
theorem exponent_tensor_bridge (m : ℕ) (alpha : Exponent) :
    ∃ I J : CopyIndex (Fin 3) (degree alpha),
      tensorExponent (degree alpha) I J = alpha ∧
      totalEnergy m (degree alpha) I - totalEnergy m (degree alpha) J = weight m alpha ∧
      ∀ r : DensityState (Fin 3),
        stateMatrix (copies r (degree alpha)) I J = monomial (stateMatrix r) alpha ∧
        pinchedCopies m (degree alpha) r I J =
          if weight m alpha = 0 then monomial (stateMatrix r) alpha else 0 := by
  obtain ⟨I, J, h⟩ := exponent_words (degree alpha) alpha rfl
  refine ⟨I, J, h, ?_, ?_⟩
  · rw [← tensor_weight, h]
  · intro r
    have he := tensor_monomial_bridge m (degree alpha) r I J
    simpa only [h] using And.intro he.2.2.1 he.2.2.2.1

/-- Below twice the upper energy minus one, the literal sparse native tensor
states have equal complete total-energy pinchings. -/
theorem sparse_low_pinching (m n : ℕ) (hm : 2 ≤ m) (hn : n < 2*m-1) :
    pinchedCopies m n rho = pinchedCopies m n (sigma m) := by
  ext I J
  rw [(tensor_monomial_bridge m n rho I J).2.2.2.1,
    (tensor_monomial_bridge m n (sigma m) I J).2.2.2.1]
  split_ifs with h
  · exact sparse_low_monomials m hm (tensorExponent n I J)
      (by rwa [tensor_degree]) h (phase m) (unit_phase _)
  · rfl

/-- A finite tuple in the same native, recursively parenthesized tensor basis. -/
def wordIndex : (n : ℕ) → (Fin n → Fin 3) → CopyIndex (Fin 3) n
  | 0, _ => PUnit.unit
  | 1, f => f 0
  | n+2, f => (f 0, wordIndex (n+1) (Fin.tail f))

private theorem wordIndex_injective : ∀ n, Function.Injective (wordIndex n)
  | 0 => by intro f g _; funext i; exact Fin.elim0 i
  | 1 => by
    intro f g h
    funext i
    change f 0 = g 0 at h
    simpa only [Subsingleton.elim i 0] using h
  | n+2 => by
    intro f g h
    have h₀ : f 0 = g 0 := congrArg Prod.fst h
    have ht : Fin.tail f = Fin.tail g := wordIndex_injective (n+1) (congrArg Prod.snd h)
    funext i
    exact Fin.cases h₀ (fun j => congrFun ht j) i

private theorem word_energy (m : ℕ) : ∀ (n : ℕ) (f : Fin n → Fin 3),
    totalEnergy m n (wordIndex n f) = ∑ k, energy m (f k)
  | 0, f => by simp [totalEnergy, wordIndex]
  | 1, f => by simp [totalEnergy, wordIndex]
  | n+2, f => by
    simp only [wordIndex, totalEnergy, word_energy, Fin.sum_univ_succ, Fin.tail]

private theorem word_entry (r : DensityState (Fin 3)) :
    ∀ (n : ℕ) (f g : Fin n → Fin 3),
    stateMatrix (copies r n) (wordIndex n f) (wordIndex n g) =
      ∏ k, stateMatrix r (f k) (g k)
  | 0, f, g => by
    change (1 : ℂ) = ∏ k : Fin 0, stateMatrix r (f k) (g k)
    simp
  | 1, f, g => by rw [Fin.prod_univ_one]; rfl
  | n+2, f, g => by
    change stateMatrix r (f 0) (g 0) *
      stateMatrix (copies r (n+1)) (wordIndex (n+1) (Fin.tail f))
        (wordIndex (n+1) (Fin.tail g)) = _
    conv_rhs => rw [Fin.prod_univ_succ]
    rw [word_entry]
    rfl

/-- The distinguishing batch length, written as the two actual block lengths. -/
abbrev copyOrder (m : ℕ) : ℕ := m + (m-1)

/-- The actual word with m copies of level two followed by m minus one zeros. -/
def wordI (m : ℕ) : CopyIndex (Fin 3) (copyOrder m) :=
  wordIndex _ (Fin.append (fun _ : Fin m => 2) (fun _ : Fin (m-1) => 0))

/-- The actual word with m copies of level one followed by m minus one twos. -/
def wordJ (m : ℕ) : CopyIndex (Fin 3) (copyOrder m) :=
  wordIndex _ (Fin.append (fun _ : Fin m => 1) (fun _ : Fin (m-1) => 2))

/-- The sum of the one-copy Hamiltonians on the native tensor product. -/
def totalHamiltonian (m : ℕ) : (n : ℕ) →
    Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ
  | 0 => 0
  | 1 => Matrix.diagonal (fun i => (energy m i : ℂ))
  | n+2 => (Matrix.diagonal (fun i => (energy m i : ℂ))) ⊗ₖ 1 +
      (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ totalHamiltonian m (n+1)

theorem total_hamiltonian_diagonal (m : ℕ) : ∀ n,
    totalHamiltonian m n = Matrix.diagonal (fun I => (totalEnergy m n I : ℂ))
  | 0 => by ext I J; simp [totalHamiltonian, totalEnergy, Matrix.diagonal]
  | 1 => rfl
  | n+2 => by
    rw [totalHamiltonian, total_hamiltonian_diagonal]
    apply Matrix.ext
    rintro ⟨a, I⟩ ⟨b, J⟩
    change (if a = b then (energy m a : ℂ) else 0) * (if I = J then 1 else 0) +
      (if a = b then 1 else 0) * (if I = J then (totalEnergy m (n+1) I : ℂ) else 0) =
      if (a, I) = (b, J) then ((energy m a + totalEnergy m (n+1) I : ℤ) : ℂ) else 0
    by_cases h₁ : a = b <;> by_cases h₂ : I = J <;>
      simp [h₁, h₂, Prod.mk.injEq]

private theorem energy_pinch_commutes (m n : ℕ)
    (X : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ) :
    energyPinch m n X * totalHamiltonian m n =
      totalHamiltonian m n * energyPinch m n X := by
  ext I J
  simp only [total_hamiltonian_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    energy_pinch_apply]
  split_ifs with h <;> simp [h, mul_comm]

private theorem energy_pinch_fixed (m n : ℕ)
    (F : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ)
    (hF : F * totalHamiltonian m n = totalHamiltonian m n * F) :
    energyPinch m n F = F := by
  ext I J
  rw [energy_pinch_apply]
  split_ifs with h
  · rfl
  · have he := congrArg (fun X => X I J) hF
    simp only [total_hamiltonian_diagonal, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at he
    have hn : (totalEnergy m n J : ℂ) - (totalEnergy m n I : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (fun he => h (Int.cast_injective he).symm)
    have hz : F I J * ((totalEnergy m n J : ℂ) - (totalEnergy m n I : ℂ)) = 0 := by
      linear_combination he
    exact ((mul_eq_zero.mp hz).resolve_right hn).symm

/-- Equality of the complete energy pinchings is exactly equality of the
unconditional complex trace pairing for every effect commuting with the actual
sum Hamiltonian. The effects retain arbitrary complex entries inside every
degenerate total-energy block. -/
theorem compatible_effects_iff (m n : ℕ) (r s : DensityState (Fin 3)) :
    pinchedCopies m n r = pinchedCopies m n s ↔
      ∀ F : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ,
        F.PosSemidef → (1-F).PosSemidef →
        F * totalHamiltonian m n = totalHamiltonian m n * F →
        Matrix.trace (F * stateMatrix (copies r n)) =
          Matrix.trace (F * stateMatrix (copies s n)) := by
  have pairing (F : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ)
      (hF : F * totalHamiltonian m n = totalHamiltonian m n * F)
      (q : DensityState (Fin 3)) :
      Matrix.trace (F * pinchedCopies m n q) =
        Matrix.trace (F * stateMatrix (copies q n)) := by
    change Matrix.trace (F * energyPinch m n _) = _
    rw [energy_pinch_pairing, energy_pinch_fixed m n F hF]
  constructor
  · intro h F _ _ hF
    rw [← pairing F hF r, h, pairing F hF s]
  · intro h
    apply D5.S3.Quantum.Foundation.EffectProbabilityExtension.effect_trace_unique
    intro E hE hE₁
    let X := CStarMatrix.ofMatrix.symm E
    have hX : X.PosSemidef :=
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hE).posSemidef
    have hX₁ : (1-X).PosSemidef := by
      apply Matrix.nonneg_iff_posSemidef.mp
      change (0 : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ) ≤
        CStarMatrix.ofMatrixStarAlgEquiv.symm (1-E)
      exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sub_nonneg.mpr hE₁)
    have hP : (1-energyPinch m n X).PosSemidef := by
      rw [← energy_pinch_one m n, ← energy_pinch_sub]
      exact energy_pinch_positive m n _ hX₁
    have he := h (energyPinch m n X) (energy_pinch_positive m n X hX) hP
      (energy_pinch_commutes m n X)
    change Matrix.trace (pinchedCopies m n r * X) =
      Matrix.trace (pinchedCopies m n s * X)
    rw [Matrix.trace_mul_comm, Matrix.trace_mul_comm (pinchedCopies m n s)]
    change Matrix.trace (X * energyPinch m n _) = Matrix.trace (X * energyPinch m n _)
    rw [energy_pinch_pairing, energy_pinch_pairing]
    exact he

/-- The two explicit orthogonal product-basis words have energy m squared,
and their actual tensor matrix element is the distinguished monomial. -/
theorem sparse_joint_words (m : ℕ) (hm : 2 ≤ m) :
    copyOrder m = 2*m-1 ∧ wordI m ≠ wordJ m ∧
    totalEnergy m (copyOrder m) (wordI m) = (m : ℤ)^2 ∧
    totalEnergy m (copyOrder m) (wordJ m) = (m : ℤ)^2 ∧
    ∀ r : DensityState (Fin 3),
      stateMatrix (copies r (copyOrder m)) (wordI m) (wordJ m) =
        starMonomial m (stateMatrix r) := by
  refine ⟨by simp [copyOrder]; omega, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' := wordIndex_injective (copyOrder m) h
    have he := congrFun h' (Fin.castAdd (m-1) (⟨0, by omega⟩ : Fin m))
    simp only [Fin.append_left] at he
    norm_num at he
  · rw [wordI, word_energy, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, energy]
    ring
  · rw [wordJ, word_energy, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, energy, Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  · intro r
    rw [wordI, wordJ, word_entry, Fin.prod_univ_add]
    simp [Fin.append_left, Fin.append_right, starMonomial]

/-- The literal projector onto the equal real superposition of the two words. -/
def jointEffect (m : ℕ) :
    Matrix (CopyIndex (Fin 3) (copyOrder m)) (CopyIndex (Fin 3) (copyOrder m)) ℂ :=
  let v := Pi.single (wordI m) (1 : ℂ) + Pi.single (wordJ m) 1
  (2 : ℂ)⁻¹ • Matrix.vecMulVec v (star v)

private theorem joint_effect_bounds (m : ℕ) (hm : 2 ≤ m) :
    (jointEffect m).PosSemidef ∧ (1 - jointEffect m).PosSemidef := by
  let h := pairEffect (wordI m) (wordJ m) (sparse_joint_words m hm).2.1
  have he : jointEffect m = h.val := rfl
  rw [he]
  exact ⟨h.2.1, h.2.2.1⟩

private theorem joint_effect_commutes (m : ℕ) (hm : 2 ≤ m) :
    jointEffect m * totalHamiltonian m (copyOrder m) =
      totalHamiltonian m (copyOrder m) * jointEffect m := by
  have hI := (sparse_joint_words m hm).2.2.1
  have hJ := (sparse_joint_words m hm).2.2.2.1
  ext a b
  simp only [total_hamiltonian_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases haI : a = wordI m <;> by_cases haJ : a = wordJ m <;>
    by_cases hbI : b = wordI m <;> by_cases hbJ : b = wordJ m <;>
    simp [jointEffect, Matrix.vecMulVec, Pi.single_apply, haI, haJ, hbI, hbJ,
      hI, hJ, eq_comm, mul_comm]

private theorem joint_effect_trace (m : ℕ)
    (X : Matrix (CopyIndex (Fin 3) (copyOrder m))
      (CopyIndex (Fin 3) (copyOrder m)) ℂ) :
    Matrix.trace (jointEffect m * X) = (2 : ℂ)⁻¹ *
      (X (wordI m) (wordI m) + X (wordJ m) (wordI m) +
        X (wordI m) (wordJ m) + X (wordJ m) (wordJ m)) := by
  rw [jointEffect, Matrix.smul_mul, Matrix.trace_smul, Matrix.vecMulVec_mul,
    Matrix.trace_vecMulVec]
  simp [add_dotProduct, Matrix.vecMul, mul_add]
  ring

private theorem sparse_diagonal_copies (u : ℂ) (hu : u * star u = 1) :
    ∀ (n : ℕ) (I : CopyIndex (Fin 3) n),
      stateMatrix (copies (sparseState u hu) n) I I = (1/3 : ℂ)^n
  | 0, I => by simp [copies, stateMatrix]
  | 1, I => by
    change sparseMatrix u I I = (1/3 : ℂ)^1
    fin_cases I <;> norm_num [sparseMatrix]
  | n+2, I => by
    change stateMatrix (sparseState u hu) I.1 I.1 *
      stateMatrix (copies (sparseState u hu) (n+1)) I.2 I.2 = _
    rw [sparse_diagonal_copies u hu (n+1)]
    have hd : stateMatrix (sparseState u hu) I.1 I.1 = (1/3 : ℂ) := by
      generalize I.1 = i
      change sparseMatrix u i i = (1/3 : ℂ)
      fin_cases i <;> norm_num [sparseMatrix]
    simp only [hd, pow_succ']

private theorem joint_born_laws (m : ℕ) (hm : 2 ≤ m) :
    Matrix.trace (jointEffect m * stateMatrix (copies rho (copyOrder m))) =
      (1/3 : ℂ)^(2*m-1) + (1/12 : ℂ)^(2*m-1) ∧
    Matrix.trace (jointEffect m * stateMatrix (copies (sigma m) (copyOrder m))) =
      (1/3 : ℂ)^(2*m-1) - (1/12 : ℂ)^(2*m-1) := by
  have hw := sparse_joint_words m hm
  have hp := sparse_pair_data m hm
  have h (r : DensityState (Fin 3)) :
      stateMatrix (copies r (copyOrder m)) (wordJ m) (wordI m) =
        star (starMonomial m (stateMatrix r)) := by
    rw [← hw.2.2.2.2 r]
    exact ((density_posSemidef (copies r (copyOrder m))).isHermitian.apply _ _).symm
  constructor
  · rw [joint_effect_trace, h, hw.2.2.2.2, hp.2.2.1]
    rw [show rho = sparseState 1 (by simp) from rfl,
      sparse_diagonal_copies, sparse_diagonal_copies, hw.1]
    simp only [star_pow, star_div₀, star_one, star_natCast, star_ofNat]
    ring
  · rw [joint_effect_trace, h, hw.2.2.2.2, hp.2.2.2.1]
    rw [show sigma m = sparseState (phase m) (unit_phase _) from rfl,
      sparse_diagonal_copies, sparse_diagonal_copies, hw.1]
    simp only [star_neg, star_pow, star_div₀, star_one, star_natCast, star_ofNat]
    ring

/-- The native equal-energy projection is an effect and gives the two exact,
unconditional Born probabilities. Their gap is strictly positive. The complete
pinchings differ at this batch length, while every compatible complex effect
has equal probabilities at every smaller copy count. -/
theorem sparse_joint_effect (m : ℕ) (hm : 2 ≤ m) :
    (jointEffect m).PosSemidef ∧ (1-jointEffect m).PosSemidef ∧
    jointEffect m * totalHamiltonian m (copyOrder m) =
      totalHamiltonian m (copyOrder m) * jointEffect m ∧
    Matrix.trace (jointEffect m * stateMatrix (copies rho (copyOrder m))) =
      (1/3 : ℂ)^(2*m-1) + (1/12 : ℂ)^(2*m-1) ∧
    Matrix.trace (jointEffect m * stateMatrix (copies (sigma m) (copyOrder m))) =
      (1/3 : ℂ)^(2*m-1) - (1/12 : ℂ)^(2*m-1) ∧
    (0 : ℝ) < 2*(1/12 : ℝ)^(2*m-1) ∧
    (1/3 : ℝ)^(2*m-1) + (1/12 : ℝ)^(2*m-1) ∈ Set.Icc (0 : ℝ) 1 ∧
    (1/3 : ℝ)^(2*m-1) - (1/12 : ℝ)^(2*m-1) ∈ Set.Icc (0 : ℝ) 1 ∧
    pinchedCopies m (copyOrder m) rho ≠ pinchedCopies m (copyOrder m) (sigma m) ∧
    ∀ n : ℕ, n < 2*m-1 →
      ∀ F : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ,
        F.PosSemidef → (1-F).PosSemidef →
        F * totalHamiltonian m n = totalHamiltonian m n * F →
        Matrix.trace (F * stateMatrix (copies rho n)) =
          Matrix.trace (F * stateMatrix (copies (sigma m) n)) := by
  have hb := joint_effect_bounds m hm
  have hp := joint_born_laws m hm
  refine ⟨hb.1, hb.2, joint_effect_commutes m hm, hp.1, hp.2,
    by positivity, ?_, ?_, ?_, ?_⟩
  · have h₃ : (1/3 : ℝ)^(2*m-1) ≤ 1/3 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have h₁₂ : (1/12 : ℝ)^(2*m-1) ≤ 1/12 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    exact ⟨by positivity, by linarith⟩
  · refine ⟨sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) (by norm_num) _), ?_⟩
    exact le_trans (sub_le_self _ (by positivity))
      (pow_le_one₀ (by norm_num) (by norm_num))
  · intro he
    have hw := sparse_joint_words m hm
    have hE : totalEnergy m (copyOrder m) (wordI m) =
        totalEnergy m (copyOrder m) (wordJ m) := hw.2.2.1.trans hw.2.2.2.1.symm
    have he' := congrArg (fun X => X (wordI m) (wordJ m)) he
    simp only [pinched_apply, hE, ite_true, hw.2.2.2.2,
      (sparse_pair_data m hm).2.2.1, (sparse_pair_data m hm).2.2.2.1] at he'
    have hz : (1/12 : ℂ)^(2*m-1) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact hz (by linear_combination (1/2 : ℂ) * he')
  · intro n hn F hF hF₁ hFH
    exact (compatible_effects_iff m n rho (sigma m)).mp
      (sparse_low_pinching m n hm hn) F hF hF₁ hFH

/-- A nonzero labelled zero-weight exponent with no proper nonzero
zero-weight subexponent. Labels, including diagonal labels, are retained. -/
def Indecomposable (m : ℕ) (alpha : Exponent) : Prop :=
  alpha ≠ 0 ∧ weight m alpha = 0 ∧
    ∀ beta : Exponent, beta ≤ alpha → weight m beta = 0 → beta = 0 ∨ beta = alpha



#print axioms total_hamiltonian_diagonal
#print axioms exponent_tensor_bridge
#print axioms tensor_monomial_bridge
#print axioms compatible_effects_iff
#print axioms sparse_low_pinching
#print axioms sparse_joint_words
#print axioms sparse_joint_effect
#print axioms sparse_low_monomials
#print axioms sparse_density_spectrum
#print axioms sparse_pair_data

end D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
