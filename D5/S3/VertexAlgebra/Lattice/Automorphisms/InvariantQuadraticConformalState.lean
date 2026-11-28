/- GID: D5/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Automorphisms/InvariantQuadraticConformalState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An invariant orthogonal projector gives a second actual fixed weight-two state. -/

import D5.S3.VertexAlgebra.Lattice.IsometryLift
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

/-! Quadratic oscillator covariance and the fixed weight-two obstruction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.InvariantQuadraticConformalState

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualConformalState LatticePositiveEnergy LatticeSugawaraCurrents
open IsometryLift Matrix MvPolynomial
open scoped BigOperators Matrix VertexOperator

noncomputable section

open private mixingMatrix oscillator_X lift_vacuum mixing_inverse from
  D5.S3.VertexAlgebra.Lattice.IsometryLift

private abbrev CurrentMatrix (D : LatticeData) := Matrix (Fin D.rank) (Fin D.rank) ℂ

private theorem pderiv_conformalPolynomial (D : LatticeData) (A : CurrentMatrix D)
    (hA : A.IsSymm) (i : Fin D.rank) :
    pderiv (i, 0) (conformalPolynomial D A) =
      ∑ j : Fin D.rank, A i j • (X (j, 0) : Oscillator D) := by
  classical
  simp only [conformalPolynomial, Derivation.map_smul, map_sum, pderiv_mul, pderiv_X,
    Pi.single_apply, Prod.mk.injEq, and_true, ite_mul, mul_ite, one_mul, mul_one,
    zero_mul, mul_zero, smul_add, smul_ite, smul_zero, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j k : Fin D.rank =>
    if j = i then A j k • (X (k, 0) : Oscillator D) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hTranspose : (∑ j, A j i • (X (j, 0) : Oscillator D)) =
      ∑ j, A i j • (X (j, 0) : Oscillator D) :=
    Finset.sum_congr rfl fun j _ => by rw [hA.apply i j]
  rw [hTranspose, ← smul_add, ← two_smul ℂ, smul_smul,
    inv_mul_cancel₀ (by norm_num), one_smul]

/-- Two derivatives recover each symmetric matrix entry, including the diagonal. -/
theorem omega_injective_of_isSymm (D : LatticeData) {A B : CurrentMatrix D}
    (hA : A.IsSymm) (hB : B.IsSymm) (h : omega D A = omega D B) : A = B := by
  classical
  have hpoly : conformalPolynomial D A = conformalPolynomial D B := by
    simpa only [omega, Finsupp.single_eq_same] using congrArg (fun v : Carrier D => v 0) h
  ext i j
  have hd := congrArg (fun p : Oscillator D => constantCoeff (pderiv (j, 0) (pderiv (i, 0) p)))
    hpoly
  simp only [pderiv_conformalPolynomial D _ hA, pderiv_conformalPolynomial D _ hB,
    map_sum, Derivation.map_smul, pderiv_X, Pi.single_apply, Prod.mk.injEq,
    and_true, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hd
  simpa only [Algebra.smul_def, mul_one, algebraMap_eq, constantCoeff_C] using hd

private theorem omega_smul (D : LatticeData) (z : ℂ) (A : CurrentMatrix D) :
    omega D (z • A) = z • omega D A := by
  classical
  unfold omega conformalPolynomial
  rw [Finsupp.smul_single, smul_comm z (2 : ℂ)⁻¹]
  simp only [Matrix.smul_apply, Finset.smul_sum, smul_assoc]

private theorem polynomial_of_variables (D : LatticeData) (A : CurrentMatrix D)
    (x : Fin D.rank → Oscillator D) :
    (2 : ℂ)⁻¹ • (∑ i, ∑ j, A i j • (x i * x j)) =
      (2 : ℂ)⁻¹ • (x ⬝ᵥ (A.map (C : ℂ →+* Oscillator D)) *ᵥ x) := by
  rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, algebraMap_eq, Matrix.map_apply]
  ac_rfl

/-- Substitution of the weight-one variables transports the quadratic matrix
by congruence. The algebra map can act arbitrarily on the higher variables. -/
theorem conformalPolynomial_substitution (D : LatticeData) (A M : CurrentMatrix D)
    (S : Oscillator D →ₐ[ℂ] Oscillator D)
    (hS : ∀ i : Fin D.rank, S (X (i, 0)) =
      ∑ k : Fin D.rank, M k i • X (k, 0)) :
    S (conformalPolynomial D A) = conformalPolynomial D (M * A * Mᵀ) := by
  classical
  let x (i : Fin D.rank) : Oscillator D := X (i, 0)
  let c : ℂ →+* Oscillator D := C
  have hx (i : Fin D.rank) : (∑ k, M k i • x k) = (x ᵥ* M.map c) i := by
    simp only [vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def, algebraMap_eq, c]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [conformalPolynomial, map_smul, map_sum, map_mul, hS]
  change (2 : ℂ)⁻¹ • (∑ i, ∑ j, A i j •
    ((∑ k, M k i • x k) * (∑ k, M k j • x k))) =
      (2 : ℂ)⁻¹ • ∑ i, ∑ j, (M * A * Mᵀ) i j • (x i * x j)
  simp_rw [hx]
  rw [polynomial_of_variables, polynomial_of_variables]
  congr 1
  rw [mulVec_vecMul, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc, c]

/-- Every vacuum-preserving lift with the specified neutral oscillator action
has the same effect on quadratic states, regardless of its charge phases. -/
theorem omega_covariance (D : LatticeData) (A M : CurrentMatrix D)
    (S : Oscillator D →ₐ[ℂ] Oscillator D) (U : Module.End ℂ (Carrier D))
    (hS : ∀ i : Fin D.rank, S (X (i, 0)) =
      ∑ k : Fin D.rank, M k i • X (k, 0))
    (z : ℂ) (hU : ∀ p : Oscillator D, U (Finsupp.single 0 p) = z • Finsupp.single 0 (S p))
    (hVacuum : U (vacuum D) = vacuum D) :
    U (omega D A) = omega D (M * A * Mᵀ) := by
  have hz : z = 1 := by
    apply smul_left_injective ℂ (vacuum_nonzero D)
    simpa only [vacuum, hU, map_one, one_smul] using hVacuum
  rw [omega, hU, hz, one_smul, conformalPolynomial_substitution D A M S hS]
  rfl

/-- The mixing matrix of the actual oscillator substitution acts by congruence. -/
theorem lift_omega (D : LatticeData) (g : Charge D ≃+ Charge D) (A : CurrentMatrix D) :
    lift D g (omega D A) = omega D (mixingMatrix D g * A * (mixingMatrix D g)ᵀ) := by
  refine omega_covariance D A (mixingMatrix D g) (oscillator D g).toAlgHom
    (lift D g).toLinearMap (fun i => oscillator_X D g (i, 0)) (phase D g 0)
    ?_ (lift_vacuum D g)
  intro p
  change lift D g (Finsupp.single 0 p) = _ • Finsupp.single 0 (oscillator D g p)
  rw [lift_single, map_zero]

/-- Every quadratic state uses exactly two frequency-one oscillators in charge zero. -/
theorem omega_mem_grade_two (D : LatticeData) (A : CurrentMatrix D) :
    omega D A ∈ grade D 2 := by
  classical
  simp only [omega, conformalPolynomial, ← Finsupp.smul_single, Finsupp.single_finsetSum]
  refine (grade D 2).smul_mem _ ((grade D 2).sum_mem fun i _ =>
    (grade D 2).sum_mem fun j _ => (grade D 2).smul_mem _ ?_)
  rw [mem_grade_iff]
  rintro ⟨a, d⟩ hd
  have hdegree : energy D (0, Finsupp.single ((i, 0) : Index D) 1 +
      Finsupp.single (j, 0) 1) = 2 := by
    simp [energy, oscillatorEnergy, map_add, Finsupp.weight_single]
  have hX : (X (i, 0) * X (j, 0) : Oscillator D) =
      monomial (Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1) 1 := by
    simp only [MvPolynomial.X, monomial_mul_monomial, mul_one]
  by_cases ha : a = 0
  · subst a
    have hne : Finsupp.single ((i, 0) : Index D) 1 + Finsupp.single (j, 0) 1 ≠ d :=
      fun h => hd (h ▸ hdegree)
    simp [hX, coeff_monomial, hne]
  · simp [Finsupp.single_eq_of_ne ha]

private theorem mixing_gram (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) :
    (mixingMatrix D g)ᵀ * gramComplex D * mixingMatrix D g = gramComplex D := by
  classical
  ext i j
  have h := congrArg (fun n : ℤ => (n : ℂ)) (hg (unitCharge D i) (unitCharge D j))
  simp only [bilinear, Int.cast_sum, Int.cast_mul] at h
  simp only [Matrix.mul_apply, Finset.sum_mul, mixingMatrix, transpose_apply]
  rw [Finset.sum_comm]
  simpa [gramComplex,
    unitCharge, apply_ite, mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul] using h

private theorem inverse_gram_covariance (D : LatticeData) (H : CurrentMatrix D)
    (hHG : H * gramComplex D = 1) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b) :
    mixingMatrix D g * H * (mixingMatrix D g)ᵀ = H := by
  classical
  let M := mixingMatrix D g
  let N := mixingMatrix D g.symm
  have hMN : M * N = 1 := mixing_inverse D g g.symm g.apply_symm_apply
  have h := congrArg (fun B : CurrentMatrix D => B * N) (mixing_gram D g hg)
  have hMG : Mᵀ * gramComplex D = gramComplex D * N := by
    change (Mᵀ * gramComplex D * M) * N = gramComplex D * N at h
    simpa only [Matrix.mul_assoc, hMN, Matrix.mul_one] using h
  have hGH := mul_eq_one_comm.mp hHG
  apply Matrix.mul_left_injective_of_inv (gramComplex D) H hGH
  change M * H * Mᵀ * gramComplex D = H * gramComplex D
  rw [Matrix.mul_assoc (M * H), hMG, ← Matrix.mul_assoc,
    Matrix.mul_assoc M H, hHG, Matrix.mul_one, hMN]

/-- A nonzero proper Gram-orthogonal projector commuting with the charge action
produces a second fixed vector in the actual weight-two space. -/
theorem projector_fixed_weight_two (D : LatticeData) {ι : Type*}
    (g : ι → Charge D ≃+ Charge D)
    (hg : ∀ t a b, bilinear D (g t a) (g t b) = bilinear D a b)
    (H P : CurrentMatrix D) (hH : H.IsSymm) (hHG : H * gramComplex D = 1)
    (hP : P * P = P) (hP₀ : P ≠ 0) (hP₁ : P ≠ 1)
    (hSelf : Pᵀ * gramComplex D = gramComplex D * P)
    (hComm : ∀ t, Commute (mixingMatrix D (g t)) P) :
    omega D H ∈ grade D 2 ∧ omega D (P * H) ∈ grade D 2 ∧
      ((Y D (omega D H))[[1]]) (omega D H) = (2 : ℂ) • omega D H ∧
      ((Y D (omega D H))[[1]]) (omega D (P * H)) = (2 : ℂ) • omega D (P * H) ∧
      (∀ t, lift D (g t) (omega D H) = omega D H ∧
        lift D (g t) (omega D (P * H)) = omega D (P * H)) ∧
      LinearIndependent ℂ ![omega D (P * H), omega D H] := by
  classical
  have hGH := mul_eq_one_comm.mp hHG
  have hPH : (P * H).IsSymm := by
    change (P * H)ᵀ = P * H
    rw [Matrix.transpose_mul, hH.eq]
    calc
      H * Pᵀ = H * (Pᵀ * gramComplex D) * H := by
        rw [Matrix.mul_assoc H, Matrix.mul_assoc Pᵀ, hGH, Matrix.mul_one]
      _ = P * H := by rw [hSelf, ← Matrix.mul_assoc H, hHG, Matrix.one_mul]
  have hGradeH := omega_mem_grade_two D H
  have hGradePH := omega_mem_grade_two D (P * H)
  have hEigen (v : Carrier D) (hv : v ∈ grade D 2) :
      ((Y D (omega D H))[[1]]) v = (2 : ℂ) • v := by
    rw [show (1 : ℤ) = 0 + 1 by rfl, omega_modes]
    simpa only [Int.cast_ofNat] using
      (actualL0_eigen_iff_grade D H hHG hGH 2 v).mpr hv
  refine ⟨hGradeH, hGradePH, hEigen _ hGradeH, hEigen _ hGradePH, ?_, ?_⟩
  · intro t
    have hInv := inverse_gram_covariance D H hHG (g t) (hg t)
    refine ⟨by rw [lift_omega, hInv], ?_⟩
    rw [lift_omega, ← Matrix.mul_assoc _ P H, (hComm t).eq,
      Matrix.mul_assoc P, Matrix.mul_assoc P, hInv]
  · rw [linearIndependent_fin2]
    change omega D H ≠ 0 ∧ ∀ c : ℂ, c • omega D H ≠ omega D (P * H)
    constructor
    · intro hzero
      have hHzero : H = 0 := omega_injective_of_isSymm D hH
        (Matrix.isSymm_zero) (by simpa [omega, conformalPolynomial] using hzero)
      have hone : (1 : CurrentMatrix D) = 0 := by simpa [hHzero] using hHG.symm
      exact hP₀ (by rw [← Matrix.mul_one P, hone, Matrix.mul_zero])
    · intro c hc
      rw [← omega_smul] at hc
      have hscalar : c • (1 : CurrentMatrix D) = P := by
        have h := omega_injective_of_isSymm D (hH.smul c) hPH hc
        simpa only [Matrix.smul_mul, Matrix.mul_assoc, hHG, Matrix.mul_one] using
          congrArg (fun B : CurrentMatrix D => B * gramComplex D) h
      have hcP : c • P = P := by
        calc
          c • P = (c • (1 : CurrentMatrix D)) * P := by rw [Matrix.smul_mul, Matrix.one_mul]
          _ = P := by rw [hscalar, hP]
      have hc1 : c = 1 := smul_left_injective ℂ hP₀ (hcP.trans (one_smul ℂ P).symm)
      exact hP₁ (by simpa [hc1] using hscalar.symm)

#print axioms omega_injective_of_isSymm
#print axioms conformalPolynomial_substitution
#print axioms omega_covariance
#print axioms lift_omega
#print axioms omega_mem_grade_two
#print axioms projector_fixed_weight_two
#check @projector_fixed_weight_two

end
end D5.S3.VertexAlgebra.Lattice.InvariantQuadraticConformalState
