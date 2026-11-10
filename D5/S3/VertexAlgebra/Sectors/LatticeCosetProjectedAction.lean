/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetProjectedAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite transverse polynomial substitution for all native source fields. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation

/-! The native Schur commutator determines the projected action on every
transverse target polynomial. All coefficient sums here are polynomial sums;
there is no interchange of unsupported infinite series. Field conventions are
those of Bakalov--Kac, math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetProjectedAction

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeCosetCompression LatticeCosetTransverse LatticeCosetSeparation
open LatticeCosetFieldSeparation LatticeDiscriminantTheta MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private multiply_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetSeparation
open private projection_single from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

/-- A finite polynomial in inverse field powers acts by integer mode shifts. -/
def polynomialMode {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : ℤ → V) (m : ℤ) : Polynomial ℂ →ₗ[ℂ] V :=
  (Finsupp.linearCombination ℂ (fun j : ℕ => A (m-j))).comp
    ((AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap.comp
      (Polynomial.toFinsuppIsoLinear ℂ).toLinearMap)

private theorem polynomialMode_monomial {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : ℤ → V) (m : ℤ) (j : ℕ) (z : ℂ) :
    polynomialMode A m (Polynomial.monomial j z) = z • A (m-j) := by
  simp [polynomialMode, Polynomial.toFinsupp_monomial]

private theorem polynomialMode_C_mul {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : ℤ → V) (m : ℤ) (z : ℂ) (q : Polynomial ℂ) :
    polynomialMode A m (Polynomial.C z * q) = z • polynomialMode A m q := by
  rw [← Polynomial.smul_eq_C_mul]
  exact map_smul _ _ _

private theorem polynomialMode_X_pow {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : ℤ → V) (m : ℤ) (r : ℕ) (q : Polynomial ℂ) :
    polynomialMode A m (Polynomial.X^r * q) = polynomialMode A (m-r) q := by
  induction q using Polynomial.induction_on' with
  | add q q' h h' => simp only [mul_add, map_add, h, h']
  | monomial d z =>
    rw [Polynomial.X_pow_mul_monomial, polynomialMode_monomial, polynomialMode_monomial]
    congr 2
    push_cast
    omega

private theorem multiply_mul (F : LatticeData) (s t : Oscillator F) (v : Carrier F) :
    multiply F (s*t) v = multiply F s (multiply F t v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n p => simp only [multiply_single, mul_assoc]

private theorem multiply_add (F : LatticeData) (s t : Oscillator F) (v : Carrier F) :
    multiply F (s+t) v = multiply F s v + multiply F t v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]; abel
  | single n p => simp [multiply_single, add_mul, Finsupp.single_add]

private theorem multiply_C (F : LatticeData) (z : ℂ) (v : Carrier F) :
    multiply F (MvPolynomial.C z) v = z • v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, smul_add]
  | single n p => simp [multiply_single, MvPolynomial.C_mul', Finsupp.smul_single]

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ) (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

/-- Evaluate the transverse polynomial at the negative Schur shifts. -/
def scalarTranslation (a : Fin e → ℤ) :
    MvPolynomial (Fin e × ℕ) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval (fun x : Fin e × ℕ =>
    -Polynomial.C (transversePair D B C a x.1 : ℂ) * Polynomial.X^(x.2+1))

private theorem projection_transverse_mul (d : Fin e → ℤ) (j : Fin e) (k : ℕ)
    (v : Carrier (ambient D e B C hC hCe)) :
    projection D B C hC hCe d (multiply _ (transverse D B C hC hCe j k) v) = 0 := by
  have ht : polynomialProjection D B C hC hCe (transverse D B C hC hCe j k) = 0 := by
    simp [polynomialProjection, transverse, projectionVariable]
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]
  | single n f =>
    rw [multiply_single, projection_single]
    split_ifs <;> simp [map_mul, ht]

/-- The complete native source acts on every transverse target polynomial by
the finite Schur substitution after longitudinal projection. The ambient
target state and the selected output sector are unrestricted. -/
theorem projected_transverse_polynomial (hD : (gramReal D).PosDef)
    (a d : Fin e → ℤ) (u : Carrier D) (h : MvPolynomial (Fin e × ℕ) ℂ) (m : ℤ)
    (v : Carrier (ambient D e B C hC hCe)) :
    projection D B C hC hCe d
        (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[m]])
          (multiply _ (transversePolynomial D B C hC hCe h) v)) =
      polynomialMode (fun t => projection D B C hC hCe d
        (((Y (ambient D e B C hC hCe) (injection D B C hC hCe a u))[[t]]) v)) m
          (scalarTranslation D B C a h) := by
  induction h using MvPolynomial.induction_on generalizing m v with
  | C z =>
    simp only [transversePolynomial, aeval_C, scalarTranslation]
    simp only [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self]
    rw [multiply_C, map_smul, map_smul]
    change z • _ = polynomialMode _ m (Polynomial.monomial 0 z)
    rw [polynomialMode_monomial]
    simp
  | add f g hf hg =>
    simp only [map_add, multiply_add, hf, hg]
  | mul_X f x hf =>
    have hx : multiply _ (transversePolynomial D B C hC hCe (f * X x)) v =
        multiply _ (transverse D B C hC hCe x.1 x.2)
          (multiply _ (transversePolynomial D B C hC hCe f) v) := by
      rw [map_mul]
      simp only [transversePolynomial, aeval_X]
      rw [mul_comm, multiply_mul]
    rw [hx, field_transverse_commutator D B C hC hCe hD,
      map_sub, map_smul, projection_transverse_mul, zero_sub, hf]
    simp only [map_mul, scalarTranslation, aeval_X]
    rw [mul_comm _ (-Polynomial.C _ * _), mul_assoc, neg_mul, map_neg,
      polynomialMode_C_mul, polynomialMode_X_pow]

end
end D5.S3.VertexAlgebra.LatticeCosetProjectedAction
