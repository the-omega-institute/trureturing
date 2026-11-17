/- GID: D5/S3/QuadraticForms/ParriloHierarchy
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ParriloHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full native polynomial SOS hierarchy of copositive matrices. -/

import D5.S3.QuadraticForms.HomogeneousSOSGram

/-! This is the full hierarchy K_n^k, for every k, defined by the native
unrestricted real polynomial SOS predicate. It is not the zeroth conic
GDNN approximation. The GNP extension characterization is a separate
mathematical obligation. -/

open scoped BigOperators
open MvPolynomial Matrix

namespace D5.S3.QuadraticForms.ParriloHierarchy

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The homogeneous form before substitution of the squared variables. -/
def liftedForm (k : ℕ) (M : Matrix L L ℝ) : MvPolynomial L ℝ :=
  (∑ i : L, X i) ^ k * ∑ i, ∑ j, C (M i j) * X i * X j

/-- The exact Parrilo polynomial, obtained by the substitution X_i to X_i². -/
def polynomial (k : ℕ) (M : Matrix L L ℝ) : MvPolynomial L ℝ :=
  expand 2 (liftedForm k M)

/-- The full hierarchy of real symmetric matrices whose actual Parrilo
polynomial is a native sum of squares. No trace normalization is imposed. -/
def K (k : ℕ) : Set (Matrix L L ℝ) :=
  {M | M.IsSymm ∧ IsSumSq (polynomial k M)}

private lemma liftedForm_homogeneous (k : ℕ) (M : Matrix L L ℝ) :
    (liftedForm k M).IsHomogeneous (k + 2) := by
  apply IsHomogeneous.mul
  · simpa only [one_mul] using
      (IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X ℝ i)).pow k
  · apply IsHomogeneous.sum
    intro i hi
    apply IsHomogeneous.sum
    intro j hj
    simpa only [zero_add] using
      ((isHomogeneous_C L (M i j)).mul (isHomogeneous_X ℝ i)).mul
        (isHomogeneous_X ℝ j)

open private expand_homogeneous from D5.S3.QuadraticForms.HomogeneousSOS
open private homogeneous_eq_form from D5.S3.QuadraticForms.HomogeneousSOSGram

private lemma polynomial_homogeneous (k : ℕ) (M : Matrix L L ℝ) :
    (polynomial k M).IsHomogeneous (2 * (k + 2)) :=
  expand_homogeneous _ _ (liftedForm_homogeneous k M)

/-- Every level of the genuine Parrilo SOS hierarchy is a closed cone of
real symmetric matrices. The native SOS condition is kept in the definition. -/
theorem K_closed (k : ℕ) : IsClosed (K (L := L) k) := by
  letI : NormedAddCommGroup (Matrix L L ℝ) :=
    inferInstanceAs (NormedAddCommGroup (L → L → ℝ))
  letI : NormedSpace ℝ (Matrix L L ℝ) :=
    inferInstanceAs (NormedSpace ℝ (L → L → ℝ))
  let f : Matrix L L ℝ →ₗ[ℝ]
      (HomogeneousSOSGram.Exponent L (2 * (k + 2)) → ℝ) := {
    toFun := fun M a => (polynomial k M).coeff a.val
    map_add' := by
      intro M N
      ext a
      have he : polynomial k (M + N) = polynomial k M + polynomial k N := by
        simp [polynomial,liftedForm,Matrix.add_apply,add_mul,mul_add,
          Finset.sum_add_distrib]
      exact congrArg (fun p : MvPolynomial L ℝ => p.coeff a.val) he
    map_smul' := by
      intro a M
      ext c
      have he : polynomial k (a • M) = a • polynomial k M := by
        simp [polynomial,liftedForm,Matrix.smul_apply,smul_eq_mul,
          MvPolynomial.smul_eq_C_mul,Finset.mul_sum,mul_assoc]
        ring
      exact congrArg (fun p : MvPolynomial L ℝ => p.coeff c.val) he }
  have hpoly (M : Matrix L L ℝ) : polynomial k M =
      HomogeneousSOSGram.form (2 * (k + 2)) (f M) :=
    homogeneous_eq_form _ _ (polynomial_homogeneous k M)
  have hsym : IsClosed {M : Matrix L L ℝ | M.IsSymm} :=
    isClosed_eq (by fun_prop) continuous_id
  have he : K (L := L) k = {M | M.IsSymm} ∩
      f ⁻¹' HomogeneousSOSGram.sosCoefficients (k + 2) := by
    ext M
    change (_ ∧ IsSumSq (polynomial k M)) ↔
      (_ ∧ IsSumSq (HomogeneousSOSGram.form (2 * (k + 2)) (f M)))
    simp only [hpoly,Set.mem_setOf_eq]
  rw [he]
  exact hsym.inter ((HomogeneousSOSGram.sosCoefficients_closed (k + 2)).preimage
    f.continuous_of_finiteDimensional)

#print axioms K_closed

end
end D5.S3.QuadraticForms.ParriloHierarchy
