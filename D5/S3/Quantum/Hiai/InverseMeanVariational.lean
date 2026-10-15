/- GID: D5/S3/Quantum/Hiai/InverseMeanVariational
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/InverseMeanVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse-mean trace variational bound with its explicit nonselfadjoint optimizer. -/

import D5.S3.Quantum.Schatten.Holder

noncomputable section
namespace D5.S3.Quantum.Hiai.InverseMeanVariational
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

-- Select spectral matrix powers rather than the inherited pointwise function power.
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- Real trace of the actual nonnegative spectral power. -/
def tracePower (r : ℝ) (A : Matrix d d ℂ) : ℝ := (Matrix.trace (A ^ r)).re

/-- The inverse-mean variational objective, with both adjoints retained. -/
def objective (r : ℝ) (X M Z : Matrix d d ℂ) : ℝ :=
  2 * tracePower (r / 2) (Zᴴ * (X * X) * Z) - tracePower r (Zᴴ * M * Z)

private lemma tracePower_eq_sum {A : Matrix d d ℂ} (hA : A.PosSemidef) (r : ℝ) :
    tracePower r A = ∑ i, (hA.isHermitian.eigenvalues i) ^ r := by
  rw [tracePower, CFC.rpow_eq_cfc_real hA.nonneg, hA.isHermitian.cfc_eq]
  simp [Matrix.IsHermitian.cfc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- Schatten powers are spectral traces of the column Gram matrix, including empty dimension. -/
lemma norm_rpow_gram (A : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    schattenNorm A r ^ r = tracePower (r / 2) (Aᴴ * A) := by
  rw [schattenNorm_rpow_eq_sum_singularValues A hr,
    tracePower_eq_sum (Matrix.posSemidef_conjTranspose_mul_self A)]
  apply Finset.sum_congr rfl
  intro i _
  unfold singularValues
  simp only [Matrix.conjTranspose_conjTranspose]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)]
  congr 1
  ring

/-- Schatten powers are spectral traces of the row Gram matrix, including empty dimension. -/
lemma norm_rpow_rowGram (A : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    schattenNorm A r ^ r = tracePower (r / 2) (A * Aᴴ) := by
  rw [norm_rpow_gram A hr,
    tracePower_eq_sum (Matrix.posSemidef_conjTranspose_mul_self A),
    tracePower_eq_sum (Matrix.posSemidef_self_mul_conjTranspose A)]
  have he := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues_eq_eigenvalues_iff
    (hB := Matrix.isHermitian_mul_conjTranspose_self A)
  rw [he.mpr (Matrix.charpoly_mul_comm Aᴴ A)]

/-- The two-factor Schatten Hölder bound followed by the quadratic Young inequality. -/
lemma holder_two_young (U V : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    2 * schattenNorm (U * V) r ^ r - schattenNorm V (2 * r) ^ (2 * r) ≤
      schattenNorm U (2 * r) ^ (2 * r) := by
  have hh := schattenNorm_mul_le U V hr (by positivity : 0 < 2 * r)
    (by positivity : 0 < 2 * r) (by field_simp; ring : 1 / r = 1 / (2 * r) + 1 / (2 * r))
  have hh' := Real.rpow_le_rpow (schattenNorm_nonneg (U * V) r) hh hr.le
  rw [Real.mul_rpow (schattenNorm_nonneg U _) (schattenNorm_nonneg V _)] at hh'
  have hp (a : ℝ) (ha : 0 ≤ a) : a ^ (2 * r) = (a ^ r) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    congr 1
    ring
  rw [hp _ (schattenNorm_nonneg U _), hp _ (schattenNorm_nonneg V _)]
  nlinarith [sq_nonneg (schattenNorm U (2 * r) ^ r - schattenNorm V (2 * r) ^ r)]

private lemma inverse_half_products {M : Matrix d d ℂ} (hM : M.PosDef) :
    (M ^ (-1 / 2 : ℝ)) * (M ^ (1 / 2 : ℝ)) = 1 ∧
    (M ^ (-1 / 2 : ℝ)) * (M ^ (-1 / 2 : ℝ)) = M⁻¹ := by
  constructor
  · convert CFC.rpow_neg_mul_rpow (a := M) (1 / 2 : ℝ) hM.isStrictlyPositive using 1 <;> congr 2 <;> ring
  · rw [← CFC.rpow_add hM.isUnit]
    norm_num
    exact ((Matrix.nonsing_inv_eq_ringInverse (A := M)).trans
      (CFC.inverse_eq_rpow_neg_one hM.isStrictlyPositive)).symm

private lemma inverse_trace_bound {X M : Matrix d d ℂ} (hX : X.PosDef) (hM : M.PosDef)
    {r : ℝ} (hr : 0 < r) (Z : Matrix d d ℂ) :
    objective r X M Z ≤ tracePower r (X * M⁻¹ * X) := by
  let U := X * (M ^ (-1 / 2 : ℝ))
  let V := (M ^ (1 / 2 : ℝ)) * Z
  have hhalf := inverse_half_products hM
  have hU : U * Uᴴ = X * M⁻¹ * X := by
    have hsa : IsSelfAdjoint ((M ^ (-1 / 2 : ℝ))) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have hstar : (M ^ (-1 / 2 : ℝ))ᴴ = M ^ (-1 / 2 : ℝ) := hsa.star_eq
    simp only [U, Matrix.conjTranspose_mul, hstar, hX.isHermitian.eq]
    simp only [mul_assoc]
    rw [← mul_assoc (M ^ _) (M ^ _) X, hhalf.2]
  have hV : Vᴴ * V = Zᴴ * M * Z := by
    have hsa : IsSelfAdjoint ((M ^ (1 / 2 : ℝ))) :=
      IsSelfAdjoint.of_nonneg CFC.rpow_nonneg
    have hsquare : (M ^ (1 / 2 : ℝ)) * (M ^ (1 / 2 : ℝ)) = M := by
      rw [← CFC.rpow_add hM.isUnit]
      norm_num
      exact CFC.rpow_one M hM.posSemidef.nonneg
    have hstar : (M ^ (1 / 2 : ℝ))ᴴ = M ^ (1 / 2 : ℝ) := hsa.star_eq
    simp only [V, Matrix.conjTranspose_mul, hstar]
    simp only [mul_assoc]
    rw [← mul_assoc (M ^ _) (M ^ _) Z, hsquare]
  have hUV : U * V = X * Z := by
    simp only [U, V, mul_assoc]
    rw [← mul_assoc (M ^ _) (M ^ _) Z, hhalf.1, one_mul]
  have hgram : (X * Z)ᴴ * (X * Z) = Zᴴ * (X * X) * Z := by
    simp [Matrix.conjTranspose_mul, hX.isHermitian.eq, mul_assoc]
  have hh := holder_two_young U V hr
  rw [hUV, norm_rpow_gram _ hr, hgram,
    norm_rpow_gram V (by positivity), norm_rpow_rowGram U (by positivity), hV, hU] at hh
  simpa only [show 2 * r / 2 = r by ring, objective] using hh

private lemma optimizer_gram {X M : Matrix d d ℂ} (hX : X.PosDef) (hM : M.PosDef) :
    (M⁻¹ * X)ᴴ * M * (M⁻¹ * X) = X * M⁻¹ * X ∧
    X * (M⁻¹ * X) = X * M⁻¹ * X := by
  letI := hM.isUnit.invertible
  constructor
  · simp [Matrix.conjTranspose_mul, hX.isHermitian.eq, hM.inv.isHermitian.eq,
      mul_assoc]
  · simp [mul_assoc]

private lemma tracePower_square {R : Matrix d d ℂ} (hR : R.PosDef) (r : ℝ) :
    tracePower (r / 2) (R * R) = tracePower r R := by
  unfold tracePower
  have hsq : R * R = (R ^ (2 : ℝ)) := by
    simpa [pow_two] using (CFC.rpow_natCast R 2 hR.posSemidef.nonneg).symm
  rw [hsq, CFC.rpow_rpow R 2 (r / 2) (by norm_num) hR.isStrictlyPositive]
  congr 2
  ring

/-- Every finite complex dimension admits the explicit invertible optimizer M inverse times X.
The optimizer need not be selfadjoint. The objective has the universal stated upper bound. -/
theorem variational_bound_and_attainment {X M : Matrix d d ℂ}
    (hX : X.PosDef) (hM : M.PosDef) {r : ℝ} (hr : 0 < r) :
    ∃ Z₀ : Matrix d d ℂ, IsUnit Z₀ ∧ Z₀ = M⁻¹ * X ∧
      objective r X M Z₀ = tracePower r (X * M⁻¹ * X) ∧
      ∀ Z : Matrix d d ℂ, objective r X M Z ≤ tracePower r (X * M⁻¹ * X) := by
  refine ⟨M⁻¹ * X, hM.inv.isUnit.mul hX.isUnit, rfl, ?_, inverse_trace_bound hX hM hr⟩
  have hR : (X * M⁻¹ * X).PosDef := by
    have h := hM.inv.mul_mul_conjTranspose_same (B := X)
      (Matrix.vecMul_injective_iff_isUnit.mpr hX.isUnit)
    simpa [hX.isHermitian.eq] using h
  have hg := optimizer_gram hX hM
  have hgram : (M⁻¹ * X)ᴴ * (X * X) * (M⁻¹ * X) =
      (X * M⁻¹ * X) * (X * M⁻¹ * X) := by
    simp [Matrix.conjTranspose_mul, hX.isHermitian.eq, hM.inv.isHermitian.eq, mul_assoc]
  rw [objective, hg.1, hgram, tracePower_square hR]
  ring

#print axioms variational_bound_and_attainment
end D5.S3.Quantum.Hiai.InverseMeanVariational
