/- GID: D5/S3/Quantum/Hiai/InverseMeanVariational
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/InverseMeanVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse-mean trace variational bound with its explicit nonselfadjoint optimizer. -/

import D5.S3.Quantum.Schatten.Holder
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery

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

private lemma norm_rpow_rowGram (A : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    schattenNorm A r ^ r = tracePower (r / 2) (A * Aᴴ) := by
  rw [norm_rpow_gram A hr,
    tracePower_eq_sum (Matrix.posSemidef_conjTranspose_mul_self A),
    tracePower_eq_sum (Matrix.posSemidef_self_mul_conjTranspose A)]
  have he := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues_eq_eigenvalues_iff
    (hB := Matrix.isHermitian_mul_conjTranspose_self A)
  rw [he.mpr (Matrix.charpoly_mul_comm Aᴴ A)]

private lemma holder_two_young (U V : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
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

/-- The inverse variational formula on the actual support, with the spectral
generalized inverse zero on the kernel. Unlike the SPD optimizer, this optimizer
may be singular. The kernel hypothesis is necessary for the universal bound. -/
theorem psd_variational_bound_and_attainment {X M : Matrix d d ℂ}
    (hX : X.PosSemidef) (hM : M.PosSemidef)
    (hker : ∀ x : d → ℂ, M *ᵥ x = 0 → X *ᵥ x = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ Z₀ : Matrix d d ℂ, Z₀ = M ^ (-1 : ℝ) * X ∧
      objective r X M Z₀ = tracePower r (X * M ^ (-1 : ℝ) * X) ∧
      ∀ Z : Matrix d d ℂ,
        objective r X M Z ≤ tracePower r (X * M ^ (-1 : ℝ) * X) := by
  let D := M ^ (-1 / 2 : ℝ)
  let S := M ^ (1 / 2 : ℝ)
  let G := M ^ (-1 : ℝ)
  let P := D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport M
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have hmul (f g : ℝ → ℝ) :
      cfc f M * cfc g M = cfc (fun x => f x * g x) M :=
    (cfc_mul f g M (hcont f) (hcont g)).symm
  have hpowers (a b : ℝ) :
      M ^ a * M ^ b = cfc (fun x : ℝ => x ^ a * x ^ b) M := by
    rw [CFC.rpow_eq_cfc_real hM.nonneg, CFC.rpow_eq_cfc_real hM.nonneg, hmul]
  have hspectrum (x : ℝ) (hx : x ∈ spectrum ℝ M) : 0 ≤ x := by
    rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hM.eigenvalues_nonneg i
  have hDS : D * S = P := by
    rw [hpowers]
    apply cfc_congr
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · have hp : 0 < x := lt_of_le_of_ne (hspectrum x hx) (Ne.symm h0)
      change x ^ (-1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = if x = 0 then 0 else 1
      rw [← Real.rpow_add hp]
      norm_num [P, D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport, h0]
  have hDD : D * D = G := by
    change M ^ (-1 / 2 : ℝ) * M ^ (-1 / 2 : ℝ) = M ^ (-1 : ℝ)
    rw [hpowers, CFC.rpow_eq_cfc_real hM.nonneg]
    apply cfc_congr
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · change x ^ (-1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = x ^ (-1 : ℝ)
      rw [← Real.rpow_add (lt_of_le_of_ne (hspectrum x hx) (Ne.symm h0))]
      norm_num
  have hSS : S * S = M := by
    calc
      _ = cfc (fun x : ℝ => x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) M := hpowers _ _
      _ = cfc (fun x : ℝ => x) M := by
        apply cfc_congr
        intro x hx
        by_cases h0 : x = 0
        · simp [h0]
        · change x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x
          rw [← Real.rpow_add (lt_of_le_of_ne (hspectrum x hx) (Ne.symm h0))]
          norm_num
      _ = M := cfc_id' ℝ M hM.isHermitian.isSelfAdjoint
  have hGM : G * M = P := by
    change M ^ (-1 : ℝ) * M = P
    conv_lhs => rhs; rw [← CFC.rpow_one M hM.nonneg]
    rw [hpowers]
    apply cfc_congr
    intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · change x ^ (-1 : ℝ) * x ^ (1 : ℝ) = if x = 0 then 0 else 1
      rw [← Real.rpow_add (lt_of_le_of_ne (hspectrum x hx) (Ne.symm h0))]
      norm_num [P, D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport, h0]
  have hPG : P * G = G := by
    change P * M ^ (-1 : ℝ) = M ^ (-1 : ℝ)
    simp only [CFC.rpow_eq_cfc_real hM.nonneg]
    unfold P D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport
    rw [hmul]
    apply cfc_congr
    intro x hx
    by_cases h0 : x = 0 <;> simp [h0]
  have hMP : M * P = M := by
    rw [← cfc_id' ℝ M hM.isHermitian.isSelfAdjoint]
    unfold P D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport
    rw [hmul]
    apply cfc_congr
    intro x hx
    by_cases h0 : x = 0 <;> simp [h0]
  have hMzero : M * (1 - P) = 0 := by rw [mul_sub, mul_one, hMP, sub_self]
  have hXzero : X * (1 - P) = 0 := by
    ext i j
    have hm : M *ᵥ (fun k => (1 - P) k j) = 0 := by
      ext k
      change (M * (1 - P)) k j = 0
      rw [hMzero]
      rfl
    exact congrFun (hker _ hm) i
  have hXP : X * P = X := by
    exact (sub_eq_zero.mp (by simpa only [mul_sub, mul_one] using hXzero)).symm
  have hDstar : Dᴴ = D := (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hSstar : Sᴴ = S := (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hGstar : Gᴴ = G := (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hG : G.PosSemidef := CFC.rpow_nonneg.posSemidef
  have hR : (X * G * X).PosSemidef := by
    simpa only [hX.isHermitian.eq] using hG.mul_mul_conjTranspose_same X
  have hbound (Z : Matrix d d ℂ) :
      objective r X M Z ≤ tracePower r (X * G * X) := by
    let U := X * D
    let V := S * Z
    have hU : U * Uᴴ = X * G * X := by
      simp only [U, Matrix.conjTranspose_mul, hDstar, hX.isHermitian.eq,
        mul_assoc]
      rw [← mul_assoc D D X, hDD]
    have hV : Vᴴ * V = Zᴴ * M * Z := by
      simp only [V, Matrix.conjTranspose_mul, hSstar, mul_assoc]
      rw [← mul_assoc S S Z, hSS]
    have hUV : U * V = X * Z := by
      change X * D * (S * Z) = X * Z
      rw [← mul_assoc, mul_assoc X D S, hDS, hXP]
    have hgram : (X * Z)ᴴ * (X * Z) = Zᴴ * (X * X) * Z := by
      simp only [Matrix.conjTranspose_mul, hX.isHermitian.eq, mul_assoc]
    have hh := holder_two_young U V hr
    rw [hUV, norm_rpow_gram _ hr, hgram,
      norm_rpow_gram V (by positivity), norm_rpow_rowGram U (by positivity), hV, hU] at hh
    simpa only [show 2 * r / 2 = r by ring, objective] using hh
  refine ⟨G * X, rfl, ?_, hbound⟩
  have hGram : (G * X)ᴴ * M * (G * X) = X * G * X := by
    simp only [Matrix.conjTranspose_mul, hX.isHermitian.eq, hGstar, mul_assoc]
    rw [← mul_assoc G M (G * X), hGM, ← mul_assoc P G X, hPG]
  have hGramX : (G * X)ᴴ * (X * X) * (G * X) =
      (X * G * X) * (X * G * X) := by
    simp only [Matrix.conjTranspose_mul, hX.isHermitian.eq, hGstar, mul_assoc]
  have hSquare : tracePower (r / 2) ((X * G * X) * (X * G * X)) =
      tracePower r (X * G * X) := by
    unfold tracePower
    have hsquare : (X * G * X) * (X * G * X) = (X * G * X) ^ (2 : ℝ) := by
      simpa [pow_two] using (CFC.rpow_natCast (X * G * X) 2 hR.nonneg).symm
    rw [hsquare, CFC.rpow_rpow_of_exponent_nonneg _ _ _ (by norm_num)
      (by positivity) hR.nonneg]
    congr 2
    ring
  rw [objective, hGram, hGramX, hSquare]
  ring

#print axioms psd_variational_bound_and_attainment
end D5.S3.Quantum.Hiai.InverseMeanVariational
