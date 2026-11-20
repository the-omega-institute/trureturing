/- GID: D5/S3/Quantum/Recovery/BKMRelativeDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMRelativeDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative Loewner bounds for the BKM power integral. -/

import D5.S3.Quantum.Matrix.SpectralPower
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-! # Relative Loewner bounds for the BKM power integral -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open D5.S3.Quantum.Matrix.SpectralPower (mpow)

namespace D5.S3.Quantum.Recovery.BKMRelativeDensity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual logarithmic-mean Bochner integral. -/
def omega (a X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ t : ℝ in 0..1, mpow a t * X * mpow a (1 - t)

private abbrev basisChange (U : Matrix.unitaryGroup n ℂ) :=
  (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U).toAlgEquiv

private def diagReal (p : n → ℝ) : Matrix n n ℂ :=
  diagonal fun k => (p k : ℂ)

private def diagRealCLM : (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  ((Matrix.diagonalLinearMap n ℝ ℂ).toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun k => Complex.ofRealCLM.comp (ContinuousLinearMap.proj k))

private theorem conjugated_cfc (a : Matrix n n ℂ) (ha : a.PosDef) (f : ℝ → ℝ) :
    (basisChange ha.isHermitian.eigenvectorUnitary).symm (cfc f a) =
      diagReal (f ∘ ha.isHermitian.eigenvalues) := by
  rw [ha.isHermitian.cfc_eq]
  exact (basisChange ha.isHermitian.eigenvectorUnitary).symm_apply_apply _

theorem continuous_mpow (a : Matrix n n ℂ) (ha : a.PosDef) :
    Continuous (fun t : ℝ => mpow a t) := by
  have he (t : ℝ) : mpow a t = basisChange ha.isHermitian.eigenvectorUnitary
      (diagReal fun k => Real.exp (t * Real.log (ha.isHermitian.eigenvalues k))) := by
    apply (basisChange ha.isHermitian.eigenvectorUnitary).symm.injective
    rw [AlgEquiv.symm_apply_apply, mpow, conjugated_cfc a ha]
    congr 1
    funext k
    simp [Real.rpow_def_of_pos (ha.eigenvalues_pos k), mul_comm]
  simp_rw [he]
  apply (basisChange ha.isHermitian.eigenvectorUnitary).toLinearEquiv.toContinuousLinearEquiv.continuous.comp
  change Continuous (fun t : ℝ => diagRealCLM (fun k => Real.exp
    (t * Real.log (ha.isHermitian.eigenvalues k))))
  fun_prop

private theorem mpow_eq_rpow {a : Matrix n n ℂ} (ha : 0 ≤ a) (t : ℝ) :
    mpow a t = a ^ t :=
  (CFC.rpow_eq_cfc_real ha).symm

theorem mpow_smul_of_nonneg {b : Matrix n n ℂ} (hb : 0 ≤ b)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    mpow (c • b) t = c ^ t • mpow b t := by
  have hcont := Real.continuous_rpow_const ht
  rw [mpow, mpow, ← cfc_comp_smul c (fun x : ℝ => x ^ t) b hcont.continuousOn
    (hb.posSemidef.isHermitian.isSelfAdjoint), ← cfc_smul (c ^ t) (fun x : ℝ => x ^ t) b
    hcont.continuousOn]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow hc (spectrum_nonneg_of_nonneg hb hx)

private theorem mpow_le_mpow {a b : Matrix n n ℂ} (ha : 0 ≤ a) (hab : a ≤ b)
    {t : ℝ} (ht : t ∈ Icc 0 1) : mpow a t ≤ mpow b t := by
  rw [mpow_eq_rpow ha, mpow_eq_rpow (ha.trans hab)]
  exact CFC.monotone_rpow ht hab

/-- Fractional powers preserve the relative bounds with powered constants. -/
private theorem mpow_relative_bounds {a b : Matrix n n ℂ} (ha : a.PosDef) (hb : b.PosDef)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hℓu : ℓ ≤ u)
    (hlo : ℓ • b ≤ a) (hhi : a ≤ u • b) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ℓ ^ t • mpow b t ≤ mpow a t ∧ mpow a t ≤ u ^ t • mpow b t := by
  have hbn := hb.posSemidef.nonneg
  rw [← mpow_smul_of_nonneg hbn hℓ.le ht.1,
    ← mpow_smul_of_nonneg hbn (hℓ.le.trans hℓu) ht.1]
  exact ⟨mpow_le_mpow (smul_nonneg hℓ.le hbn) hlo ht,
    mpow_le_mpow ha.posSemidef.nonneg hhi ht⟩

omit [Fintype n] [DecidableEq n] in
private theorem transpose_mono {A B : Matrix n n ℂ} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  rw [Matrix.le_iff, ← Matrix.transpose_sub]
  exact (Matrix.le_iff.mp h).transpose

omit [Fintype n] [DecidableEq n] in
private theorem kronecker_mono [Finite n] {A B C D : Matrix n n ℂ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hAB : A ≤ B) (hCD : C ≤ D) :
    A ⊗ₖ C ≤ B ⊗ₖ D := by
  let := Fintype.ofFinite n
  apply Matrix.le_iff.mpr
  have h₁ := (Matrix.le_iff.mp hAB).kronecker ((hC.trans hCD).posSemidef)
  have h₂ := hA.posSemidef.kronecker (Matrix.le_iff.mp hCD)
  convert h₁.add h₂ using 1
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kronecker_apply]
  ring

/-- The coefficient of left and right multiplication in column vectorization. -/
def powerCoefficient (a : Matrix n n ℂ) (t : ℝ) : Matrix (n × n) (n × n) ℂ :=
  (mpow a (1 - t))ᵀ ⊗ₖ mpow a t

private theorem powerCoefficient_mulVec (a X : Matrix n n ℂ) (t : ℝ) :
    powerCoefficient a t *ᵥ vec X = vec (mpow a t * X * mpow a (1 - t)) := by
  rw [powerCoefficient, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose]

private theorem scaled_powerCoefficient (b : Matrix n n ℂ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ((c ^ (1 - t) • mpow b (1 - t))ᵀ ⊗ₖ (c ^ t • mpow b t)) =
      c • powerCoefficient b t := by
  have hc_exp : c ^ (1 - t) * c ^ t = c := by
    rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
  rw [Matrix.transpose_smul, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul, hc_exp, powerCoefficient]

/-- The complementary exponents yield the original relative constants in the tensor order. -/
private theorem powerCoefficient_relative_bounds {a b : Matrix n n ℂ} (ha : a.PosDef)
    (hb : b.PosDef) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hℓu : ℓ ≤ u)
    (hlo : ℓ • b ≤ a) (hhi : a ≤ u • b) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ℓ • powerCoefficient b t ≤ powerCoefficient a t ∧
      powerCoefficient a t ≤ u • powerCoefficient b t := by
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  obtain ⟨hl, hu⟩ := mpow_relative_bounds ha hb hℓ hℓu hlo hhi ht
  obtain ⟨hl', hu'⟩ := mpow_relative_bounds ha hb hℓ hℓu hlo hhi ht'
  have hmp (x : Matrix n n ℂ) (hx : x.PosDef) (s : ℝ) : 0 ≤ mpow x s := by
    rw [mpow_eq_rpow hx.posSemidef.nonneg]
    exact CFC.rpow_nonneg
  have htrans (M : Matrix n n ℂ) (hM : 0 ≤ M) : 0 ≤ Mᵀ :=
    hM.posSemidef.transpose.nonneg
  constructor
  · rw [← scaled_powerCoefficient b hℓ t]
    exact kronecker_mono
      (htrans _ (smul_nonneg (Real.rpow_nonneg hℓ.le _) (hmp b hb _)))
      (smul_nonneg (Real.rpow_nonneg hℓ.le _) (hmp b hb _))
      (transpose_mono hl') hl
  · rw [← scaled_powerCoefficient b (hℓ.trans_le hℓu) t]
    exact kronecker_mono (htrans _ (hmp a ha _)) (hmp a ha _) (transpose_mono hu') hu

private theorem continuous_powerCoefficient (a : Matrix n n ℂ) (ha : a.PosDef) :
    Continuous (powerCoefficient a) := by
  have h := continuous_mpow a ha
  have h' := h.comp ((continuous_const (y := (1 : ℝ))).sub continuous_id)
  apply continuous_matrix
  rintro ⟨i, k⟩ ⟨j, l⟩
  exact (h'.matrix_elem j i).mul (h.matrix_elem k l)

/-- Bochner integral of the coefficients for the actual BKM power integral. -/
def omegaCoefficient (a : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  ∫ t : ℝ in 0..1, powerCoefficient a t

/-- The integrated coefficient acts by `omega` under column vectorization. -/
theorem omegaCoefficient_mulVec (a X : Matrix n n ℂ) (ha : a.PosDef) :
    omegaCoefficient a *ᵥ vec X = vec (omega a X) := by
  let eval : Matrix (n × n) (n × n) ℂ →ₗ[ℂ] ((n × n) → ℂ) :=
    { toFun := fun A => A *ᵥ vec X
      map_add' := fun A B => Matrix.add_mulVec A B _
      map_smul' := fun c A => Matrix.smul_mulVec c A _ }
  let vectorize : Matrix n n ℂ →ₗ[ℂ] ((n × n) → ℂ) :=
    { toFun := vec
      map_add' := Matrix.vec_add
      map_smul' := Matrix.vec_smul }
  let E := eval.toContinuousLinearMap
  let V := vectorize.toContinuousLinearMap
  have hk := (continuous_powerCoefficient a ha).intervalIntegrable (μ := volume) 0 1
  have hp : IntervalIntegrable (fun t : ℝ => mpow a t * X * mpow a (1 - t)) volume 0 1 :=
    have ht : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
    (((continuous_mpow a ha).mul (continuous_const (y := X))).mul
      ((continuous_mpow a ha).comp ht)).intervalIntegrable 0 1
  change E (∫ t : ℝ in 0..1, powerCoefficient a t) =
    V (∫ t : ℝ in 0..1, mpow a t * X * mpow a (1 - t))
  rw [← E.intervalIntegral_comp_comm hk, ← V.intervalIntegral_comp_comm hp]
  simp only [E, V]
  exact congrArg (fun f : ℝ → (n × n) → ℂ => ∫ t : ℝ in 0..1, f t)
    (funext (powerCoefficient_mulVec a X))

/-- Loewner comparison for the coefficient of the actual BKM power integral. -/
theorem omegaCoefficient_relative_bounds {a b : Matrix n n ℂ} (ha : a.PosDef)
    (hb : b.PosDef) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hℓu : ℓ ≤ u)
    (hlo : ℓ • b ≤ a) (hhi : a ≤ u • b) :
    ℓ • omegaCoefficient b ≤ omegaCoefficient a ∧
      omegaCoefficient a ≤ u • omegaCoefficient b := by
  let : IsOrderedModule ℝ (Matrix (n × n) (n × n) ℂ) :=
    IsOrderedModule.of_smul_nonneg (fun c hc M hM => (hM.posSemidef.smul hc).nonneg)
  have h₀₁ : (0 : ℝ) ≤ 1 := zero_le_one
  have ha' := continuous_powerCoefficient a ha
  have hb' := continuous_powerCoefficient b hb
  have hA := (ha'.intervalIntegrable (μ := volume) 0 1).1
  have hscaled (c : ℝ) :
      Integrable (fun t => c • powerCoefficient b t) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hb'.const_smul c |>.intervalIntegrable (μ := volume) 0 1).1
  have hpoint :
      ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        ℓ • powerCoefficient b t ≤ powerCoefficient a t ∧
          powerCoefficient a t ≤ u • powerCoefficient b t :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ ht =>
      powerCoefficient_relative_bounds ha hb hℓ hℓu hlo hhi (Ioc_subset_Icc_self ht)
  have hlow := MeasureTheory.integral_mono_ae (hscaled ℓ) hA (hpoint.mono fun _ ht => ht.1)
  have hhigh := MeasureTheory.integral_mono_ae hA (hscaled u) (hpoint.mono fun _ ht => ht.2)
  rw [MeasureTheory.integral_smul] at hlow hhigh
  simpa only [omegaCoefficient, intervalIntegral.integral_of_le h₀₁] using And.intro hlow hhigh


end D5.S3.Quantum.Recovery.BKMRelativeDensity
