/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sub-Gaussian tails for finite Hermitian sign matrices. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.FiniteSignMatrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- Interpret a fair bit as a symmetric sign. -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- The uniform measure on all assignments of the finitely many sign bits. -/
def signCubeMeasure (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  uniformOn Set.univ

instance signCubeMeasure_isProbabilityMeasure {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (signCubeMeasure ι) := by
  unfold signCubeMeasure
  infer_instance

theorem signCubeMeasure_eq_pi (ι : Type*) [Fintype ι] :
    signCubeMeasure ι = Measure.pi (fun _ : ι => uniformOn (Set.univ : Set Bool)) := by
  simpa only [signCubeMeasure, Set.pi_univ] using
    (uniformOn_pi (f := fun _ : ι => (Set.univ : Set Bool)))

/-- The real linear functional with coefficient vector `a` on the sign cube. -/
def signLinearForm {ι : Type*} [Fintype ι] (a : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∑ i, a i * signValue (ω i)

private theorem signBit_hasSubgaussianMGF :
    HasSubgaussianMGF signValue 1 (uniformOn (Set.univ : Set Bool)) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := signValue) (μ := uniformOn (Set.univ : Set Bool)) (a := -1) (b := 1) (measurable_of_countable signValue).aemeasurable
    (ae_of_all _ fun b => by cases b <;> norm_num [signValue, Set.mem_Icc])
    (by
      simp only [uniformOn, ProbabilityTheory.cond, Measure.restrict_univ,
        integral_smul_measure, integral_count, Fintype.sum_bool]
      simp [signValue])
  convert h using 1
  norm_num

/-- The moment generating function has variance proxy equal to the coefficient energy. -/
theorem signLinearForm_hasSubgaussianMGF {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasSubgaussianMGF (signLinearForm a) (∑ i, (‖a i‖₊ : ℝ≥0) ^ 2) (signCubeMeasure ι) := by
  rw [signCubeMeasure_eq_pi]
  let μ : ι → Measure Bool := fun _ => uniformOn Set.univ
  have h_indep : iIndepFun (fun i ω => a i * signValue (ω i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (measurable_of_countable (fun b => a i * signValue b)).aemeasurable)
  refine HasSubgaussianMGF.sum_of_iIndepFun h_indep (s := Finset.univ) (fun i _ => ?_)
  have h_eval := measurePreserving_eval μ i
  have h_map : HasSubgaussianMGF signValue 1
      ((Measure.pi μ).map (Function.eval i)) := by
    rw [h_eval.map_eq]
    exact signBit_hasSubgaussianMGF
  have h_bit := HasSubgaussianMGF.of_map h_eval.measurable.aemeasurable h_map
  convert h_bit.const_mul (a i) using 1
  · rfl
  · apply NNReal.eq
    change ((‖a i‖₊ ^ 2 : ℝ≥0) : ℝ) = (a i) ^ 2 * 1
    simp only [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs, mul_one]

private theorem subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
  rw [show {ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω} by
    ext ω
    exact (le_abs (a := t) (b := X ω))]
  calc
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add (hX.measure_ge_le ht) (hX.neg.measure_ge_le ht)

private theorem signLinearForm_hasSubgaussianMGF_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {c : ℝ≥0} (ha : ∑ i, a i ^ 2 ≤ (c : ℝ)) :
    HasSubgaussianMGF (signLinearForm a) c (signCubeMeasure ι) := by
  have hc : (∑ i, (‖a i‖₊ : ℝ≥0) ^ 2) ≤ c := by
    rw [← NNReal.coe_le_coe]
    simpa only [NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
      using ha
  have h := signLinearForm_hasSubgaussianMGF a
  exact ⟨h.integrable_exp_mul, fun s => (h.mgf_le s).trans (by gcongr)⟩

open _root_.Matrix

/-- Two independent bits for each ordered pair of matrix indices. -/
abbrev HermitianSignIndex (α : Type) := Bool × (α × α)

/-- Evaluate the existing sign matrix on a single assignment from the uniform cube. -/
def signCubeMatrix {α : Type} [LinearOrder α] [DecidableEq α]
    (ω : HermitianSignIndex α → Bool) : Matrix α α ℂ :=
  finiteSignMatrix (fun i j => ω (false, i, j)) (fun i j => ω (true, i, j))

/-- Evaluate the existing bipartite sample on the same uniform cube. -/
def signCubeSample {d : ℕ} (ω : HermitianSignIndex (Fin d × Fin d) → Bool) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  finiteSignSample (fun i j => ω (false, i, j)) (fun i j => ω (true, i, j))

/-- Select the real component for `false` and the imaginary component for `true`. -/
def signComponent (imag : Bool) (z : ℂ) : ℝ := if imag then z.im else z.re

private theorem signComponent_sum {ι : Type*} [Fintype ι] (imag : Bool) (f : ι → ℂ) :
    signComponent imag (∑ i, f i) = ∑ i, signComponent imag (f i) := by
  cases imag <;> simp [signComponent, Complex.re_sum, Complex.im_sum]

private def signPairWeight (imag : Bool) (a b : ℂ) (bit : Bool) : ℝ :=
  (3 / 5 : ℝ) * signComponent imag (if bit then Complex.I * (a - b) else a + b)

private theorem signScalar_re (ε η : Bool) : (signScalar ε η).re = (3 / 5 : ℝ) * signValue ε := by
  cases ε <;> cases η <;> norm_num [signScalar, signValue, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.normSq_apply]

private theorem signScalar_im (ε η : Bool) : (signScalar ε η).im = (3 / 5 : ℝ) * signValue η := by
  cases ε <;> cases η <;> norm_num [signScalar, signValue, Complex.mul_re, Complex.mul_im,
    Complex.div_im, Complex.normSq_apply]

private theorem signComponent_pair (imag : Bool) (a b : ℂ) (ε η : Bool) :
    signComponent imag (a * signScalar ε η + b * star (signScalar ε η)) =
      signPairWeight imag a b false * signValue ε +
        signPairWeight imag a b true * signValue η := by
  cases imag <;>
    simp [signComponent, signPairWeight, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, signScalar_re,
      signScalar_im] <;> ring

private theorem signPairWeight_energy (imag : Bool) (a b : ℂ) :
    (signPairWeight imag a b false) ^ 2 + (signPairWeight imag a b true) ^ 2 ≤
      (18 / 25 : ℝ) * (Complex.normSq a + Complex.normSq b) := by
  cases imag <;>
    simp [signComponent, signPairWeight, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  · nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.im + b.im)]
  · nlinarith [sq_nonneg (a.im - b.im), sq_nonneg (a.re + b.re)]

/-- Coefficients of a fixed real or imaginary bilinear component on the sign cube. -/
def signBilinearCoefficients {α : Type} [LinearOrder α] (imag : Bool)
    (x y : α → ℂ) (idx : HermitianSignIndex α) : ℝ :=
  if idx.2.1 < idx.2.2 then
    signPairWeight imag (star (x idx.2.1) * y idx.2.2) (star (x idx.2.2) * y idx.2.1) idx.1
  else 0

private theorem sum_signCubeMatrix_upper {α : Type} [Fintype α] [LinearOrder α]
    [DecidableEq α] (a : α → α → ℂ) (ω : HermitianSignIndex α → Bool) :
    (∑ i, ∑ j, a i j * signCubeMatrix ω i j) =
      ∑ i, ∑ j, if i < j then
        a i j * signScalar (ω (false, i, j)) (ω (true, i, j)) +
          a j i * star (signScalar (ω (false, i, j)) (ω (true, i, j)))
        else 0 := by
  let S (i j : α) := signScalar (ω (false, i, j)) (ω (true, i, j))
  let U (i j : α) := if i < j then a i j * S i j else 0
  let L (i j : α) := if j < i then a i j * star (S j i) else 0
  have hsplit (i j : α) : a i j * signCubeMatrix ω i j = U i j + L i j := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [signCubeMatrix, finiteSignMatrix, S, U, L, h, h.ne, h.not_gt]
    · simp [signCubeMatrix, finiteSignMatrix, U, L]
    · simp [signCubeMatrix, finiteSignMatrix, S, U, L, h, h.ne', h.not_gt]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := L)]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [U, L, S, hij]

/-- Every fixed bilinear component is exactly the indicated real sign functional. -/
theorem signCubeMatrix_bilinear_component_eq {α : Type} [Fintype α] [LinearOrder α]
    [DecidableEq α] (imag : Bool) (x y : α → ℂ) (ω : HermitianSignIndex α → Bool) :
    signComponent imag (star x ⬝ᵥ (signCubeMatrix ω *ᵥ y)) =
      signLinearForm (signBilinearCoefficients imag x y) ω := by
  let a (i j : α) := star (x i) * y j
  have hsum : star x ⬝ᵥ (signCubeMatrix ω *ᵥ y) =
      ∑ i, ∑ j, a i j * signCubeMatrix ω i j := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a]
    ring
  rw [hsum, sum_signCubeMatrix_upper]
  simp only [signLinearForm, Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [signComponent_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simpa [signBilinearCoefficients, a, hij, add_comm] using
      (signComponent_pair imag (a i j) (a j i) (ω (false, i, j)) (ω (true, i, j)))
  · simp [signBilinearCoefficients, signComponent, hij]

private theorem sum_upper_normSq_le {α : Type} [Fintype α] [LinearOrder α]
    (a : α → α → ℂ) :
    (∑ i, ∑ j, if i < j then Complex.normSq (a i j) + Complex.normSq (a j i) else 0) ≤
      ∑ i, ∑ j, Complex.normSq (a i j) := by
  let U (i j : α) := if i < j then Complex.normSq (a i j) else 0
  let L (i j : α) := if j < i then Complex.normSq (a i j) else 0
  have hsplit (i j : α) :
      (if i < j then Complex.normSq (a i j) + Complex.normSq (a j i) else 0) =
        U i j + L j i := by
    by_cases hij : i < j <;> simp [U, L, hij]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => L j i)]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [U, L, h, h.not_gt]
  · simpa [U, L] using Complex.normSq_nonneg (a i i)
  · simp [U, L, h, h.not_gt]

/-- Both components have variance proxy at most `(18/25) ‖x‖₂² ‖y‖₂²`. -/
theorem signBilinearCoefficients_energy_le {α : Type} [Fintype α] [LinearOrder α]
    (imag : Bool) (x y : α → ℂ) :
    (∑ k, signBilinearCoefficients imag x y k ^ 2) ≤
      (18 / 25 : ℝ) * (∑ i, Complex.normSq (x i)) * (∑ j, Complex.normSq (y j)) := by
  let a (i j : α) := star (x i) * y j
  calc
    _ ≤ (18 / 25 : ℝ) *
        (∑ i, ∑ j, if i < j then Complex.normSq (a i j) + Complex.normSq (a j i) else 0) := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      simp_rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i < j
      · simpa [signBilinearCoefficients, a, hij, add_comm] using
          (signPairWeight_energy imag (a i j) (a j i))
      · simp [signBilinearCoefficients, hij]
    _ ≤ (18 / 25 : ℝ) * (∑ i, ∑ j, Complex.normSq (a i j)) :=
      mul_le_mul_of_nonneg_left (sum_upper_normSq_le a) (by norm_num)
    _ = _ := by
      simp only [a, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, mul_assoc]

private theorem sum_normSq_le_one {α : Type} [Fintype α] {x : α → ℂ}
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) : (∑ i, Complex.normSq (x i)) ≤ 1 := by
  have heq : (∑ i, Complex.normSq (x i)) = ‖WithLp.toLp 2 x‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : α => ℂ) (WithLp.toLp 2 x)).symm
  rw [heq]
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

/-- Each real or imaginary bilinear component of the exact bipartite sample is
sub-Gaussian with variance proxy `18/25` on the Euclidean unit ball. -/
theorem signCubeSample_bilinear_component_hasSubgaussianMGF {d : ℕ}
    (imag : Bool) (x y : Fin d × Fin d → ℂ)
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) (hy : ‖WithLp.toLp 2 y‖ ≤ 1) :
    HasSubgaussianMGF (fun ω => signComponent imag (star x ⬝ᵥ (signCubeSample ω *ᵥ y)))
      (18 / 25 : ℝ≥0) (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))) := by
  let : LinearOrder (Fin d × Fin d) := Equiv.linearOrder finProdFinEquiv
  have hcoeff : (∑ i, signBilinearCoefficients imag x y i ^ 2) ≤ (18 / 25 : ℝ) := by
    have hx' := sum_normSq_le_one hx
    have hy' := sum_normSq_le_one hy
    have hy_nonneg : 0 ≤ ∑ j, Complex.normSq (y j) :=
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (y j)
    apply (signBilinearCoefficients_energy_le imag x y).trans
    calc
      _ ≤ (18 / 25 : ℝ) * 1 * 1 := by gcongr
      _ = _ := by ring
  have h := signLinearForm_hasSubgaussianMGF_le (c := (18 / 25 : ℝ≥0))
    (signBilinearCoefficients imag x y) (by simpa using hcoeff)
  refine h.congr (ae_of_all _ fun ω => ?_)
  change signLinearForm (signBilinearCoefficients imag x y) ω =
    signComponent imag (star x ⬝ᵥ (signCubeMatrix ω *ᵥ y))
  exact (signCubeMatrix_bilinear_component_eq imag x y ω).symm

theorem signCubeSample_bilinear_component_tail {d : ℕ}
    (imag : Bool) (x y : Fin d × Fin d → ℂ)
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) (hy : ‖WithLp.toLp 2 y‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | t ≤ |signComponent imag (star x ⬝ᵥ (signCubeSample ω *ᵥ y))|} ≤
      2 * Real.exp (-(t ^ 2) / (2 * (18 / 25 : ℝ))) := by
  simpa using subgaussian_abs_tail
    (signCubeSample_bilinear_component_hasSubgaussianMGF imag x y hx hy) ht

/-- Complex bilinear norm tail on the exact bipartite sign sample. -/
theorem signCubeSample_bilinear_tail {d : ℕ} (x y : Fin d × Fin d → ℂ)
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) (hy : ‖WithLp.toLp 2 y‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | t ≤ ‖star x ⬝ᵥ (signCubeSample ω *ᵥ y)‖} ≤
      4 * Real.exp (-(t ^ 2) / (4 * (18 / 25 : ℝ))) := by
  let μ := signCubeMeasure (HermitianSignIndex (Fin d × Fin d))
  let z (ω : HermitianSignIndex (Fin d × Fin d) → Bool) :=
    star x ⬝ᵥ (signCubeSample ω *ᵥ y)
  let u := t / Real.sqrt 2
  have hs : 0 < Real.sqrt 2 := by positivity
  have hu : 0 ≤ u := div_nonneg ht hs.le
  have hsub : {ω | t ≤ ‖z ω‖} ⊆ {ω | u ≤ |(z ω).re|} ∪ {ω | u ≤ |(z ω).im|} := by
    intro ω hω
    have h : t ≤ Real.sqrt 2 * max |(z ω).re| |(z ω).im| :=
      hω.trans (Complex.norm_le_sqrt_two_mul_max _)
    have hmax : u ≤ max |(z ω).re| |(z ω).im| :=
      (div_le_iff₀ hs).2 (by simpa only [mul_comm] using h)
    exact le_max_iff.mp hmax
  have h_re : μ.real {ω | u ≤ |(z ω).re|} ≤ 2 * Real.exp (-(u ^ 2) / (2 * (18 / 25 : ℝ))) :=
    signCubeSample_bilinear_component_tail false x y hx hy hu
  have h_im : μ.real {ω | u ≤ |(z ω).im|} ≤ 2 * Real.exp (-(u ^ 2) / (2 * (18 / 25 : ℝ))) :=
    signCubeSample_bilinear_component_tail true x y hx hy hu
  have hsq : u ^ 2 = t ^ 2 / 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have hexp : -(u ^ 2) / (2 * (18 / 25 : ℝ)) = -(t ^ 2) / (4 * (18 / 25 : ℝ)) := by
    rw [hsq]
    ring
  calc
    _ ≤ μ.real ({ω | u ≤ |(z ω).re|} ∪ {ω | u ≤ |(z ω).im|}) := measureReal_mono hsub
    _ ≤ μ.real {ω | u ≤ |(z ω).re|} + μ.real {ω | u ≤ |(z ω).im|} := measureReal_union_le _ _
    _ ≤ _ := by
      convert add_le_add h_re h_im using 1
      rw [hexp]
      ring

/-- Hermitian quadratic forms are real, so their norm tail uses the one-component bound. -/
theorem signCubeSample_quadratic_tail {d : ℕ} (x : Fin d × Fin d → ℂ)
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | t ≤ ‖star x ⬝ᵥ (signCubeSample ω *ᵥ x)‖} ≤
      2 * Real.exp (-(t ^ 2) / (2 * (18 / 25 : ℝ))) := by
  have h_abs (ω : HermitianSignIndex (Fin d × Fin d) → Bool) :
      |signComponent false (star x ⬝ᵥ (signCubeSample ω *ᵥ x))| =
        ‖star x ⬝ᵥ (signCubeSample ω *ᵥ x)‖ := by
    apply Complex.abs_re_eq_norm.mpr
    have hH : (signCubeSample ω).IsHermitian := finiteSignSample_isHermitian _ _
    have h := congrArg Complex.im (hH.star_dotProduct_mulVec_comm x x)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  simpa only [h_abs] using signCubeSample_bilinear_component_tail false x x hx hx ht

/-- Union bound for any specified finite family of pairs of vectors in the unit ball. -/
theorem signCubeSample_bilinear_finset_tail {d : ℕ} {ι : Type*} (s : Finset ι)
    (x y : ι → Fin d × Fin d → ℂ)
    (hx : ∀ i ∈ s, ‖WithLp.toLp 2 (x i)‖ ≤ 1)
    (hy : ∀ i ∈ s, ‖WithLp.toLp 2 (y i)‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | ∃ i ∈ s, t ≤ ‖star (x i) ⬝ᵥ (signCubeSample ω *ᵥ y i)‖} ≤
      (s.card : ℝ) * (4 * Real.exp (-(t ^ 2) / (4 * (18 / 25 : ℝ)))) := by
  let μ := signCubeMeasure (HermitianSignIndex (Fin d × Fin d))
  let E (i : ι) := {ω : HermitianSignIndex (Fin d × Fin d) → Bool |
    t ≤ ‖star (x i) ⬝ᵥ (signCubeSample ω *ᵥ y i)‖}
  change μ.real {ω | ∃ i ∈ s, ω ∈ E i} ≤ _
  rw [show {ω | ∃ i ∈ s, ω ∈ E i} = ⋃ i ∈ s, E i by ext ω; simp]
  calc
    _ ≤ ∑ i ∈ s, μ.real (E i) := measureReal_biUnion_finset_le s E
    _ ≤ ∑ _i ∈ s, 4 * Real.exp (-(t ^ 2) / (4 * (18 / 25 : ℝ))) :=
      Finset.sum_le_sum fun i hi => signCubeSample_bilinear_tail (x i) (y i) (hx i hi) (hy i hi) ht
    _ = _ := by simp [nsmul_eq_mul]

end D5.S3.Quantum.Entanglement.EntanglementBreaking
