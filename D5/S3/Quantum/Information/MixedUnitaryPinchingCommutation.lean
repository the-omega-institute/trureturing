/- GID: D5/S3/Quantum/Information/MixedUnitaryPinchingCommutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/MixedUnitaryPinchingCommutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Non-isotropic mixed-unitary qubit channels fail to commute with marginal pinching. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Information.ActualQubitChordObstruction

/-! Spectral marginal pinching and mixed-unitary qubit channels. -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.FiniteDimensional (QubitMatrix qubitX qubitZ)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch blochMatrix blochLinear)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma spin)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)

namespace D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation

/-- A finite convex combination of unitary conjugations, on every complex matrix. -/
def IsMixedUnitary (φ : QubitMatrix → QubitMatrix) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (u : Fin k → QubitMatrix),
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j = 1) ∧
    (∀ j, u j ∈ unitaryGroup (Fin 2) ℂ) ∧
    ∀ a, φ a = ∑ j, (p j : ℂ) • (u j * a * star (u j))

/-- The source's isotropic channels, extended linearly from states to all matrices.
The antiunitary action on states is `a ↦ u * aᵀ * star u`. -/
def IsIsotropic (φ : QubitMatrix → QubitMatrix) : Prop :=
  ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ u ∈ unitaryGroup (Fin 2) ℂ,
    (∀ a, φ a = ((1 - γ : ℝ) : ℂ) • (u * a * star u) +
      (γ : ℂ) • (a.trace / 2) • 1) ∨
    (∀ a, φ a = ((1 - γ : ℝ) : ℂ) • (u * aᵀ * star u) +
      (γ : ℂ) • (a.trace / 2) • 1)

/-- The tensor extension `φ ⊗ id`, acting on each block indexed by the second qubit. -/
def localMap (φ : QubitMatrix → QubitMatrix)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a c => φ (fun i j => ρ (i, a.2) (j, c.2)) a.1 c.1

/-- The marginal on the first qubit is the partial trace over the second qubit. -/
def marginalA (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : QubitMatrix :=
  partialTraceRight ρ

/-- A Hermitian qubit matrix with two distinct eigenvalues. -/
def IsNondegenerate (a : QubitMatrix) : Prop :=
  ∃ h : a.IsHermitian, Function.Injective h.eigenvalues

/-- Pinching in a spectral basis of the first marginal, by its rank-one eigenprojectors.
The value outside the Hermitian-marginal domain is an arbitrary total extension. -/
def pinchA (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := by
  classical
  exact if h : (marginalA ρ).IsHermitian then
    ∑ i : Fin 2,
      let p : QubitMatrix := fun a c =>
        h.eigenvectorBasis i a * star (h.eigenvectorBasis i c)
      (p ⊗ₖ (1 : QubitMatrix)) * ρ * (p ⊗ₖ (1 : QubitMatrix))
  else ρ

private def blochOperator (φ : QubitMatrix → QubitMatrix) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (trace (sigma i.succ * φ (sigma j.succ))).re / 2

private def witness (n x : Fin 3 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 4 : ℂ) • ((1 : QubitMatrix) ⊗ₖ (1 : QubitMatrix) +
    (1 / 2 : ℂ) • (spin n ⊗ₖ (1 : QubitMatrix)) +
    (1 / 4 : ℂ) • (spin x ⊗ₖ qubitZ))

private lemma mixed_basic (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ) :
    (∃ f : QubitMatrix →ₗ[ℂ] QubitMatrix, ∀ a, φ a = f a) ∧
    φ 1 = 1 ∧ (∀ a, (φ a).trace = a.trace) ∧
    (∀ a, a.IsHermitian → (φ a).IsHermitian) := by
  obtain ⟨k, p, u, _, hp, hu, hrep⟩ := hφ
  let f : QubitMatrix →ₗ[ℂ] QubitMatrix :=
    { toFun := fun a => ∑ j, (p j : ℂ) • (u j * a * star (u j))
      map_add' := by
        intro a b
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Finset.smul_sum,
          RingHom.id_apply]
        congr 1
        funext j
        rw [mul_comm c] }
  refine ⟨⟨f, hrep⟩, ?_, ?_, ?_⟩
  · rw [hrep]
    simp only [mul_one, Unitary.mul_star_self_of_mem (hu _), ← Finset.sum_smul,
      ← Complex.ofReal_sum, hp, Complex.ofReal_one, one_smul]
  · intro a
    rw [hrep, Matrix.trace_sum]
    have he (j : Fin k) : trace (u j * a * star (u j)) = trace a := by
      rw [Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem (hu j), one_mul]
    simp only [Matrix.trace_smul, he, smul_eq_mul, ← Finset.sum_mul,
      ← Complex.ofReal_sum, hp, Complex.ofReal_one, one_mul]
  · intro a ha
    rw [hrep]
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, star_sum, star_mul,
      Complex.star_def, Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro l _
    have hs : (u l * a * star (u l)).IsHermitian := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.isHermitian_mul_mul_conjTranspose (u l) ha
    rw [← Complex.star_def, hs.apply]
    ring

private lemma mixed_channel_data (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ) :
    (∃ f : QubitMatrix →ₗ[ℂ] QubitMatrix, ∀ a, φ a = f a) ∧
    φ 1 = 1 ∧ (∀ a, (φ a).trace = a.trace) ∧
    (∀ a, a.IsHermitian → (φ a).IsHermitian) ∧
    ∀ v : Fin 3 → ℝ, φ (spin v) = spin (blochOperator φ *ᵥ v) := by
  obtain ⟨hf, h1, htr, hh⟩ := mixed_basic φ hφ
  refine ⟨hf, h1, htr, hh, ?_⟩
  obtain ⟨f, hf⟩ := hf
  have hsigma (j : Fin 3) : (sigma j.succ).IsHermitian ∧ trace (sigma j.succ) = 0 := by
    fin_cases j <;> constructor
    all_goals first
      | (apply Matrix.IsHermitian.ext; intro i j; fin_cases i <;> fin_cases j <;>
          simp [sigma, pauliMatrix, qubitX, qubitZ])
      | simp [sigma, pauliMatrix, qubitX, qubitZ, Matrix.trace_fin_two]
  have hcolumn (j : Fin 3) : φ (sigma j.succ) = spin (fun i => blochOperator φ i j) := by
    let m := φ (sigma j.succ)
    have hm : m.IsHermitian := hh _ (hsigma j).1
    have ht : trace m = 0 := (htr _).trans (hsigma j).2
    have hr : (m 1 0).re = (m 0 1).re := by
      simpa using (congrArg Complex.re (hm.apply 1 0)).symm
    have hi : (m 1 0).im = -(m 0 1).im := by
      simpa using (congrArg Complex.im (hm.apply 1 0)).symm
    calc
      m = blochMatrix 0 (bloch m) := by
        simpa only [ht, Complex.zero_re] using
          (D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
            m hm).1
      _ = _ := by
        change blochMatrix 0 (bloch m) = spin (fun i => (trace (sigma i.succ * m)).re / 2)
        ext i k
        fin_cases i <;> fin_cases k <;> apply Complex.ext <;>
          simp [blochMatrix, bloch, spin, sigma, pauliMatrix, qubitX, qubitZ,
            Fin.sum_univ_three, Matrix.trace_fin_two, Matrix.mul_apply,
            Fin.sum_univ_two, hr, hi] <;> ring
  intro v
  have hs : φ (spin v) = ∑ j, (v j : ℂ) • φ (sigma j.succ) := by
    rw [hf, spin, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, ← hf]
  rw [hs]
  simp_rw [hcolumn]
  unfold spin Matrix.mulVec dotProduct
  simp only [Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_mul]
  module

private lemma scalar_gram_isotropic (φ : QubitMatrix → QubitMatrix)
    (hφ : IsMixedUnitary φ)
    (hq : ∃ c : ℝ, (blochOperator φ)ᵀ * blochOperator φ = c • 1) :
    IsIsotropic φ := by
  sorry

private lemma normalize_probe (t : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3 → ℝ)
    (hab : a ⬝ᵥ b = 0) (hc : (t *ᵥ a) ⬝ᵥ (t *ᵥ b) ≠ 0) :
    ∃ n x : Fin 3 → ℝ, n ⬝ᵥ n = 1 ∧ x ⬝ᵥ x = 1 ∧ n ⬝ᵥ x = 0 ∧
      (t *ᵥ n) ⬝ᵥ (t *ᵥ x) ≠ 0 := by
  have ha : a ≠ 0 := by
    intro h
    exact hc (by rw [h, Matrix.mulVec_zero, zero_dotProduct])
  have hb : b ≠ 0 := by
    intro h
    exact hc (by rw [h, Matrix.mulVec_zero, dotProduct_zero])
  have hpos (v : Fin 3 → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v := by
    have hn : 0 ≤ v ⬝ᵥ v := by
      unfold dotProduct
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    exact lt_of_le_of_ne hn (Ne.symm (dotProduct_self_eq_zero.not.mpr hv))
  have hra : Real.sqrt (a ⬝ᵥ a) ≠ 0 := (Real.sqrt_pos.mpr (hpos a ha)).ne'
  have hrb : Real.sqrt (b ⬝ᵥ b) ≠ 0 := (Real.sqrt_pos.mpr (hpos b hb)).ne'
  have hunit (v : Fin 3 → ℝ) (hv : v ≠ 0) :
      ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) = 1 := by
    rw [smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    have hr := (Real.sqrt_pos.mpr (hpos v hv)).ne'
    field_simp [hr]
    nlinarith [Real.sq_sqrt (hpos v hv).le]
  refine ⟨(Real.sqrt (a ⬝ᵥ a))⁻¹ • a, (Real.sqrt (b ⬝ᵥ b))⁻¹ • b,
    hunit a ha, hunit b hb, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, hab, smul_zero, smul_zero]
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    exact mul_ne_zero (inv_ne_zero hra) (mul_ne_zero (inv_ne_zero hrb) hc)

private lemma orthogonal_probe (t : Matrix (Fin 3) (Fin 3) ℝ)
    (ht : ¬ ∃ c : ℝ, tᵀ * t = c • 1) :
    ∃ n x : Fin 3 → ℝ, n ⬝ᵥ n = 1 ∧ x ⬝ᵥ x = 1 ∧ n ⬝ᵥ x = 0 ∧
      (t *ᵥ n) ⬝ᵥ (t *ᵥ x) ≠ 0 := by
  classical
  let q := tᵀ * t
  have hgram (a b : Fin 3 → ℝ) : (t *ᵥ a) ⬝ᵥ (t *ᵥ b) = a ⬝ᵥ (q *ᵥ b) := by
    symm
    change a ⬝ᵥ ((tᵀ * t) *ᵥ b) = _
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have he (i j : Fin 3) :
      (t *ᵥ Pi.single i 1) ⬝ᵥ (t *ᵥ Pi.single j 1) = q i j := by
    rw [hgram, single_dotProduct, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply, one_mul]
  by_cases hoff : ∃ i j, i ≠ j ∧ q i j ≠ 0
  · obtain ⟨i, j, hij, hq⟩ := hoff
    apply normalize_probe t (Pi.single i 1) (Pi.single j 1)
    · simp [single_dotProduct, hij]
    · rwa [he]
  · have ho (i j : Fin 3) (hij : i ≠ j) : q i j = 0 := by
      by_contra h
      exact hoff ⟨i, j, hij, h⟩
    have hd : ∃ i, q i i ≠ q 0 0 := by
      by_contra h
      push Not at h
      apply ht
      refine ⟨q 0 0, ?_⟩
      change q = q 0 0 • 1
      ext i j
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using h i
      · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul, mul_zero]
        exact ho i j hij
    obtain ⟨i, hi⟩ := hd
    have hi0 : i ≠ 0 := by intro h; exact hi (by rw [h])
    apply normalize_probe t (Pi.single 0 1 + Pi.single i 1) (Pi.single 0 1 - Pi.single i 1)
    · simp [add_dotProduct, dotProduct_sub, single_dotProduct, hi0, Ne.symm hi0]
    · rw [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_sub,
        dotProduct_sub, he, he, he, he, ho 0 i (Ne.symm hi0), ho i 0 hi0]
      simpa only [sub_zero, zero_sub, neg_zero, add_zero, zero_add, sub_eq_add_neg]
        using sub_ne_zero.mpr hi.symm

private lemma spectral_projectors (a : QubitMatrix) (h : a.IsHermitian) :
    let p : Fin 2 → QubitMatrix := fun i r s =>
      h.eigenvectorBasis i r * star (h.eigenvectorBasis i s)
    p 0 + p 1 = 1 ∧
      a = (h.eigenvalues 0 : ℂ) • p 0 + (h.eigenvalues 1 : ℂ) • p 1 := by
  dsimp only
  have hu : (h.eigenvectorUnitary : QubitMatrix) *
      star (h.eigenvectorUnitary : QubitMatrix) = 1 :=
    Unitary.coe_mul_star_self h.eigenvectorUnitary
  have hs := h.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  constructor
  · ext i j
    have he := congrFun (congrFun hu i) j
    change h.eigenvectorBasis 0 i * star (h.eigenvectorBasis 0 j) +
      h.eigenvectorBasis 1 i * star (h.eigenvectorBasis 1 j) = (1 : QubitMatrix) i j
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using he
  · calc
      a = _ := hs
      _ = _ := by
        ext i j
        change _ = (h.eigenvalues 0 : ℂ) *
          (h.eigenvectorBasis 0 i * star (h.eigenvectorBasis 0 j)) +
          (h.eigenvalues 1 : ℂ) *
            (h.eigenvectorBasis 1 i * star (h.eigenvectorBasis 1 j))
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.diagonal_apply]
        ring

private lemma pinching_formula
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (v : Fin 3 → ℝ)
    (hm : marginalA ρ = blochMatrix 1 (WithLp.toLp 2 v)) (hv : v ≠ 0) :
    pinchA ρ = (1 / 2 : ℂ) •
      (ρ + (((v ⬝ᵥ v)⁻¹ : ℝ) : ℂ) •
        ((spin v ⊗ₖ (1 : QubitMatrix)) * ρ * (spin v ⊗ₖ (1 : QubitMatrix)))) := by
  classical
  let a := blochMatrix 1 (WithLp.toLp 2 v)
  have ha : a.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [a, blochMatrix]
  have h : (marginalA ρ).IsHermitian := hm.symm ▸ ha
  let p : Fin 2 → QubitMatrix := fun i r s =>
    h.eigenvectorBasis i r * star (h.eigenvectorBasis i s)
  obtain ⟨hsum, hspec⟩ := spectral_projectors (marginalA ρ) h
  change p 0 + p 1 = 1 at hsum
  change marginalA ρ = (h.eigenvalues 0 : ℂ) • p 0 +
    (h.eigenvalues 1 : ℂ) • p 1 at hspec
  have htrace : h.eigenvalues 0 + h.eigenvalues 1 = 1 := by
    have ht := h.trace_eq_sum_eigenvalues
    conv_lhs at ht =>
      rw [hm, D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix_trace]
    rw [Fin.sum_univ_two] at ht
    change (1 : ℂ) = (h.eigenvalues 0 : ℂ) + (h.eigenvalues 1 : ℂ) at ht
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.one_re] using
      (congrArg Complex.re ht).symm
  have hdet : h.eigenvalues 0 * h.eigenvalues 1 = (1 - v ⬝ᵥ v) / 4 := by
    have hd := h.det_eq_prod_eigenvalues
    conv_lhs at hd =>
      rw [hm, D5.S3.Quantum.Information.ActualQubitChordObstruction.det_bloch]
    rw [Fin.prod_univ_two] at hd
    change (((1 - ‖WithLp.toLp 2 v‖ ^ 2) / 4 : ℝ) : ℂ) =
      (h.eigenvalues 0 : ℂ) * (h.eigenvalues 1 : ℂ) at hd
    have hr := congrArg Complex.re hd
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero] at hr
    rw [← hr, EuclideanSpace.real_norm_sq_eq]
    unfold dotProduct
    simp only [pow_two]
  have hdelta : (h.eigenvalues 0 - h.eigenvalues 1) ^ 2 = v ⬝ᵥ v := by
    nlinarith [hdet]
  have hvv : v ⬝ᵥ v ≠ 0 := dotProduct_self_eq_zero.not.mpr hv
  let c : ℂ := (h.eigenvalues 0 : ℂ) - (h.eigenvalues 1 : ℂ)
  have hc : c ^ 2 = ((v ⬝ᵥ v : ℝ) : ℂ) := by
    dsimp only [c]
    exact_mod_cast hdelta
  have hspin : spin v = c • (p 0 - p 1) := by
    have he : spin v = (2 : ℂ) • marginalA ρ - 1 := by
      rw [hm]
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [spin, sigma, pauliMatrix, qubitX, qubitZ, blochMatrix,
          Fin.sum_univ_three] <;> ring
    rw [he, hspec, ← hsum]
    have ht : (h.eigenvalues 1 : ℂ) = 1 - (h.eigenvalues 0 : ℂ) := by
      exact_mod_cast (show h.eigenvalues 1 = 1 - h.eigenvalues 0 by linarith)
    rw [ht]
    dsimp only [c]
    rw [ht]
    module
  let p0 := p 0 ⊗ₖ (1 : QubitMatrix)
  let p1 := p 1 ⊗ₖ (1 : QubitMatrix)
  have hpsum : p0 + p1 = 1 := by
    rw [← Matrix.add_kronecker, hsum, Matrix.one_kronecker_one]
  have hk : spin v ⊗ₖ (1 : QubitMatrix) = c • (p0 - p1) := by
    rw [hspin, Matrix.smul_kronecker]
    congr 1
    ext i j
    change (p 0 i.1 j.1 - p 1 i.1 j.1) * (1 : QubitMatrix) i.2 j.2 =
      p 0 i.1 j.1 * (1 : QubitMatrix) i.2 j.2 -
        p 1 i.1 j.1 * (1 : QubitMatrix) i.2 j.2
    exact sub_mul _ _ _
  have hcoeff : (((v ⬝ᵥ v)⁻¹ : ℝ) : ℂ) * (c * c) = 1 := by
    rw [← pow_two, hc, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hvv)
  rw [pinchA, dite_eq_left h, Fin.sum_univ_two]
  change p0 * ρ * p0 + p1 * ρ * p1 = _
  simp only [hk, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcoeff, one_smul]
  have hr : ρ = (p0 + p1) * ρ * (p0 + p1) := by rw [hpsum, one_mul, mul_one]
  conv_rhs => arg 2; arg 1; rw [hr]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
  module

private lemma witness_marginal (n x : Fin 3 → ℝ) :
    marginalA (witness n x) = blochMatrix 1 (WithLp.toLp 2 ((1 / 2 : ℝ) • n)) := by
  ext i j
  change (∑ b : Fin 2, witness n x (i, b) (j, b)) = _
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [witness, spin, sigma, pauliMatrix, qubitX, qubitZ, blochMatrix,
      Fin.sum_univ_three] <;> ring

private def localLinear (f : QubitMatrix →ₗ[ℂ] QubitMatrix) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →ₗ[ℂ]
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ where
  toFun := localMap f
  map_add' a b := by
    ext i j
    exact congrFun (congrFun (f.map_add
      (fun r s : Fin 2 => a (r, i.2) (s, j.2))
      (fun r s : Fin 2 => b (r, i.2) (s, j.2))) i.1) j.1
  map_smul' c a := by
    ext i j
    exact congrFun (congrFun (f.map_smul c
      (fun r s : Fin 2 => a (r, i.2) (s, j.2))) i.1) j.1

private lemma local_kronecker (f : QubitMatrix →ₗ[ℂ] QubitMatrix) (a b : QubitMatrix) :
    localLinear f (a ⊗ₖ b) = f a ⊗ₖ b := by
  ext i j
  change f (fun r s => a r s * b i.2 j.2) i.1 j.1 = f a i.1 j.1 * b i.2 j.2
  have he : (fun r s => a r s * b i.2 j.2) = b i.2 j.2 • a := by
    ext r s
    exact mul_comm _ _
  rw [he, map_smul]
  exact mul_comm _ _

private lemma spin_triple (a b : Fin 3 → ℝ) :
    spin a * spin b * spin a = (2 * (a ⬝ᵥ b) : ℂ) • spin a -
      ((a ⬝ᵥ a : ℝ) : ℂ) • spin b := by
  unfold dotProduct
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spin, sigma, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

private lemma spin_scale (r : ℝ) (a : Fin 3 → ℝ) :
    spin (r • a) = (r : ℂ) • spin a := by
  unfold spin
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul, Finset.smul_sum]

private lemma spin_square (a : Fin 3 → ℝ) :
    spin a * spin a = ((a ⬝ᵥ a : ℝ) : ℂ) • (1 : QubitMatrix) := by
  unfold dotProduct
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spin, sigma, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

private lemma witness_density (n x : Fin 3 → ℝ)
    (hn : n ⬝ᵥ n = 1) (hx : x ⬝ᵥ x = 1) (hnx : n ⬝ᵥ x = 0) :
    (witness n x).PosSemidef ∧ (witness n x).trace = 1 := by
  let k := spin n ⊗ₖ (1 : QubitMatrix)
  let l := spin x ⊗ₖ qubitZ
  let h := (1 / 2 : ℂ) • k + (1 / 4 : ℂ) • l
  have hspin (v : Fin 3 → ℝ) : (spin v).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [spin, sigma, pauliMatrix, qubitX, qubitZ, Fin.sum_univ_three]
  have hz : qubitZᴴ = qubitZ := by
    exact D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.1
  have hstar : hᴴ = h := by
    simp only [h, k, l, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, (hspin n).eq,
      (hspin x).eq, hz, Complex.star_def, map_div₀, map_one, map_ofNat]
  have hnn : spin n * spin n = 1 := by
    rw [spin_square, hn, Complex.ofReal_one, one_smul]
  have hxx : spin x * spin x = 1 := by
    rw [spin_square, hx, Complex.ofReal_one, one_smul]
  have hanti : spin n * spin x = -(spin x * spin n) := by
    have he := spin_triple n x
    rw [hnx, hn] at he
    norm_num at he
    have hm := congrArg (fun a : QubitMatrix => a * spin n) he
    simpa only [Matrix.mul_assoc, hnn, Matrix.mul_one, neg_mul] using hm
  have hkk : k * k = 1 := by
    simp only [k, ← Matrix.mul_kronecker_mul, hnn, Matrix.one_mul,
      Matrix.one_kronecker_one]
  have hll : l * l = 1 := by
    have hzz : qubitZ * qubitZ = 1 := by
      simpa only [pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2
    simp only [l, ← Matrix.mul_kronecker_mul, hxx, hzz, Matrix.one_kronecker_one]
  have hkl : k * l = -(l * k) := by
    simp only [k, l, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hanti]
    ext i j
    change -(spin x * spin n) i.1 j.1 * qubitZ i.2 j.2 =
      -((spin x * spin n) i.1 j.1 * qubitZ i.2 j.2)
    ring
  have hsq : h * h = (5 / 16 : ℂ) • 1 := by
    simp only [h, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hkk, hll, hkl]
    module
  have hw : witness n x = (1 / 4 : ℂ) • (1 + h) := by
    rw [witness, Matrix.one_kronecker_one]
    dsimp only [h, k, l]
    module
  have heq : witness n x = (1 / 8 : ℂ) • ((1 + h) * (1 + h)ᴴ) +
      (11 / 128 : ℂ) • 1 := by
    rw [hw, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hstar]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hsq]
    module
  constructor
  · rw [heq]
    exact ((Matrix.posSemidef_self_mul_conjTranspose (1 + h)).smul
      (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 8)).add
      ((Matrix.PosSemidef.one).smul
        (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 11 / 128))
  · have ht (v : Fin 3 → ℝ) : trace (spin v) = 0 := by
      rw [Matrix.trace_fin_two]
      simp [spin, sigma, pauliMatrix, qubitX, qubitZ, Fin.sum_univ_three]
    simp only [witness, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_kronecker, ht]
    norm_num [qubitZ, Matrix.trace_fin_two]

private lemma local_witness (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (n x : Fin 3 → ℝ) :
    localMap φ (witness n x) = witness (blochOperator φ *ᵥ n) (blochOperator φ *ᵥ x) := by
  obtain ⟨⟨f, hf⟩, h1, _, _, hspin⟩ := mixed_channel_data φ hφ
  have he : φ = f := funext hf
  subst φ
  change localLinear f (witness n x) = _
  simp only [witness, map_add, map_smul, local_kronecker, h1, hspin]

private lemma pinch_witness (a b : Fin 3 → ℝ) (ha : a ≠ 0) :
    pinchA (witness a b) = witness a (((a ⬝ᵥ b) / (a ⬝ᵥ a)) • a) := by
  have haa : a ⬝ᵥ a ≠ 0 := dotProduct_self_eq_zero.not.mpr ha
  have hc : ((a ⬝ᵥ a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast haa
  rw [pinching_formula (witness a b) ((1 / 2 : ℝ) • a) (witness_marginal a b)
    (smul_ne_zero (by norm_num) ha)]
  simp only [spin_scale, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold witness
  simp only [spin_scale, Matrix.smul_kronecker, Matrix.one_kronecker_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, spin_triple,
    spin_square, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  push_cast
  field_simp [hc]
  ring

private lemma mapped_marginal (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (n x : Fin 3 → ℝ) :
    marginalA (localMap φ (witness n x)) = φ (marginalA (witness n x)) ∧
    φ (marginalA (witness n x)) =
      blochMatrix 1 (WithLp.toLp 2 ((1 / 2 : ℝ) • (blochOperator φ *ᵥ n))) := by
  obtain ⟨⟨f, hf⟩, _, _, _⟩ := mixed_basic φ hφ
  have he : φ = f := funext hf
  have hl : marginalA (localMap φ (witness n x)) = φ (marginalA (witness n x)) := by
    rw [he]
    let a0 : QubitMatrix := fun r s => witness n x (r, 0) (s, 0)
    let a1 : QubitMatrix := fun r s => witness n x (r, 1) (s, 1)
    have hm : marginalA (witness n x) = a0 + a1 := by
      ext r s
      change (∑ b : Fin 2, witness n x (r, b) (s, b)) = _
      rw [Fin.sum_univ_two]
      rfl
    rw [hm]
    ext i j
    change (∑ b : Fin 2, f (fun r s => witness n x (r, b) (s, b)) i j) =
      f (a0 + a1) i j
    rw [Fin.sum_univ_two, f.map_add]
    rfl
  refine ⟨hl, ?_⟩
  rw [← hl, local_witness φ hφ, witness_marginal]

private lemma bloch_nondegenerate (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    IsNondegenerate (blochMatrix 1 (WithLp.toLp 2 v)) := by
  let a := blochMatrix 1 (WithLp.toLp 2 v)
  have h : a.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [a, blochMatrix]
  refine ⟨h, ?_⟩
  have hn : h.eigenvalues 0 ≠ h.eigenvalues 1 := by
    intro he
    let p : Fin 2 → QubitMatrix := fun i r s =>
      h.eigenvectorBasis i r * star (h.eigenvectorBasis i s)
    obtain ⟨hsum, hspec⟩ := spectral_projectors a h
    change p 0 + p 1 = 1 at hsum
    change a = (h.eigenvalues 0 : ℂ) • p 0 + (h.eigenvalues 1 : ℂ) • p 1 at hspec
    rw [he, ← smul_add, hsum] at hspec
    have hb := congrArg bloch hspec
    have hz : bloch ((h.eigenvalues 1 : ℂ) • (1 : QubitMatrix)) = 0 := by
      ext i
      fin_cases i <;> simp [bloch]
    change bloch (blochMatrix 1 (WithLp.toLp 2 v)) = _ at hb
    rw [D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_blochMatrix, hz] at hb
    apply hv
    funext i
    exact congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w i) hb
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hn hij)
  · exact False.elim (hn hij.symm)
  · rfl

private lemma commutator_identity (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (n x : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1) (hnx : n ⬝ᵥ x = 0)
    (htn : blochOperator φ *ᵥ n ≠ 0) :
    pinchA (localMap φ (witness n x)) - localMap φ (pinchA (witness n x)) =
      ((((blochOperator φ *ᵥ n) ⬝ᵥ (blochOperator φ *ᵥ x) /
        ((blochOperator φ *ᵥ n) ⬝ᵥ (blochOperator φ *ᵥ n)) : ℝ) : ℂ) / 16) •
        (spin (blochOperator φ *ᵥ n) ⊗ₖ qubitZ) := by
  have hn0 : n ≠ 0 := by
    intro h
    simp only [h, zero_dotProduct] at hn
    norm_num at hn
  rw [local_witness φ hφ, pinch_witness _ _ htn, pinch_witness n x hn0,
    hnx, zero_div, zero_smul, local_witness φ hφ, Matrix.mulVec_zero]
  unfold witness
  have hz : spin (0 : Fin 3 → ℝ) = 0 := by simp [spin]
  simp only [spin_scale, Matrix.smul_kronecker, hz, Matrix.zero_kronecker]
  module

private lemma commutator_nonzero (a b : Fin 3 → ℝ) (hab : a ⬝ᵥ b ≠ 0) :
    ((((a ⬝ᵥ b) / (a ⬝ᵥ a) : ℝ) : ℂ) / 16) • (spin a ⊗ₖ qubitZ) ≠ 0 := by
  have ha : a ≠ 0 := by
    intro h
    exact hab (by rw [h, zero_dotProduct])
  have haa : a ⬝ᵥ a ≠ 0 := dotProduct_self_eq_zero.not.mpr ha
  have hc : ((((a ⬝ᵥ b) / (a ⬝ᵥ a) : ℝ) : ℂ) / 16) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast div_ne_zero hab haa) (by norm_num)
  apply smul_ne_zero hc
  intro hk
  have hs : spin a = 0 := by
    ext i j
    have he := congrFun (congrFun hk (i, 0)) (j, 0)
    change spin a i j * qubitZ 0 0 = 0 at he
    simpa [qubitZ] using he
  have he := spin_square a
  rw [hs, zero_mul] at he
  have hz := congrFun (congrFun he 0) 0
  have : ((a ⬝ᵥ a : ℝ) : ℂ) = 0 := by simpa using hz.symm
  exact haa (by exact_mod_cast this)

/-- Every non-isotropic mixed-unitary qubit channel fails to commute with marginal pinching
on a two-qubit density matrix whose input and output marginals are nondegenerate. -/
theorem result (φ : QubitMatrix → QubitMatrix) (hφ : IsMixedUnitary φ)
    (hi : ¬ IsIsotropic φ) :
    ∃ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ IsNondegenerate (marginalA ρ) ∧
      IsNondegenerate (φ (marginalA ρ)) ∧
      pinchA (localMap φ ρ) ≠ localMap φ (pinchA ρ) := by
  have hq : ¬ ∃ c : ℝ, (blochOperator φ)ᵀ * blochOperator φ = c • 1 :=
    fun h => hi (scalar_gram_isotropic φ hφ h)
  obtain ⟨n, x, hn, hx, hnx, hcross⟩ := orthogonal_probe (blochOperator φ) hq
  have hn0 : n ≠ 0 := by
    intro h
    simp only [h, zero_dotProduct] at hn
    norm_num at hn
  have htn : blochOperator φ *ᵥ n ≠ 0 := by
    intro h
    exact hcross (by rw [h, zero_dotProduct])
  have hn2 : (1 / 2 : ℝ) • n ≠ 0 := smul_ne_zero (by norm_num) hn0
  have htn2 : (1 / 2 : ℝ) • (blochOperator φ *ᵥ n) ≠ 0 :=
    smul_ne_zero (by norm_num) htn
  refine ⟨witness n x, (witness_density n x hn hx hnx).1,
    (witness_density n x hn hx hnx).2, ?_, ?_, ?_⟩
  · rw [witness_marginal]
    exact bloch_nondegenerate _ hn2
  · rw [(mapped_marginal φ hφ n x).2]
    exact bloch_nondegenerate _ htn2
  · intro heq
    have hz := commutator_identity φ hφ n x hn hnx htn
    rw [heq, sub_self] at hz
    exact commutator_nonzero _ _ hcross hz.symm

end D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
