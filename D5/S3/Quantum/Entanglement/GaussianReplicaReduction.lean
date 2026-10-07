/- GID: D5/S3/Quantum/Entanglement/GaussianReplicaReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianReplicaReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian integrals and twist kernels reduce replica determinants. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
open Matrix Filter Topology
open scoped Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.GaussianReplicaReduction

/-! ## Gaussian quadratic integrals -/

section GaussianQuadraticIntegrals

/-
Source: mbrcic/ai-safety-formalization-atlas, commit
254b6275b753efb609cd38ef4c85eef29b4a13b4,
AISafetyAtlas/SingularLearning/GaussianQuadratic.lean.
Source: mbrcic/ai-safety-formalization-atlas, same commit,
AISafetyAtlas/SingularLearning/Coordinates.lean.
Authors: Mario Brcic (upstream CITATION.cff).
Apache-2.0; full license, source mapping and retirement condition:
Library/Analytic/brcic2026gaussianquadratic.md.
The declarations are transplanted verbatim up to import visibility, removal of
the module command and public modifier in the repository's non-module syntax,
and the namespace adaptation from AISafetyAtlas.SingularLearning to
D5.S3.Quantum.Entanglement.GaussianReplicaReduction.
-/

open MeasureTheory Matrix Real WithLp
open scoped Matrix MatrixOrder

/-! ## Change of variables along a linear map -/

/-- **Linear change of variables.** For an additive Haar measure `μ` on a finite-dimensional
real normed space and a linear self-map `f` with nonzero determinant,

    ∫ x, g (f x) ∂μ = |det f|⁻¹ • ∫ y, g y ∂μ .

Mathlib has the measure-level statement
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` but not this integral-level
corollary; only the scalar-dilation special cases (`Measure.integral_comp_smul` and friends)
are available. No hypothesis on `g` is needed, because `f` is a homeomorphism and hence a
measurable embedding. -/
theorem integral_comp_linearMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) (g : E → F) :
    ∫ x, g (f x) ∂μ = |LinearMap.det f|⁻¹ • ∫ y, g y ∂μ := by
  have hemb : MeasurableEmbedding f :=
    (f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  rw [← hemb.integral_map (μ := μ) g, Measure.map_linearMap_addHaar_eq_smul_addHaar μ hf,
    integral_smul_measure]
  simp [abs_inv]

/-! ## The square-root factorization -/

/-- Every positive-definite real matrix factors as `M = Bᵀ * B` with `B.det = √(det M)`.

The witness is the continuous-functional-calculus square root `CFC.sqrt M`, which is
self-adjoint (hence symmetric over `ℝ`) and squares to `M`; its determinant is `√(det M)` by
`Matrix.PosSemidef.det_sqrt`. Positive definiteness is used only through
`Matrix.nonneg_iff_posSemidef`, i.e. to know `0 ≤ M` in the matrix order. -/
theorem exists_transpose_mul_self_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) : ∃ B : Matrix (Fin n) (Fin n) ℝ, M = Bᵀ * B ∧ B.det = √M.det := by
  have hnn : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hsh : (CFC.sqrt M)ᵀ = CFC.sqrt M :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian
  refine ⟨CFC.sqrt M, ?_, ?_⟩
  · rw [hsh, CFC.sqrt_mul_sqrt_self M hnn]
  · rw [hM.posSemidef.det_sqrt, RCLike.sqrt_of_nonneg hM.posSemidef.det_nonneg]
    simp

/-! ## The multivariate Gaussian integral -/

/-- **The multivariate Gaussian integral.** For a positive-definite `M : ℝ^{n×n}`,

    ∫_{ℝⁿ} exp (-(xᵀ M x)) dx = π ^ (n/2) / √(det M) .

The integral is taken over `EuclideanSpace ℝ (Fin n)`, whose `volume` is Lebesgue measure;
the quadratic form is written on the underlying vector `ofLp x : Fin n → ℝ`.

Absent from the pinned Mathlib, which has only the isotropic case
`GaussianFourier.integral_rexp_neg_mul_sq_norm`. The proof writes `M = Bᵀ B` and applies
`integral_comp_linearMap` to `y = B x`, whose Jacobian `|det B| = √(det M)` is exactly the
determinant factor. -/
theorem integral_exp_neg_quadraticForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(ofLp x ⬝ᵥ M *ᵥ ofLp x))
      = Real.pi ^ ((n : ℝ) / 2) / √M.det := by
  obtain ⟨B, hBM, hBdet⟩ := exists_transpose_mul_self_of_posDef hM
  have hdetB : LinearMap.det (Matrix.toEuclideanLin B : _ →ₗ[ℝ] _) = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hne : LinearMap.det (Matrix.toEuclideanLin B : _ →ₗ[ℝ] _) ≠ 0 := by
    rw [hdetB, hBdet]
    exact ne_of_gt (Real.sqrt_pos.mpr hM.det_pos)
  -- `xᵀ M x = ‖B x‖²`, with the Euclidean norm.
  have key : ∀ x : EuclideanSpace ℝ (Fin n),
      Real.exp (-(ofLp x ⬝ᵥ M *ᵥ ofLp x))
        = Real.exp (-1 * ‖(Matrix.toEuclideanLin B : _ →ₗ[ℝ] _) x‖ ^ 2) := by
    intro x
    rw [hBM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      neg_one_mul, EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  simp only [key]
  rw [integral_comp_linearMap volume hne fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-1 * ‖y‖ ^ 2),
    GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1), hdetB, hBdet]
  simp [abs_of_nonneg (Real.sqrt_nonneg M.det), smul_eq_mul, div_eq_inv_mul]

/-- The multivariate Gaussian integral over the plain product space `Fin n → ℝ`, whose
`volume` is the same Lebesgue measure. Transported from `integral_exp_neg_quadraticForm`
along `PiLp.volume_preserving_toLp`.

The quadratic form, rather than a norm, is what is written: the ambient norm on `Fin n → ℝ`
is the supremum norm, so `‖·‖` here would state a different — and false — theorem. -/
theorem integral_exp_neg_quadraticForm_pi {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) :
    ∫ v : Fin n → ℝ, Real.exp (-(v ⬝ᵥ M *ᵥ v)) = Real.pi ^ ((n : ℝ) / 2) / √M.det := by
  have h := integral_exp_neg_quadraticForm M hM
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding] at h
  simpa using h

/-- Uncurrying a finite Pi type preserves the product measure: the two product
measures `∏_{i} ∏_{j}` and `∏_{(i,j)}` agree, because a box for the pair index
pulls back to a box for the nested index. This is the finite-product counterpart
of `MeasureTheory.Measure.infinitePi_map_piCurry`, which is stated only for
`infinitePi` and so does not apply to `volume`. -/
theorem measurePreserving_curry_symm (ι κ X : Type*) [Fintype ι] [Fintype κ]
    [MeasureSpace X] [SigmaFinite (volume : Measure X)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ X).symm volume volume where
  measurable := (MeasurableEquiv.curry ι κ X).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have hpre : (MeasurableEquiv.curry ι κ X).symm ⁻¹' Set.univ.pi s
        = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
      ext g
      simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi, Function.uncurry, Prod.forall]
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    exact (Fintype.prod_prod_type fun p => volume (s p)).symm


end GaussianQuadraticIntegrals

/-! ## Replica determinant reduction -/

theorem scalar_block_determinant {R : Type*} [Fintype R] [DecidableEq R]
    (Q : Matrix R R ℝ) (a b : ℝ) (ha : a ≠ 0) :
    (Matrix.fromBlocks (a • (1 : Matrix R R ℝ)) ((-b) • Q)
      ((-b) • Qᵀ) (a • (1 : Matrix R R ℝ))).det =
      (a ^ 2 • (1 : Matrix R R ℝ) - b ^ 2 • (Qᵀ * Q)).det := by
  have hblocks : Matrix.fromBlocks (a • (1 : Matrix R R ℝ)) ((-b) • Q)
      ((-b) • Qᵀ) (a • (1 : Matrix R R ℝ)) =
      Matrix.fromBlocks (a • (1 : Matrix R R ℝ)) 0 0 (1 : Matrix R R ℝ) *
        Matrix.fromBlocks (1 : Matrix R R ℝ) ((-b / a) • Q)
          ((-b) • Qᵀ) (a • (1 : Matrix R R ℝ)) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_zero]
    congr 1
    field_simp [ha]
  rw [hblocks, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one, Matrix.det_smul, Matrix.det_one, mul_one,
    Matrix.det_fromBlocks_one₁₁, ← Matrix.det_smul]
  congr 1
  simp only [smul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1 <;> field_simp

theorem paired_projection_determinant {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype R] [DecidableEq R] (V₀ V₁ : Matrix ι R ℝ)
    (h₀ : V₀ᵀ * V₀ = 1) (h₁ : V₁ᵀ * V₁ = 1) (b : ℝ) (hb : 1 - b ≠ 0) :
    (1 - b • (V₀ * V₀ᵀ + V₁ * V₁ᵀ)).det =
      ((1 - b) ^ 2 • (1 : Matrix R R ℝ) -
        b ^ 2 • ((V₀ᵀ * V₁)ᵀ * (V₀ᵀ * V₁))).det := by
  let V := Matrix.fromCols V₀ V₁
  have hVV : V * Vᵀ = V₀ * V₀ᵀ + V₁ * V₁ᵀ := by
    dsimp only [V]
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]
  rw [← hVV, ← Matrix.smul_mul, Matrix.det_one_sub_mul_comm, Matrix.mul_smul]
  have hgram : Vᵀ * V = Matrix.fromBlocks 1 (V₀ᵀ * V₁) (V₀ᵀ * V₁)ᵀ 1 := by
    dsimp only [V]
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, h₀, h₁,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hgram]
  have hblock : 1 - b • Matrix.fromBlocks (1 : Matrix R R ℝ) (V₀ᵀ * V₁)
      (V₀ᵀ * V₁)ᵀ (1 : Matrix R R ℝ) =
      Matrix.fromBlocks ((1 - b) • (1 : Matrix R R ℝ)) ((-b) • (V₀ᵀ * V₁))
        ((-b) • (V₀ᵀ * V₁)ᵀ) ((1 - b) • (1 : Matrix R R ℝ)) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply]
        <;> split_ifs <;> simp
  rw [hblock]
  exact scalar_block_determinant _ _ _ hb

set_option maxHeartbeats 2000000 in
-- The symbolic determinant expansion includes all 24 permutations of four coordinates.
/-- The binary replica matrices satisfy the tripartite-bipartite determinant product identity. -/
theorem binary_replica_determinant_identity (x y z a b : ℝ) (h : x + y + z = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![z, x + y; x + y, z]
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![x, y + z; y + z, x]
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![y, z + x; z + x, y]
    let Q : Matrix (Fin 4) (Fin 4) ℝ :=
      !![z, y, x, 0; y, z, 0, x; x, 0, z, y; 0, x, y, z]
    (a • 1 - b • (Aᵀ * A)).det * (a • 1 - b • (Bᵀ * B)).det *
      (a • 1 - b • (Cᵀ * C)).det =
      (a - b) ^ 2 * (a • 1 - b • (Qᵀ * Q)).det := by
  dsimp only
  have hz : z = 1 - x - y := by linarith
  simp only [hz, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.succAbove, Fin.sum_univ_zero]
  simp
  ring

/-- A square root of a quadratic polynomial has the expected linear scaling limit. -/
theorem sqrt_quadratic_ratio_limit (b c : ℝ) (hb : 0 ≤ b) (hbc : 0 ≤ b + c) :
    Tendsto (fun a : ℝ => Real.sqrt (b * a ^ 2 + c) / a) atTop (𝓝 (Real.sqrt b)) := by
  have ht : Tendsto (fun a : ℝ => b + c * (a⁻¹) ^ 2) atTop (𝓝 b) := by
    convert (tendsto_const_nhds (x := b)).add
      ((tendsto_const_nhds (x := c)).mul (tendsto_inv_atTop_zero.pow 2)) using 1
    simp
  have heq : (fun a : ℝ => Real.sqrt (b * a ^ 2 + c) / a) =ᶠ[atTop]
      (fun a : ℝ => Real.sqrt (b + c * (a⁻¹) ^ 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have ha0 : 0 < a := by linarith
    have hq : 0 ≤ b * a ^ 2 + c := by nlinarith [mul_nonneg hb (show 0 ≤ a ^ 2 - 1 by nlinarith)]
    calc
      Real.sqrt (b * a ^ 2 + c) / a = Real.sqrt ((b * a ^ 2 + c) / a ^ 2) := by
        rw [Real.sqrt_div hq, Real.sqrt_sq ha0.le]
      _ = Real.sqrt (b + c * (a⁻¹) ^ 2) := by congr 1; field_simp
  exact ht.sqrt.congr' heq.symm

set_option maxHeartbeats 800000 in
-- Rationalization combines two square-root identities before taking limits.
/-- The symmetric Gaussian parameter has a positive quadratic scaling limit. -/
theorem symmetric_parameter_scaled_limit (N : ℝ) (hN : 2 < N) :
    let e (a : ℝ) := ((a ^ 2 - 1) * (N - 2) - Real.sqrt (a ^ 2 - 1) *
      Real.sqrt ((a ^ 2 - 1) * N ^ 2 + 4 * (N - 1))) / (2 * a * (N - 1))
    Tendsto (fun a : ℝ => a ^ 2 * ((a + (N - 1) * e a) / (a - e a))) atTop
      (𝓝 ((N - 1) / N ^ 2)) := by
  dsimp only
  let e (a : ℝ) := ((a ^ 2 - 1) * (N - 2) - Real.sqrt (a ^ 2 - 1) *
    Real.sqrt ((a ^ 2 - 1) * N ^ 2 + 4 * (N - 1))) / (2 * a * (N - 1))
  let s (a : ℝ) := Real.sqrt (a ^ 2 - 1)
  let t (a : ℝ) := Real.sqrt ((a ^ 2 - 1) * N ^ 2 + 4 * (N - 1))
  have hnpos : 0 < N := by linarith
  have hn1pos : 0 < N - 1 := by linarith
  have hn0 : N ≠ 0 := by linarith
  have hn1 : N - 1 ≠ 0 := by linarith
  have hs : Tendsto (fun a => s a / a) atTop (𝓝 1) := by
    simpa only [s, one_mul, ← sub_eq_add_neg, Real.sqrt_one] using
      sqrt_quadratic_ratio_limit 1 (-1) (by norm_num) (by norm_num)
  have ht : Tendsto (fun a => t a / a) atTop (𝓝 N) := by
    have hh := sqrt_quadratic_ratio_limit (N ^ 2) (4 * (N - 1) - N ^ 2) (sq_nonneg N) (by linarith)
    rw [Real.sqrt_sq (by linarith : 0 ≤ N)] at hh
    convert hh using 1
    funext a
    dsimp only [t]
    congr 2
    ring
  have heq : (fun a => e a / a) =ᶠ[atTop]
      (fun a => ((1 - (a⁻¹) ^ 2) * (N - 2) - (s a / a) * (t a / a)) / (2 * (N - 1))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have ha0 : a ≠ 0 := by linarith
    dsimp only [e,s,t]
    field_simp
  have he : Tendsto (fun a => e a / a) atTop (𝓝 (-1 / (N - 1))) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_inv_atTop_zero.pow 2)).mul_const (N - 2)).sub (hs.mul ht) |>.div_const (2 * (N - 1))
    convert hh.congr' heq.symm using 1
    congr 1
    field_simp
    ring
  have hd : Tendsto (fun a => (a - e a) / a) atTop (𝓝 (N / (N - 1))) := by
    have heq : (fun a => (a - e a) / a) =ᶠ[atTop] (fun a => 1 - e a / a) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
      rw [sub_div, div_self (by linarith : a ≠ 0)]
    convert ((tendsto_const_nhds (x := (1 : ℝ))).sub he).congr' heq.symm using 1
    congr 1
    field_simp
    ring
  have hsmall : (fun a => a ^ 2 * ((a + (N - 1) * e a) / (a - e a))) =ᶠ[atTop]
      (fun a => ((t a / a) - (N - 2) * (s a / a)) /
        ((N * (s a / a) + t a / a) * ((a - e a) / a))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hd.eventually_const_lt (show 0 < N / (N - 1) by positivity)] with a ha hda
    have ha0 : 0 < a := by linarith
    have hd0 : a - e a ≠ 0 := by
      exact (div_pos_iff.mp hda).elim (fun h => h.1.ne')
        (fun h => False.elim (not_lt_of_ge ha0.le h.2))
    have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
    have hs2 : s a ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have ht2 : t a ^ 2 = (a ^ 2 - 1) * N ^ 2 + 4 * (N - 1) :=
      Real.sq_sqrt (by positivity)
    have ht0 : 0 < t a := Real.sqrt_pos.mpr (by positivity)
    have hst : s a * N + t a ≠ 0 := by dsimp only [s]; positivity
    have hid : (2 * a ^ 2 + (a ^ 2 - 1) * (N - 2) - s a * t a) *
        (s a * N + t a) = 2 * (t a - (N - 2) * s a) := by
      linear_combination -(N * t a) * hs2 - s a * ht2
    have hex : (a + (N - 1) * e a) * a =
        (2 * a ^ 2 + (a ^ 2 - 1) * (N - 2) - s a * t a) / 2 := by
      dsimp only [e,s,t]
      field_simp [hn1, ha0.ne']
      ring
    have hrat : (a + (N - 1) * e a) * (a * (s a * N + t a)) =
        t a - (N - 2) * s a := by
      rw [← mul_assoc, hex]
      linear_combination (1 / 2 : ℝ) * hid
    have hnorm : N * (s a / a) + t a / a = (s a * N + t a) / a := by ring
    rw [hnorm]
    apply (eq_div_iff (mul_ne_zero (div_ne_zero hst ha0.ne') (div_ne_zero hd0 ha0.ne'))).mpr
    field_simp [ha0.ne',hd0]
    linear_combination hrat
  have hh := ((ht.sub (hs.const_mul (N - 2))).div
    (((hs.const_mul N).add ht).mul hd) (by positivity : (N * 1 + N) * (N / (N - 1)) ≠ 0))
  convert hh.congr' hsmall.symm using 1
  congr 1
  field_simp
  ring

/-- A positive quadratic scaling limit fixes the leading logarithmic term. -/
theorem log_equivalent_of_scaled_limit {ε : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (h : Tendsto (fun a => a ^ 2 * ε a) atTop (𝓝 C)) :
    Asymptotics.IsEquivalent atTop (fun a => Real.log (ε a))
      (fun a => -2 * Real.log a) := by
  have hb := Asymptotics.isBigO_const_of_tendsto (h.log hC.ne') (one_ne_zero : (1 : ℝ) ≠ 0)
  have ho := hb.trans_isLittleO (Real.isLittleO_const_log_atTop (c := 1))
  have heq : (fun a => Real.log (a ^ 2 * ε a)) =ᶠ[atTop]
      (fun a => Real.log (ε a) - (-2 * Real.log a)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), h.eventually_const_lt hC] with a ha hp
    have he : ε a ≠ 0 := (mul_pos_iff.mp hp).elim (fun hh => hh.2.ne') (fun hh => hh.2.ne)
    rw [Real.log_mul (pow_ne_zero _ ha.ne') he, Real.log_pow]
    ring
  exact (ho.const_mul_right (by norm_num : (-2 : ℝ) ≠ 0)).congr' heq Filter.EventuallyEq.rfl

/-- A stochastic matrix with positive entries along transitive twists
has only constant fixed vectors. -/
theorem stochastic_twist_kernel {R K : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
    (M : Matrix R R ℝ) (hM : M ∈ Matrix.rowStochastic ℝ R)
    (g : K → Equiv.Perm R) (hpos : ∀ k r, 0 < M r (g k r))
    (htrans : ∀ r s, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) r s)
    (x : R → ℝ) : M *ᵥ x = x ↔ ∃ c, x = fun _ => c := by
  classical
  constructor
  · intro hx
    obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
    have hmax : ∀ s, x s ≤ x r := fun s => hr s (Finset.mem_univ s)
    have hstep (i j : R) (hi : x i = x r) (hij : 0 < M i j) : x j = x r := by
      have hsum : ∑ s, M i s * (x r - x s) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        rw [Matrix.sum_row_of_mem_rowStochastic hM, one_mul]
        change x r - (M *ᵥ x) i = 0
        rw [hx, hi, sub_self]
      have ht := (Finset.sum_eq_zero_iff_of_nonneg
        (fun s (_ : s ∈ Finset.univ) =>
          mul_nonneg (hM.1 _ _) (sub_nonneg.mpr (hmax s)))).mp hsum j (Finset.mem_univ j)
      rcases mul_eq_zero.mp ht with hz | hz
      · exact False.elim (hij.ne' hz)
      · linarith
    refine ⟨x r, funext fun s => ?_⟩
    have hp := htrans r s
    induction hp with
    | refl => rfl
    | @tail j k hj hstepRel ih =>
      rcases hstepRel with ⟨k, rfl⟩
      exact hstep j _ ih (hpos k j)
  · rintro ⟨c, rfl⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_mul,
      Matrix.sum_row_of_mem_rowStochastic hM, one_mul]

/-- A transitive permutation average containing the identity
has a Gram matrix that fixes exactly the constants. -/
theorem permutation_average_kernel {R K : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype K] (g : K → Equiv.Perm R) (k₀ : K) (hid : g k₀ = 1)
    (htrans : ∀ r s, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) r s) :
    let Q : Matrix R R ℝ := Matrix.of fun i j =>
      ∑ k, if i = g k j then (Fintype.card K : ℝ)⁻¹ else 0
    (Qᵀ * Q ∈ Matrix.rowStochastic ℝ R) ∧
      (∀ x : R → ℝ, (Qᵀ * Q) *ᵥ x = x ↔ ∃ c, x = fun _ => c) := by
  classical
  dsimp only
  let Q : Matrix R R ℝ := Matrix.of fun i j =>
    ∑ k, if i = g k j then (Fintype.card K : ℝ)⁻¹ else 0
  have : Nonempty K := ⟨k₀⟩
  have hc : 0 < (Fintype.card K : ℝ)⁻¹ := by positivity
  have hnonneg : ∀ i j, 0 ≤ Q i j := by
    intro i j
    exact Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have hcol : ∀ j, ∑ i, Q i j = 1 := by
    intro j
    dsimp only [Q, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp [Fintype.card_ne_zero]
  have hrow : ∀ i, ∑ j, Q i j = 1 := by
    intro i
    dsimp only [Q, Matrix.of_apply]
    rw [Finset.sum_comm]
    have he (k : K) : ∑ j, (if i = g k j then (Fintype.card K : ℝ)⁻¹ else 0) =
        (Fintype.card K : ℝ)⁻¹ := by
      simp_rw [← (g k).symm_apply_eq]
      simp
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  have hQ : Q ∈ Matrix.rowStochastic ℝ R := Matrix.mem_rowStochastic_iff_sum.mpr ⟨hnonneg, hrow⟩
  have hQt : Qᵀ ∈ Matrix.rowStochastic ℝ R :=
    Matrix.mem_rowStochastic_iff_sum.mpr ⟨fun i j => hnonneg j i, hcol⟩
  have hM : Qᵀ * Q ∈ Matrix.rowStochastic ℝ R := (Matrix.rowStochastic ℝ R).mul_mem hQt hQ
  have hentry (k : K) (i : R) : 0 < Q (g k i) i := by
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun l => if g k i = g l i then (Fintype.card K : ℝ)⁻¹ else 0)
      (fun l _ => by split_ifs <;> positivity) (Finset.mem_univ k)
    exact hc.trans_le (by simpa only [Q, Matrix.of_apply, eq_self, ite_true] using hle)
  have hdiag (i : R) : 0 < Q i i := by simpa [hid] using hentry k₀ i
  have hpos (k : K) (i : R) : 0 < (Qᵀ * Q) i (g k i) := by
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => Q j i * Q j (g k i))
      (fun j _ => mul_nonneg (hnonneg _ _) (hnonneg _ _)) (Finset.mem_univ (g k i))
    exact (mul_pos (hentry k i) (hdiag (g k i))).trans_le hle
  exact ⟨hM, fun x => stochastic_twist_kernel _ hM g hpos htrans x⟩

/-- A Hermitian stochastic matrix with constant fixed space
has a simple vanishing determinant factor. -/
theorem stochastic_determinant_factor {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
    (G : Matrix R R ℝ) (hG : G.IsHermitian) (hM : G ∈ Matrix.rowStochastic ℝ R)
    (hker : ∀ x : R → ℝ, G *ᵥ x = x ↔ ∃ c, x = fun _ => c) :
    ∃ D : ℝ → ℝ, Continuous D ∧ 0 < D 0 ∧ ∀ e : ℝ,
      (((1 + e) / 2) ^ 2 • (1 : Matrix R R ℝ) - ((1 - e) / 2) ^ 2 • G).det = e * D e := by
  classical
  have hspec : (1 : ℝ) ∈ spectrum ℝ G := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : R → ℝ))
    refine ⟨?_, one_ne_zero⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, one_smul]
    exact hM.2
  obtain ⟨i₀, hi₀⟩ := hG.spectrum_real_eq_range_eigenvalues ▸ hspec
  have hupper (i : R) : hG.eigenvalues i ≤ 1 := by
    have heig : Module.End.HasEigenvalue G.toLin' (hG.eigenvalues i) := by
      apply Module.End.HasEigenvalue.of_mem_spectrum
      rw [Matrix.spectrum_toLin']
      exact hG.eigenvalues_mem_spectrum_real i
    obtain ⟨r, hr⟩ := eigenvalue_mem_ball heig
    simp only [Metric.mem_closedBall, Real.dist_eq] at hr
    have hs : ∑ j ∈ Finset.univ.erase r, ‖G r j‖ = 1 - G r r := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hM.1 _ _)]
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ r), Matrix.sum_row_of_mem_rowStochastic hM]
    rw [hs] at hr
    linarith [le_abs_self (hG.eigenvalues i - G r r)]
  have huniq (i : R) (hi : hG.eigenvalues i = 1) : i = i₀ := by
    have hv (j : R) (hj : hG.eigenvalues j = 1) :
        ∃ c, (⇑(hG.eigenvectorBasis j) : R → ℝ) = fun _ => c := by
      apply (hker _).mp
      rw [hG.mulVec_eigenvectorBasis, hj, one_smul]
    obtain ⟨c, hc⟩ := hv i hi
    obtain ⟨d, hd⟩ := hv i₀ hi₀
    have hd0 : d ≠ 0 := by
      intro hz
      have hh : hG.eigenvectorBasis i₀ = 0 := by ext r; simp [hd, hz]
      exact hG.eigenvectorBasis.toBasis.ne_zero i₀ hh
    apply hG.eigenvectorBasis.toBasis.linearIndependent.eq_of_smul_apply_eq_smul_apply d c i i₀ hd0
    ext r
    simp [hc, hd, mul_comm]
  have hprod (e : ℝ) :
      (((1 + e) / 2) ^ 2 • (1 : Matrix R R ℝ) - ((1 - e) / 2) ^ 2 • G).det =
        ∏ i, (((1 + e) / 2) ^ 2 - ((1 - e) / 2) ^ 2 * hG.eigenvalues i) := by
    let φ := Unitary.conjStarAlgAut ℝ (Matrix R R ℝ) hG.eigenvectorUnitary
    have hφ : φ (Matrix.diagonal hG.eigenvalues) = G := by
      simpa only [φ, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
        hG.spectral_theorem.symm
    have hd : Matrix.diagonal (fun i => ((1 + e) / 2) ^ 2 -
        ((1 - e) / 2) ^ 2 * hG.eigenvalues i) =
        ((1 + e) / 2) ^ 2 • (1 : Matrix R R ℝ) -
          ((1 - e) / 2) ^ 2 • Matrix.diagonal hG.eigenvalues := by
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> simp
    have he : φ (Matrix.diagonal (fun i => ((1 + e) / 2) ^ 2 -
        ((1 - e) / 2) ^ 2 * hG.eigenvalues i)) =
        ((1 + e) / 2) ^ 2 • (1 : Matrix R R ℝ) - ((1 - e) / 2) ^ 2 • G := by
      rw [hd, map_sub, map_smul, map_smul, map_one, hφ]
    rw [← he]
    simp only [φ, Unitary.conjStarAlgAut_apply, Matrix.det_mul]
    rw [mul_assoc, mul_comm (Matrix.det (Matrix.diagonal _)), ← mul_assoc,
      ← Matrix.det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one,
      one_mul, Matrix.det_diagonal]
  let D (e : ℝ) := ∏ i ∈ Finset.univ.erase i₀,
    (((1 + e) / 2) ^ 2 - ((1 - e) / 2) ^ 2 * hG.eigenvalues i)
  refine ⟨D, ?_, ?_, ?_⟩
  · dsimp only [D]; fun_prop
  · apply Finset.prod_pos
    intro i hi
    have hne : hG.eigenvalues i ≠ 1 := fun h => (Finset.mem_erase.mp hi).1 (huniq i h)
    have hlt : hG.eigenvalues i < 1 := lt_of_le_of_ne (hupper i) hne
    norm_num
    linarith
  · intro e
    rw [hprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    change (((1 + e) / 2) ^ 2 - ((1 - e) / 2) ^ 2 * hG.eigenvalues i₀) * D e = e * D e
    rw [hi₀]
    congr 1
    ring

/-- Transitive permutation averages give a positive continuous residual determinant. -/
theorem permutation_average_determinant_factor {R K : Type*}
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype K] (g : K → Equiv.Perm R) (k₀ : K) (hid : g k₀ = 1)
    (htrans : ∀ r s, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) r s) :
    let Q : Matrix R R ℝ := Matrix.of fun i j =>
      ∑ k, if i = g k j then (Fintype.card K : ℝ)⁻¹ else 0
    ∃ D : ℝ → ℝ, Continuous D ∧ 0 < D 0 ∧ ∀ e : ℝ,
      (((1 + e) / 2) ^ 2 • (1 : Matrix R R ℝ) - ((1 - e) / 2) ^ 2 • (Qᵀ * Q)).det = e * D e := by
  dsimp only
  have h := permutation_average_kernel g k₀ hid htrans
  let Q : Matrix R R ℝ := Matrix.of fun i j =>
    ∑ k, if i = g k j then (Fintype.card K : ℝ)⁻¹ else 0
  have hH : (Qᵀ * Q).IsHermitian := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial Q]
    exact Matrix.isHermitian_conjTranspose_mul_self Q
  exact stochastic_determinant_factor (Qᵀ * Q) hH h.1 h.2

/-- A family containing a cyclic shift reaches every replica on a finite cycle. -/
theorem cyclic_twists_transitive {K : Type*} (n : ℕ) (g : K → Equiv.Perm (Fin n))
    (k : K) (hk : g k = finRotate n) :
    ∀ r s, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) r s := by
  intro r s
  have : NeZero n := r.neZero
  have hit (t : ℕ) : Relation.ReflTransGen (fun i j => ∃ k, g k i = j) r ((finRotate n)^[t] r) := by
    induction t with
    | zero => exact .refl
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ih.tail ⟨k, by rw [hk]⟩
  have he : (finRotate n)^[(s - r).val] r = s := by
    rw [← congr_fun (finCycle_eq_finRotate_iterate (k := s - r)) r]
    simp [finCycle_apply]
  rw [← he]
  exact hit _

/-- Two coordinate shifts connect a rectangular replica torus. -/
theorem torus_twists_transitive {K : Type*} (n m : ℕ)
    (g : K → Equiv.Perm (Fin n × Fin m)) (k₁ k₂ : K)
    (h₁ : g k₁ = Equiv.prodCongr (finRotate n) (Equiv.refl (Fin m)))
    (h₂ : g k₂ = Equiv.prodCongr (Equiv.refl (Fin n)) (finRotate m)) :
    ∀ r s, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) r s := by
  intro r s
  have hA : ∀ u v : Fin n, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) (u, r.2) (v, r.2) := by
    intro u v
    have hh := cyclic_twists_transitive n (fun _ : Unit => finRotate n) () rfl u v
    induction hh with
    | refl => exact .refl
    | @tail a b ha hab ih =>
      rcases hab with ⟨_, rfl⟩
      exact ih.tail ⟨k₁, by simp [h₁]⟩
  have hB : ∀ u v : Fin m, Relation.ReflTransGen (fun i j => ∃ k, g k i = j) (s.1, u) (s.1, v) := by
    intro u v
    have hh := cyclic_twists_transitive m (fun _ : Unit => finRotate m) () rfl u v
    induction hh with
    | refl => exact .refl
    | @tail a b ha hab ih =>
      rcases hab with ⟨_, rfl⟩
      exact ih.tail ⟨k₂, by simp [h₂]⟩
  exact (hA r.1 s.1).trans (hB r.2 s.2)

/-- Four simple replica determinants give the large-squeezing entropy coefficient. -/
theorem replica_entropy_asymptotic (n : ℕ) (hn : 2 < n) (ε : ℝ → ℝ) (C : ℝ)
    (hC : 0 < C) (hscale : Tendsto (fun a => a ^ 2 * ε a) atTop (𝓝 C))
    (D : Fin 4 → ℝ → ℝ) (hD : ∀ i, Continuous (D i)) (hpos : ∀ i, 0 < D i 0) :
    Asymptotics.IsEquivalent atTop (fun a =>
      (1 / (1 - (n : ℝ))) * (1 / (n : ℝ)) *
        Real.log (Real.sqrt (ε a ^ (n ^ 2) / (ε a * D 0 (ε a)))) -
      (1 / 2) * ((1 / (1 - (n : ℝ))) *
        Real.log (Real.sqrt (ε a ^ n / (ε a * D 1 (ε a)))) +
        (1 / (1 - (n : ℝ))) * Real.log (Real.sqrt (ε a ^ n / (ε a * D 2 (ε a)))) +
        (1 / (1 - (n : ℝ))) * Real.log (Real.sqrt (ε a ^ n / (ε a * D 3 (ε a))))))
      (fun a => (2 - (n : ℝ)) / (2 * (n : ℝ)) * Real.log a) := by
  have hnreal : 2 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : 1 - (n : ℝ) ≠ 0 := by linarith
  have hn1' : (n : ℝ) - 1 ≠ 0 := by linarith
  have he0 : Tendsto ε atTop (𝓝 0) := by
    have hh := hscale.mul (tendsto_inv_atTop_zero.pow 2)
    simp only [zero_pow (by omega : 2 ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    field_simp
  have hepos : ∀ᶠ a in atTop, 0 < ε a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hscale.eventually_const_lt hC] with a ha he
    exact (mul_pos_iff.mp he).elim (fun h => h.2)
      (fun h => False.elim (not_lt_of_ge (sq_nonneg a) h.1))
  have hlim (i : Fin 4) : Tendsto (fun a => Real.log (D i (ε a))) atTop (𝓝 (Real.log (D i 0))) :=
    ((hD i).continuousAt.tendsto.comp he0).log (hpos i).ne'
  let R (a : ℝ) := Real.log (D 0 (ε a)) / (2 * (n : ℝ) * ((n : ℝ) - 1)) -
    (Real.log (D 1 (ε a)) + Real.log (D 2 (ε a)) + Real.log (D 3 (ε a))) / (4 * ((n : ℝ) - 1))
  have hR : Tendsto R atTop (𝓝 (Real.log (D 0 0) / (2 * (n : ℝ) * ((n : ℝ) - 1)) -
      (Real.log (D 1 0) + Real.log (D 2 0) + Real.log (D 3 0)) / (4 * ((n : ℝ) - 1)))) :=
    ((hlim 0).div_const _).sub ((((hlim 1).add (hlim 2)).add (hlim 3)).div_const _)
  have hsmall := (Asymptotics.isBigO_const_of_tendsto hR
    (one_ne_zero : (1 : ℝ) ≠ 0)).trans_isLittleO
    (Real.isLittleO_const_log_atTop (c := 1))
  have hcoef0 : (2 - (n : ℝ)) / (2 * (n : ℝ)) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hsmall' := hsmall.const_mul_right hcoef0
  have hlog := log_equivalent_of_scaled_limit hC hscale
  have hleading := (Asymptotics.IsEquivalent.refl (u := fun _ : ℝ =>
    ((n : ℝ) - 2) / (4 * (n : ℝ))) (l := atTop)).mul hlog
  change Asymptotics.IsEquivalent atTop
    (fun a => ((n : ℝ) - 2) / (4 * (n : ℝ)) * Real.log (ε a))
    (fun a => ((n : ℝ) - 2) / (4 * (n : ℝ)) * (-2 * Real.log a)) at hleading
  have hcoef : (fun a : ℝ => ((n : ℝ) - 2) / (4 * (n : ℝ)) * (-2 * Real.log a)) =
      (fun a => (2 - (n : ℝ)) / (2 * (n : ℝ)) * Real.log a) := by funext a; ring
  rw [hcoef] at hleading
  have hz (m : ℕ) (e d : ℝ) (he : 0 < e) (hd : 0 < d) :
      Real.log (Real.sqrt (e ^ m / (e * d))) = ((m : ℝ) - 1) / 2 * Real.log e - Real.log d / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_div (pow_pos he _).ne' (mul_pos he hd).ne',
      Real.log_pow, Real.log_mul he.ne' hd.ne']
    ring
  apply (hleading.add hsmall').congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hepos,
    ((hD 0).continuousAt.tendsto.comp he0).eventually_const_lt (hpos 0),
    ((hD 1).continuousAt.tendsto.comp he0).eventually_const_lt (hpos 1),
    ((hD 2).continuousAt.tendsto.comp he0).eventually_const_lt (hpos 2),
    ((hD 3).continuousAt.tendsto.comp he0).eventually_const_lt (hpos 3)] with a he h0 h1 h2 h3
  dsimp only [Pi.add_apply, Pi.sub_apply, R]
  dsimp only [Function.comp_apply] at h0 h1 h2 h3
  rw [hz (n ^ 2) (ε a) (D 0 (ε a)) he h0, hz n (ε a) (D 1 (ε a)) he h1,
    hz n (ε a) (D 2 (ε a)) he h2, hz n (ε a) (D 3 (ε a)) he h3]
  simp only [Nat.cast_pow]
  field_simp [hn0, hn1, hn1']
  ring

end D5.S3.Quantum.Entanglement.GaussianReplicaReduction
