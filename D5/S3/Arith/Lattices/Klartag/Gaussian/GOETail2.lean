/- GID: D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Gaussian/GOETail2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian moments, independence and operator norm tails. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail

open D5.S3.Arith.Lattices.Klartag.Gaussian

namespace D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail

open MeasureTheory
open ProbabilityTheory
open Module
open Set
open Finset
open scoped ENNReal NNReal RealInnerProductSpace Matrix

/-- A real random variable whose law is `N(0, v)` has a sub-Gaussian MGF with parameter `v`.
Mathlib has `mgf_gaussianReal` and `integrable_exp_mul_gaussianReal` but no bridge to
`HasSubgaussianMGF`, which occurs in no file other than `Probability/Moments/SubGaussian.lean`. -/
theorem hasSubgaussianMGF_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    HasSubgaussianMGF X v P := by
  refine ⟨?_, ?_⟩
  · intro t
    have h1 : Integrable (fun z : ℝ => Real.exp (t * z)) (P.map X) := by
      rw [hX.map_eq]; exact integrable_exp_mul_gaussianReal t
    rwa [integrable_map_measure (by fun_prop) hX.aemeasurable] at h1
  · intro t
    exact le_of_eq (by rw [mgf_gaussianReal hX t]; simp)

/-- A nondegenerate Gaussian map equality certifies a.e. measurability because
the Gaussian law has no atoms, while the fallback pushforward is a Dirac mass. -/
theorem hasSubgaussianMGF_of_map_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : P.map X = gaussianReal 0 v) (_hv : v ≠ 0) :
    HasSubgaussianMGF X v P := by
  have hXm : AEMeasurable X P := by
    rcases eq_or_ne P 0 with rfl | hP
    · exact aemeasurable_zero_measure
    by_contra hnot
    have hdirac := Measure.map_of_not_aemeasurable_of_ne_zero hnot hP
    haveI : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal _hv
    have hsingle := congrArg
      (fun μ : Measure ℝ => μ {(Classical.ofNonempty : ℝ)}) (hX.symm.trans hdirac)
    simpa using hsingle
  exact hasSubgaussianMGF_of_hasLaw_gaussianReal ⟨hXm, hX⟩

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u v : Fin n → ℝ) : u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (u b * v a) * hA.apply a b

/-- `toEuclideanCLM` of a symmetric real matrix is self-adjoint, in the elementary form
`D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.opNorm_le_of_net` consumes. -/
theorem inner_toEuclideanCLM_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, y⟫ = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  exact dotProduct_mulVec_comm hA _ _

/-- `B + Bᵀ` is symmetric. -/
theorem isSymm_add_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : (B + Bᵀ).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_transpose]
  exact add_comm _ _

/-- The quadratic form of the symmetrised matrix, as a linear form in the independent entries
of `B`. -/
noncomputable def quadForm {Ω : Type*} {n : ℕ} (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) * B ω p.1 p.2

/-- **Step 3a.** The quadratic form of `B + Bᵀ` is a sum over the *full* product
`Fin n × Fin n` of the independent entries of `B`, with coefficients `2 x_i x_j`. No `i ≤ j`
filter and no `Prod.swap` reindexing: the only reindexing is one `Finset.sum_comm`. -/
theorem inner_symmetrized {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (B + Bᵀ) x, x⟫
      = ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) * B p.1 p.2 := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.transpose_apply, Finset.mul_sum]
  have expand : ∀ i : Fin n, ∑ j, x i * ((B i j + B j i) * x j)
      = (∑ j, x i * B i j * x j) + (∑ j, x i * B j i * x j) := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => expand i, Finset.sum_add_distrib]
  have swap : ∑ i, ∑ j, x i * B j i * x j = ∑ i, ∑ j, x i * B i j * x j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [swap, ← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A unit vector of `EuclideanSpace ℝ (Fin n)` has coordinate squares summing to `1`. -/
theorem sum_sq_coord_eq_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    ∑ i, x i ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (𝕜 := ℝ) x
  rw [hx] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  linarith [h]

/-- **Step 3c.** For a unit vector `x`, the linear form `∑ p, (2 x_{p.1} x_{p.2}) B_{p.1 p.2}`
in the independent entries of `B` is sub-Gaussian with parameter `4c`. The coefficient bound is
`D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.sum_sq_coeff_le`; the closure properties are `HasSubgaussianMGF.const_mul` and
`.sum_of_iIndepFun`, and the parameter is relaxed by `D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.hasSubgaussianMGF_mono`. -/
theorem hasSubgaussianMGF_quadForm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (B : Ω → Matrix (Fin n) (Fin n) ℝ) {c : ℝ≥0}
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => B ω i j) c P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    HasSubgaussianMGF (quadForm B x) (4 * c) P := by
  classical
  have hindep' : iIndepFun
      (fun (p : Fin n × Fin n) (ω : Ω) => (2 * x p.1 * x p.2) * B ω p.1 p.2) P :=
    hindep.comp (fun p z => (2 * x p.1 * x p.2) * z)
      (fun p => measurable_const_mul (2 * x p.1 * x p.2))
  have hsubG : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
      HasSubgaussianMGF (fun ω => (2 * x p.1 * x p.2) * B ω p.1 p.2)
        (⟨(2 * x p.1 * x p.2) ^ 2, sq_nonneg _⟩ * c) P :=
    fun p _ => (hsub p.1 p.2).const_mul (2 * x p.1 * x p.2)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep' hsubG
  refine hasSubgaussianMGF_mono hsum ?_
  have hcoeff : ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) ^ 2 ≤ 4 :=
    sum_sq_coeff_le x (sum_sq_coord_eq_one x hx)
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  have hcoe : ∀ p : Fin n × Fin n,
      ((⟨(2 * x p.1 * x p.2) ^ 2, sq_nonneg _⟩ * c : ℝ≥0) : ℝ)
        = (2 * x p.1 * x p.2) ^ 2 * (c : ℝ) := fun _ => rfl
  simp only [hcoe]
  rw [← Finset.sum_mul]
  have h4 : ((4 * c : ℝ≥0) : ℝ) = 4 * (c : ℝ) := by push_cast; ring
  rw [h4]
  exact mul_le_mul_of_nonneg_right hcoeff c.coe_nonneg

/-- **The tail, with `C = 12`.** Steps 4 (union bound over the `ε = 1/4` net), 5 (the constant),
6 (assembly) and 8 (`n = 0`). -/
theorem opNormTail_symmetrized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (B : Ω → Matrix (Fin n) (Fin n) ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => B ω i j) c P)
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 12 * Real.sqrt c * s * Real.sqrt n ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  classical
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hcR : (0 : ℝ) < (c : ℝ) := hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hset : {ω : Ω | 12 * Real.sqrt (c : ℝ) * s * Real.sqrt ((0 : ℕ) : ℝ) ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} = Set.univ := by
      ext ω; simp
    rw [hset]
    have huniv : P.real (Set.univ : Set Ω) = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [huniv]
    simp

  have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  obtain ⟨N, hN1, hN2, hN3⟩ :=
    exists_net (E := EuclideanSpace ℝ (Fin n)) volume (ε := 1 / 4) (by norm_num)
  rw [finrank_euclideanSpace_fin] at hN2

  obtain ⟨z, hz⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hz1 : ‖(‖z‖⁻¹ • z : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
      inv_mul_cancel₀ hzn]
  obtain ⟨y₀, hy₀, -⟩ := hN3 _ hz1
  have hNne : N.Nonempty := ⟨y₀, hy₀⟩
  set u : ℝ := 6 * Real.sqrt (c : ℝ) * s * Real.sqrt (n : ℝ) with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hs0.le)
      (Real.sqrt_nonneg _)
  have hQsub : ∀ x ∈ N, HasSubgaussianMGF (quadForm B x) (4 * c) P := fun x hx =>
    hasSubgaussianMGF_quadForm B hindep hsub x (hN1 x hx)

  have hcontain : {ω | 12 * Real.sqrt (c : ℝ) * s * Real.sqrt (n : ℝ) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ⊆ ⋃ x ∈ N, {ω | u ≤ |quadForm B x ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    have hM0 : 0 ≤ N.sup' hNne (fun y => |quadForm B y ω|) :=
      le_trans (abs_nonneg (quadForm B y₀ ω))
        (Finset.le_sup' (fun y => |quadForm B y ω|) hy₀)
    have hbound : ∀ y ∈ N, |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ) y, y⟫|
        ≤ N.sup' hNne (fun y => |quadForm B y ω|) := by
      intro y hy
      rw [inner_symmetrized]
      exact Finset.le_sup' (fun y => |quadForm B y ω|) hy
    have hnet := opNorm_le_of_net (E := EuclideanSpace ℝ (Fin n))
      (by norm_num : (0 : ℝ) < 1 / 4) N hN1 hN3 _
      (inner_toEuclideanCLM_symm (isSymm_add_transpose (B ω))) hM0 hbound
    have key : u ≤ N.sup' hNne (fun y => |quadForm B y ω|) := by rw [hu]; linarith
    exact (Finset.le_sup'_iff hNne).mp key

  have hterm : ∀ x ∈ N, P.real {ω | u ≤ |quadForm B x ω|}
      ≤ 2 * Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ))) := by
    intro x hx
    have hsplit : {ω | u ≤ |quadForm B x ω|}
        ⊆ {ω | u ≤ quadForm B x ω} ∪ {ω | u ≤ (-quadForm B x) ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      rcases abs_cases (quadForm B x ω) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hω; exact Or.inl hω
      · rw [h1] at hω; exact Or.inr hω
    calc P.real {ω | u ≤ |quadForm B x ω|}
        ≤ P.real ({ω | u ≤ quadForm B x ω} ∪ {ω | u ≤ (-quadForm B x) ω}) :=
          measureReal_mono hsplit (measure_ne_top P _)
      _ ≤ P.real {ω | u ≤ quadForm B x ω} + P.real {ω | u ≤ (-quadForm B x) ω} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ)))
            + Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ))) :=
          add_le_add ((hQsub x hx).measure_ge_le hu0) ((hQsub x hx).neg.measure_ge_le hu0)
      _ = 2 * Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ))) := by ring

  have hexp : -u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ)) = -(9 / 2 * s ^ 2 * n) := by
    have h1 : Real.sqrt (c : ℝ) ^ 2 = (c : ℝ) := Real.sq_sqrt c.coe_nonneg
    have h2 : Real.sqrt ((n : ℕ) : ℝ) ^ 2 = ((n : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have h3 : u ^ 2 = 36 * (c : ℝ) * s ^ 2 * n := by
      rw [hu, show (6 * Real.sqrt (c : ℝ) * s * Real.sqrt ((n : ℕ) : ℝ)) ^ 2
        = 36 * Real.sqrt (c : ℝ) ^ 2 * s ^ 2 * Real.sqrt ((n : ℕ) : ℝ) ^ 2 by ring, h1, h2]
    rw [h3]
    have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcR
    push_cast
    field_simp
    ring

  calc P.real {ω | 12 * Real.sqrt (c : ℝ) * s * Real.sqrt (n : ℝ) ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖}
      ≤ P.real (⋃ x ∈ N, {ω | u ≤ |quadForm B x ω|}) :=
        measureReal_mono hcontain (measure_ne_top P _)
    _ ≤ ∑ x ∈ N, P.real {ω | u ≤ |quadForm B x ω|} := measureReal_biUnion_finset_le N _
    _ ≤ ∑ _x ∈ N, 2 * Real.exp (-(9 / 2 * s ^ 2 * n)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [← hexp]
        exact hterm x hx
    _ = (N.card : ℝ) * (2 * Real.exp (-(9 / 2 * s ^ 2 * n))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 : ℝ) ^ n * (2 * Real.exp (-(9 / 2 * s ^ 2 * n))) := by
        have h9 : (1 + 2 / (1 / 4 : ℝ)) = 9 := by norm_num
        rw [h9] at hN2
        exact mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = 2 * ((9 : ℝ) ^ n * Real.exp (-(9 / 2 * s ^ 2 * n))) := by ring
    _ ≤ 2 * Real.exp (-(s ^ 2 * n)) :=
        mul_le_mul_of_nonneg_left (union_bound_arith hs) (by norm_num)
    _ ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
        have := Real.exp_pos (-(s ^ 2 * (n : ℝ)))
        linarith

/-- The Gaussian case at a general variance, which is the form the discrete chain of hinge 1
plugs into: its increment after time `t` is a standard Gaussian on `R^{n×n}_sym` scaled by `√t`,
i.e. `B + Bᵀ` with the entries of `B` i.i.d. `N(0, t/4)`. -/
theorem gaussian_opNormTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (B : Ω → Matrix (Fin n) (Fin n) ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hlaw : ∀ i j, P.map (fun ω => B ω i j) = gaussianReal 0 v)
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 12 * Real.sqrt v * s * Real.sqrt n ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ≤ 4 * Real.exp (-(s ^ 2 * n)) :=
  opNormTail_symmetrized P n B v hv hindep
    (fun i j => hasSubgaussianMGF_of_map_gaussianReal (hlaw i j) (ne_of_gt hv)) s hs

end D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail
