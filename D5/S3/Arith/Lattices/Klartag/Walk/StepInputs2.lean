/- GID: D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/StepInputs2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.Increments
import D5.S3.Arith.Lattices.Klartag.Completion.GoodEvent

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open Module
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

noncomputable section

section NormToolkit

variable {n : ℕ}

/-- **The operator norm is at most the Frobenius norm**, row by row by Cauchy–Schwarz.  Mathlib
has the two norms (`Matrix.toEuclideanCLM`, `Matrix.frobenius_norm`) but not this comparison in a
form free of the scoped `Matrix.Norms` instances. -/
theorem opNorm_le_frobenius (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ ≤ Real.sqrt (∑ i, ∑ j, (M i j) ^ 2) := by
  set C := Real.sqrt (∑ i, ∑ j, (M i j) ^ 2) with hC
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun x => ?_
  have hx : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  have hcoord : ∀ i : Fin n,
      (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) i = ∑ j, M i j * x j := by
    intro i; simp [Matrix.mulVec, dotProduct]
  have hTx : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 = ∑ i, (∑ j, M i j * x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoord i, Real.norm_eq_abs, sq_abs]
  have hrow : ∀ i : Fin n, (∑ j, M i j * x j) ^ 2 ≤ (∑ j, (M i j) ^ 2) * ∑ j, (x j) ^ 2 :=
    fun i => sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 ≤ (∑ i, ∑ j, (M i j) ^ 2) * ‖x‖ ^ 2 := by
    rw [hTx, hx, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hrow i
  have hfin : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [mul_pow, hC, Real.sq_sqrt (by positivity)]
    exact hsum
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) M x), mul_nonneg hC0 (norm_nonneg x),
    hfin]

/-- In the model of `R^{n×n}_sym`, the Frobenius norm of `symMat x` *is* the Euclidean norm of the
coordinate vector `x` (`Increments.sum_symMat_mul_eq_inner`), so the operator norm of the matrix is
at most `‖x‖`. -/
theorem opNorm_symMat_le_norm (x : EuclideanSpace ℝ (UT n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat x)‖ ≤ ‖x‖ := by
  refine (opNorm_le_frobenius (symMat x)).trans ?_
  have h : ∑ i, ∑ j, (symMat x i j) ^ 2 = ‖x‖ ^ 2 := by
    have := sum_symMat_mul_eq_inner x x
    rw [real_inner_self_eq_norm_sq] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sq (symMat x i j) ▸ rfl
  rw [h, Real.sqrt_sq (norm_nonneg x)]

/-- **The per-step bound in the currency `oneStep_of_good` consumes**: the orthogonal projection
contracts the Euclidean norm, so the operator norm of the projected increment is at most the norm
of the increment. -/
theorem opNorm_symMat_starProjection_le (K : Submodule ℝ (EuclideanSpace ℝ (UT n)))
    [K.HasOrthogonalProjection] (x : EuclideanSpace ℝ (UT n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (K.starProjection x))‖ ≤ ‖x‖ :=
  (opNorm_symMat_le_norm _).trans (K.norm_starProjection_apply_le x)

end NormToolkit

section StepBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two-sided Gaussian tail. -/
theorem measureReal_abs_ge_le {X : Ω → ℝ} {v : ℝ≥0} (hX : P.map X = gaussianReal 0 v)
    {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | a ≤ |X ω|} ≤ 2 * Real.exp (-a ^ 2 / (2 * v)) := by
  by_cases hv : v = 0
  · subst v
    simpa using (measureReal_le_one (μ := P) (s := {ω | a ≤ |X ω|})).trans
      (by norm_num : (1 : ℝ) ≤ 2)
  have hgauss := D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.hasSubgaussianMGF_of_map_gaussianReal hX hv
  have hsub : {ω | a ≤ |X ω|} ⊆ {ω | a ≤ X ω} ∪ {ω | a ≤ -X ω} := by
    intro ω hω
    rcases abs_cases (X ω) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (by simpa [h1] using hω)
    · exact Or.inr (by simpa [h1] using hω)
  calc P.real {ω | a ≤ |X ω|}
      ≤ P.real ({ω | a ≤ X ω} ∪ {ω | a ≤ -X ω}) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ P.real {ω | a ≤ X ω} + P.real {ω | a ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-a ^ 2 / (2 * v)) + Real.exp (-a ^ 2 / (2 * v)) := by
        exact add_le_add (hgauss.measure_ge_le ha) (hgauss.neg.measure_ge_le ha)
    _ = 2 * Real.exp (-a ^ 2 / (2 * v)) := by ring

/-- **The Euclidean-norm tail by a coordinate union bound.**  No independence is used: the
coordinates only have to be marginally `N(0, v)`. -/
theorem measureReal_norm_ge_le {ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ≥0}
    (hlaw : ∀ p : ι, P.map (fun ω => ξ ω p) = gaussianReal 0 v)
    {η : ℝ} (hη : 0 < η) :
    P.real {ω | η ≤ ‖ξ ω‖}
      ≤ (Fintype.card ι : ℝ) * (2 * Real.exp (-(η ^ 2 / (Fintype.card ι : ℝ)) / (2 * v))) := by
  classical
  rcases isEmpty_or_nonempty ι with hemp | hne
  · have hzero : {ω | η ≤ ‖ξ ω‖} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have : ξ ω = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]
      exact hη
    rw [hzero, measureReal_empty, Fintype.card_eq_zero]
    simp
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos
  set a : ℝ := η / Real.sqrt d with ha
  have ha0 : 0 < a := by
    rw [ha]; exact div_pos hη (Real.sqrt_pos.2 hd0)
  have hasq : a ^ 2 = η ^ 2 / d := by rw [ha, div_pow, Real.sq_sqrt hd0.le]
  have hsub : {ω | η ≤ ‖ξ ω‖} ⊆ ⋃ p ∈ (univ : Finset ι), {ω | a ≤ |ξ ω p|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_ofPred_eq, not_exists, not_le,
      exists_prop, true_and] at hcon
    have hsum : ‖ξ ω‖ ^ 2 = ∑ p, (ξ ω p) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl fun p _ => by rw [Real.norm_eq_abs, sq_abs]
    have hlt : ∑ p, (ξ ω p) ^ 2 < ∑ _p : ι, a ^ 2 := by
      refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun p _ => ?_
      have := hcon p
      nlinarith [abs_nonneg (ξ ω p), sq_abs (ξ ω p)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hasq] at hlt
    rw [← hd, mul_div_cancel₀ _ (ne_of_gt hd0)] at hlt
    have hηle : η ≤ ‖ξ ω‖ := hω
    nlinarith [norm_nonneg (ξ ω), hsum, hlt]
  calc P.real {ω | η ≤ ‖ξ ω‖}
      ≤ P.real (⋃ p ∈ (univ : Finset ι), {ω | a ≤ |ξ ω p|}) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ p : ι, P.real {ω | a ≤ |ξ ω p|} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p : ι, 2 * Real.exp (-a ^ 2 / (2 * v)) :=
        Finset.sum_le_sum fun p _ => measureReal_abs_ge_le (hlaw p) ha0.le
    _ = d * (2 * Real.exp (-(η ^ 2 / d) / (2 * v))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hasq, ← hd]

/-- The set on which **every** step has a small increment.  This is the second half of the good
event: `GoodEvent.goodEvent` controls the *accumulated* sum, this controls each single step, and
`GoodEvent.oneStep_of_good` needs both. -/
def stepGood (ξ : ℕ → Ω → EuclideanSpace ℝ ι) (N : ℕ) (η : ℝ) : Set Ω :=
  {ω | ∀ k, k < N → ‖ξ k ω‖ ≤ η}

/-- **The union bound over the `N` steps.**  Cost `N · d · 2 · exp(−η²/(2 d v))`. -/
theorem measureReal_compl_stepGood_le {ξ : ℕ → Ω → EuclideanSpace ℝ ι} {v : ℝ≥0}
    (hlaw : ∀ k, ∀ p : ι, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    {η : ℝ} (hη : 0 < η) (N : ℕ) :
    P.real (stepGood ξ N η)ᶜ
      ≤ (N : ℝ) * ((Fintype.card ι : ℝ)
          * (2 * Real.exp (-(η ^ 2 / (Fintype.card ι : ℝ)) / (2 * v)))) := by
  classical
  have hsub : (stepGood ξ N η)ᶜ ⊆ ⋃ k ∈ Finset.range N, {ω | η ≤ ‖ξ k ω‖} := by
    intro ω hω
    simp only [stepGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    exact Set.mem_biUnion (Finset.mem_range.2 hk) hlt.le
  calc P.real (stepGood ξ N η)ᶜ
      ≤ P.real (⋃ k ∈ Finset.range N, {ω | η ≤ ‖ξ k ω‖}) :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ k ∈ Finset.range N, P.real {ω | η ≤ ‖ξ k ω‖} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, (Fintype.card ι : ℝ)
          * (2 * Real.exp (-(η ^ 2 / (Fintype.card ι : ℝ)) / (2 * v))) :=
        Finset.sum_le_sum fun k _ => measureReal_norm_ge_le (hlaw k) hη
    _ = (N : ℝ) * ((Fintype.card ι : ℝ)
          * (2 * Real.exp (-(η ^ 2 / (Fintype.card ι : ℝ)) / (2 * v)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end StepBound

section StepBoundModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {n : ℕ}

end StepBoundModel

section H2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ι : Type*} [Fintype ι]

theorem stronglyMeasurable_coord_comap {ξ : Ω → EuclideanSpace ℝ ι} (p : ι) :
    StronglyMeasurable[MeasurableSpace.comap ξ inferInstance] fun ω => ξ ω p :=
  Measurable.stronglyMeasurable
    (((measurable_pi_apply p).comp (WithLp.measurable_ofLp _ _)).comp (comap_measurable ξ))

/-- **H2** — the centred increment kills the middle term of the one-step inequality. -/
theorem condExp_inner_eq_zero {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ)
    [SigmaFinite (P.trim hℱ)] {V ξ : Ω → EuclideanSpace ℝ ι}
    (hV : ∀ p, StronglyMeasurable[ℱ] fun ω => V ω p)
    (hξm : Measurable[mΩ] ξ)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) ℱ P)
    (hmean : ∀ p, ∫ ω, ξ ω p ∂P = 0)
    (hintξ : ∀ p, Integrable (fun ω => ξ ω p) P)
    (hint : ∀ p, Integrable (fun ω => V ω p * ξ ω p) P) :
    P[fun ω => ⟪V ω, ξ ω⟫ | ℱ] =ᵐ[P] 0 := by
  classical
  have hxi : ∀ p : ι, P[fun ω => ξ ω p | ℱ] =ᵐ[P] fun _ => (0 : ℝ) := by
    intro p
    refine (condExp_indep_eq hξm.comap_le hℱ (stronglyMeasurable_coord_comap p) hind).trans ?_
    exact Filter.Eventually.of_forall fun ω => hmean p
  have hdecomp : (fun ω => ⟪V ω, ξ ω⟫) = ∑ p : ι, (fun ω => V ω p * ξ ω p) := by
    funext ω
    rw [Finset.sum_apply]
    simp [PiLp.inner_apply, mul_comm]
  rw [hdecomp]
  refine (condExp_finsetSum (fun p _ => hint p) ℱ).trans ?_
  have hall : ∀ᵐ ω ∂P, ∀ p : ι, (P[fun ω => V ω p * ξ ω p | ℱ]) ω = 0 := by
    rw [ae_all_iff]
    intro p
    have h1 := condExp_mul_of_stronglyMeasurable_left (hV p) (hint p) (hintξ p)
    filter_upwards [h1, hxi p] with ω hω1 hω2
    have hstep : (P[fun ω => V ω p * ξ ω p | ℱ]) ω
        = V ω p * (P[fun ω => ξ ω p | ℱ]) ω := hω1
    rw [hstep, hω2, mul_zero]
  filter_upwards [hall] with ω hω
  rw [Finset.sum_apply]
  simp [hω]

end H2

section H3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

/-- **The trace of an orthogonal projection is the dimension of its range**, in the elementary
`∑_p ⟪b p, π (b p)⟫` form.  Mathlib has `LinearMap.IsProj.trace` but not this, and not the bridge
from `LinearMap.trace` to an orthonormal-basis sum. -/
theorem sum_inner_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (b : OrthonormalBasis ι ℝ E) :
    ∑ p : ι, ⟪b p, K.starProjection (b p)⟫ = (finrank ℝ K : ℝ) := by
  classical
  have hself : ∀ x : E, ⟪x, K.starProjection x⟫ = ‖K.starProjection x‖ ^ 2 := by
    intro x
    have h0 : ⟪x - K.starProjection x, K.starProjection x⟫ = (0 : ℝ) :=
      K.starProjection_inner_eq_zero x _ (K.starProjection_apply_mem x)
    have : ⟪x, K.starProjection x⟫ - ⟪K.starProjection x, K.starProjection x⟫ = 0 := by
      rw [← inner_sub_left]; exact h0
    rw [← real_inner_self_eq_norm_sq]
    linarith
  set c : OrthonormalBasis (Fin (finrank ℝ K)) ℝ K := stdOrthonormalBasis ℝ K with hc
  have hfix : ∀ i, K.starProjection ((c i : E)) = (c i : E) :=
    fun i => Submodule.starProjection_eq_self_iff.2 (c i).2
  have hpar : ∀ p : ι, ‖K.starProjection (b p)‖ ^ 2
      = ∑ i, ⟪(c i : E), b p⟫ ^ 2 := by
    intro p
    have hmem : K.starProjection (b p) ∈ K := K.starProjection_apply_mem _
    have hy : ‖K.starProjection (b p)‖ ^ 2 = ‖(⟨K.starProjection (b p), hmem⟩ : K)‖ ^ 2 := rfl
    rw [hy, ← c.sum_sq_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinner : (⟪c i, (⟨K.starProjection (b p), hmem⟩ : K)⟫ : ℝ)
        = ⟪(c i : E), K.starProjection (b p)⟫ := rfl
    rw [hinner]
    congr 1
    rw [← Submodule.inner_starProjection_left_eq_right, hfix i]
  calc ∑ p : ι, ⟪b p, K.starProjection (b p)⟫
      = ∑ p : ι, ∑ i, ⟪(c i : E), b p⟫ ^ 2 := by
        exact Finset.sum_congr rfl fun p _ => by rw [hself (b p), hpar p]
    _ = ∑ i, ∑ p : ι, ⟪(c i : E), b p⟫ ^ 2 := Finset.sum_comm
    _ = ∑ _i : Fin (finrank ℝ K), (1 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [b.sum_sq_inner_left]
        have hone : ‖(c i : E)‖ = 1 := c.norm_eq_one i
        rw [hone, one_pow]
    _ = (finrank ℝ K : ℝ) := by simp

end H3

section H3Coord

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inner_single_left' (p : ι) (y : EuclideanSpace ℝ ι) :
    ⟪(EuclideanSpace.single p (1:ℝ)), y⟫ = y p := by
  simp [EuclideanSpace.inner_single_left]

/-- The quadratic form of an orthogonal projection, in coordinates. -/
theorem norm_starProjection_sq_eq (K : Submodule ℝ (EuclideanSpace ℝ ι))
    [K.HasOrthogonalProjection] (x : EuclideanSpace ℝ ι) :
    ‖K.starProjection x‖ ^ 2
      = ∑ p, ∑ q, (K.starProjection (EuclideanSpace.single p (1:ℝ))) q * (x p * x q) := by
  have hself : ⟪x, K.starProjection x⟫ = ‖K.starProjection x‖ ^ 2 := by
    have h0 : ⟪x - K.starProjection x, K.starProjection x⟫ = (0 : ℝ) :=
      K.starProjection_inner_eq_zero x _ (K.starProjection_apply_mem x)
    have h1 : ⟪x, K.starProjection x⟫ - ⟪K.starProjection x, K.starProjection x⟫ = 0 := by
      rw [← inner_sub_left]; exact h0
    rw [← real_inner_self_eq_norm_sq]
    linarith
  have hcoord : ∀ p : ι, (K.starProjection x) p
      = ∑ q, (K.starProjection (EuclideanSpace.single p (1:ℝ))) q * x q := by
    intro p
    rw [← inner_single_left' p (K.starProjection x),
      ← Submodule.inner_starProjection_left_eq_right]
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun q _ => by simp [RCLike.inner_apply, mul_comm]
  rw [← hself, PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hcoord p, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

end H3Coord

section H3Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The conditional expectation of a quadratic form in the increment with `ℱ`-measurable
coefficients. -/
theorem condExp_quadForm {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) [SigmaFinite (P.trim hℱ)]
    {M : Ω → ι → ι → ℝ} {ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ}
    (hM : ∀ p q, StronglyMeasurable[ℱ] fun ω => M ω p q)
    (hξm : Measurable[mΩ] ξ)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) ℱ P)
    (hcov : ∀ p q : ι, ∫ ω, ξ ω p * ξ ω q ∂P = if p = q then v else 0)
    (hintprod : ∀ p q, Integrable (fun ω => ξ ω p * ξ ω q) P)
    (hint : ∀ p q, Integrable (fun ω => M ω p q * (ξ ω p * ξ ω q)) P) :
    P[fun ω => ∑ p, ∑ q, M ω p q * (ξ ω p * ξ ω q) | ℱ]
      =ᵐ[P] fun ω => v * ∑ p, M ω p p := by
  classical
  have hpair : ∀ p q : ι,
      P[fun ω => ξ ω p * ξ ω q | ℱ] =ᵐ[P] fun _ => (if p = q then v else 0) := by
    intro p q
    have hsm : StronglyMeasurable[MeasurableSpace.comap ξ inferInstance]
        (fun ω => ξ ω p * ξ ω q) :=
      (stronglyMeasurable_coord_comap p).mul (stronglyMeasurable_coord_comap q)
    refine (condExp_indep_eq hξm.comap_le hℱ hsm hind).trans ?_
    exact Filter.Eventually.of_forall fun ω => hcov p q
  have hterm : ∀ p q : ι, P[fun ω => M ω p q * (ξ ω p * ξ ω q) | ℱ]
      =ᵐ[P] fun ω => M ω p q * (if p = q then v else 0) := by
    intro p q
    have h1 := condExp_mul_of_stronglyMeasurable_left (hM p q) (hint p q) (hintprod p q)
    filter_upwards [h1, hpair p q] with ω hω1 hω2
    have hstep : (P[fun ω => M ω p q * (ξ ω p * ξ ω q) | ℱ]) ω
        = M ω p q * (P[fun ω => ξ ω p * ξ ω q | ℱ]) ω := hω1
    rw [hstep, hω2]
  have hall : ∀ᵐ ω ∂P, ∀ p q : ι, (P[fun ω => M ω p q * (ξ ω p * ξ ω q) | ℱ]) ω
      = M ω p q * (if p = q then v else 0) := by
    rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro q; exact hterm p q
  have hflat : (fun ω => ∑ p, ∑ q, M ω p q * (ξ ω p * ξ ω q))
      = ∑ r : ι × ι, (fun ω => M ω r.1 r.2 * (ξ ω r.1 * ξ ω r.2)) := by
    funext ω
    rw [Finset.sum_apply, Fintype.sum_prod_type]
  have hall : ∀ᵐ ω ∂P, ∀ r : ι × ι, (P[fun ω => M ω r.1 r.2 * (ξ ω r.1 * ξ ω r.2) | ℱ]) ω
      = M ω r.1 r.2 * (if r.1 = r.2 then v else 0) := by
    rw [ae_all_iff]; intro r; exact hterm r.1 r.2
  rw [hflat]
  have hsum := condExp_finsetSum (μ := P) (s := (Finset.univ : Finset (ι × ι)))
    (f := fun r : ι × ι => (fun ω => M ω r.1 r.2 * (ξ ω r.1 * ξ ω r.2)))
    (fun r _ => hint r.1 r.2) ℱ
  filter_upwards [hsum, hall] with ω h1 h2
  rw [h1, Finset.sum_apply, Finset.sum_congr rfl fun r _ => h2 r, Fintype.sum_prod_type]
  have hinner : ∀ p : ι, ∑ q : ι, M ω p q * (if p = q then v else 0) = M ω p p * v := by
    intro p
    rw [Finset.sum_congr rfl fun q _ => (by split <;> simp :
      M ω p q * (if p = q then v else 0) = if p = q then M ω p q * v else 0)]
    rw [Finset.sum_ite_eq univ p]
    simp
  rw [Finset.sum_congr rfl fun p _ => hinner p, ← Finset.sum_mul, mul_comm]

end H3Prob

section H3Cov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurable_coord {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable[mΩ] ξ) (p : ι) :
    Measurable[mΩ] fun ω => ξ ω p :=
  ((measurable_pi_apply p).comp (WithLp.measurable_ofLp _ _)).comp hξ

theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := (0:ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- The increment's coordinates are centred. -/
theorem integral_coord_eq_zero {ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ≥0}
    (hξ : Measurable[mΩ] ξ)
    (hlaw : ∀ p : ι, P.map (fun ω => ξ ω p) = gaussianReal 0 v) (r : ι) :
    ∫ ω, ξ ω r ∂P = 0 := by
  have hmap : ∫ t : ℝ, t ∂(P.map (fun ω => ξ ω r)) = ∫ ω, ξ ω r ∂P :=
    integral_map (φ := fun ω => ξ ω r) (f := fun t : ℝ => t)
      (measurable_coord hξ r).aemeasurable (by fun_prop)
  rw [← hmap, hlaw r]
  simp

/-- The covariance of the increment's coordinates. -/
theorem integral_coord_mul {ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ≥0}
    (hξ : Measurable[mΩ] ξ)
    (hindep : iIndepFun (fun (p : ι) (ω : Ω) => ξ ω p) P)
    (hlaw : ∀ p : ι, P.map (fun ω => ξ ω p) = gaussianReal 0 v) (p q : ι) :
    ∫ ω, ξ ω p * ξ ω q ∂P = if p = q then (v : ℝ) else 0 := by
  have hmean : ∀ r : ι, ∫ ω, ξ ω r ∂P = 0 := by
    intro r
    have hmap : ∫ t : ℝ, t ∂(P.map (fun ω => ξ ω r)) = ∫ ω, ξ ω r ∂P :=
      integral_map (φ := fun ω => ξ ω r) (f := fun t : ℝ => t)
        (measurable_coord hξ r).aemeasurable (by fun_prop)
    rw [← hmap, hlaw r]
    simp
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    have hsq : ∀ ω, ξ ω p * ξ ω p = (fun t : ℝ => t ^ 2) (ξ ω p) := fun ω => by ring
    have hmap : ∫ t : ℝ, t ^ 2 ∂(P.map (fun ω => ξ ω p)) = ∫ ω, (fun t : ℝ => t ^ 2) (ξ ω p) ∂P :=
      integral_map (φ := fun ω => ξ ω p) (f := fun t : ℝ => t ^ 2)
        (measurable_coord hξ p).aemeasurable (by fun_prop)
    rw [integral_congr_ae (Filter.Eventually.of_forall hsq), ← hmap, hlaw p]
    exact integral_sq_gaussianReal v
  · rw [if_neg hpq]
    have hind : IndepFun (fun ω => ξ ω p) (fun ω => ξ ω q) P := hindep.indepFun hpq
    rw [hind.integral_fun_mul_eq_mul_integral
      (measurable_coord hξ p).aestronglyMeasurable
      (measurable_coord hξ q).aestronglyMeasurable]
    rw [show P[fun ω => ξ ω p] = ∫ ω, ξ ω p ∂P from rfl, hmean p, zero_mul]

end H3Cov

section H3Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem condExp_norm_starProjection_sq
    {K : Ω → Submodule ℝ (EuclideanSpace ℝ ι)} {ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ≥0}
    (hξm : Measurable ξ)
    (hindep : iIndepFun (fun (p : ι) (ω : Ω) => ξ ω p) P)
    (hlaw : ∀ p : ι, P.map (fun ω => ξ ω p) = gaussianReal 0 v)
    (hintprod : ∀ p q : ι, Integrable (fun ω => ξ ω p * ξ ω q) P)
    (hint : ∀ p q : ι, Integrable (fun ω =>
      ((K ω).starProjection (EuclideanSpace.single p (1:ℝ))) q * (ξ ω p * ξ ω q)) P)
    {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) [SigmaFinite (P.trim hℱ)]
    (hM : ∀ p q : ι, StronglyMeasurable[ℱ]
      fun ω => ((K ω).starProjection (EuclideanSpace.single p (1:ℝ))) q)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance) ℱ P) :
    P[fun ω => ‖(K ω).starProjection (ξ ω)‖ ^ 2 | ℱ]
      =ᵐ[P] fun ω => (v : ℝ) * (finrank ℝ (K ω) : ℝ) := by
  have hrw : (fun ω => ‖(K ω).starProjection (ξ ω)‖ ^ 2)
      = fun ω => ∑ p, ∑ q,
          ((K ω).starProjection (EuclideanSpace.single p (1:ℝ))) q * (ξ ω p * ξ ω q) :=
    funext fun ω => norm_starProjection_sq_eq (K ω) (ξ ω)
  rw [hrw]
  refine (condExp_quadForm (mΩ := mΩ) hℱ hM hξm hind (integral_coord_mul (mΩ := mΩ) hξm hindep hlaw) hintprod
    hint).trans (Filter.Eventually.of_forall fun ω => ?_)
  have hsum : ∑ p : ι, ((K ω).starProjection (EuclideanSpace.single p (1:ℝ))) p
      = (finrank ℝ (K ω) : ℝ) := by
    rw [← sum_inner_starProjection (K ω) (EuclideanSpace.basisFun ι ℝ)]
    exact Finset.sum_congr rfl fun p _ => by
      rw [EuclideanSpace.basisFun_apply, inner_single_left']
  simp only [hsum]

end H3Assembly

section Conversion

variable {n : ℕ}

theorem norm_sq_euclidean (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]

theorem norm_sq_mulVec (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 = ∑ i, (∑ j, M i j * x j) ^ 2 := by
  rw [norm_sq_euclidean]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) i = ∑ j, M i j * x j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hc]

theorem frobenius_mul_left_le (X B : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, ∑ j, ((X * B) i j) ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖ ^ 2 * ∑ i, ∑ j, (B i j) ^ 2 := by
  rw [Finset.sum_comm]
  have key : ∀ j : Fin n, ∑ i, ((X * B) i j) ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖ ^ 2 * ∑ k, (B k j) ^ 2 := by
    intro j
    set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k => B k j) with hx
    have h1 : ∑ i, ((X * B) i j) ^ 2 = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X x‖ ^ 2 := by
      rw [norm_sq_mulVec]
      exact (Finset.sum_congr rfl fun i _ => by simp [Matrix.mul_apply, hx]).symm
    have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X x‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖x‖ ^ 2 = ∑ k, (B k j) ^ 2 := by rw [norm_sq_euclidean]
    rw [h1, ← h3]
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) X x), norm_nonneg x,
      norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) X), h2]
  calc ∑ j, ∑ i, ((X * B) i j) ^ 2
      ≤ ∑ j, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖ ^ 2 * ∑ k, (B k j) ^ 2 :=
        Finset.sum_le_sum fun j _ => key j
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖ ^ 2 * ∑ j, ∑ k, (B k j) ^ 2 := by
        rw [Finset.mul_sum]
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖ ^ 2 * ∑ i, ∑ j, (B i j) ^ 2 := by
        rw [Finset.sum_comm]

theorem frobenius_mul_right_le (B Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.IsSymm) :
    ∑ i, ∑ j, ((B * Y) i j) ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y‖ ^ 2 * ∑ i, ∑ j, (B i j) ^ 2 := by
  have key : ∀ i : Fin n, ∑ j, ((B * Y) i j) ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y‖ ^ 2 * ∑ k, (B i k) ^ 2 := by
    intro i
    set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k => B i k) with hx
    have h1 : ∑ j, ((B * Y) i j) ^ 2 = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y x‖ ^ 2 := by
      rw [norm_sq_mulVec]
      refine (Finset.sum_congr rfl fun j _ => ?_).symm
      congr 1
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [hx]; simp only; rw [hY.apply j k]; ring
    have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y x‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖x‖ ^ 2 = ∑ k, (B i k) ^ 2 := by rw [norm_sq_euclidean]
    rw [h1, ← h3]
    nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Y x), norm_nonneg x,
      norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) Y), h2]
  calc ∑ i, ∑ j, ((B * Y) i j) ^ 2
      ≤ ∑ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y‖ ^ 2 * ∑ k, (B i k) ^ 2 :=
        Finset.sum_le_sum fun i _ => key i
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Y‖ ^ 2 * ∑ i, ∑ j, (B i j) ^ 2 := by
        rw [Finset.mul_sum]

theorem comm_of_conj {A S : Matrix (Fin n) (Fin n) ℝ} (hSA : S * A * S = 1) : A * S = S * A := by
  have h1 : S * (A * S) = 1 := by rw [← Matrix.mul_assoc]; exact hSA
  have hr : S⁻¹ = A * S := Matrix.inv_eq_right_inv h1
  have hl : S⁻¹ = S * A := Matrix.inv_eq_left_inv hSA
  rw [← hr, hl]

theorem isUnit_det_of_conj {A S : Matrix (Fin n) (Fin n) ℝ} (hSA : S * A * S = 1) :
    IsUnit S.det :=
  Matrix.isUnit_det_of_right_inverse (B := A * S) (by rw [← Matrix.mul_assoc]; exact hSA)

theorem mul_mul_left_of_conj {A S : Matrix (Fin n) (Fin n) ℝ} (hSA : S * A * S = 1) :
    (A * S) * S = 1 := by
  rw [← Matrix.inv_eq_right_inv (A := S) (B := A * S) (by rw [← Matrix.mul_assoc]; exact hSA)]
  exact Matrix.nonsing_inv_mul S (isUnit_det_of_conj hSA)

theorem mul_mul_right_of_conj {A S : Matrix (Fin n) (Fin n) ℝ} (hSA : S * A * S = 1) :
    S * (S * A) = 1 := by
  rw [← Matrix.inv_eq_left_inv (A := S) (B := S * A) hSA]
  exact Matrix.mul_nonsing_inv S (isUnit_det_of_conj hSA)

theorem isSymm_mul_of_conj {A S : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hS : S.IsSymm)
    (hSA : S * A * S = 1) : (A * S).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, hS.eq, hA.eq]
  exact (comm_of_conj hSA).symm

theorem opNorm_sq_le_of_sq {A R : Matrix (Fin n) (Fin n) ℝ} (hR : R.IsSymm) (hRR : R * R = A) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) R‖ ^ 2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) R with hT
  have hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖T x‖ ^ 2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖x‖ ^ 2 := by
    intro x
    have h1 : ‖T x‖ ^ 2 = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
      rw [← real_inner_self_eq_norm_sq, hT]
      rw [D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.inner_toEuclideanCLM_symm hR]
      congr 1
      rw [← hRR, map_mul]
      rfl
    rw [h1]
    calc ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫
        ≤ |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫| := le_abs_self _
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖x‖ ^ 2 :=
          D5.S3.Arith.Lattices.Klartag.Completion.GoodEvent.abs_inner_self_le_opNorm A x
  have hA0 : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := norm_nonneg _
  have hle : ‖T‖ ≤ Real.sqrt ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have h2 : ‖T x‖ ^ 2 ≤ (Real.sqrt ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA0]
      exact hbound x
    nlinarith [norm_nonneg (T x), mul_nonneg (Real.sqrt_nonneg
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖) (norm_nonneg x)]
  nlinarith [norm_nonneg T, Real.sq_sqrt hA0, Real.sqrt_nonneg
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖, hle]

theorem frobenius_conj_le {A H S : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hS : S.IsSymm)
    (hSA : S * A * S = 1) :
    ∑ i, ∑ j, (H i j) ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ^ 2 * ∑ i, ∑ j, ((S * H * S) i j) ^ 2 := by
  have hcomm : A * S = S * A := comm_of_conj hSA
  have hleft : A * (S * S) = 1 := by
    rw [← Matrix.mul_assoc]; exact mul_mul_left_of_conj hSA
  have hright : (S * S) * A = 1 := by
    rw [Matrix.mul_assoc]; exact mul_mul_right_of_conj hSA
  have hRsymm : (A * S).IsSymm := isSymm_mul_of_conj hA hS hSA
  have hRsymm' : (S * A).IsSymm := hcomm ▸ hRsymm
  have hRR : (A * S) * (A * S) = A := by
    calc (A * S) * (A * S) = A * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hSA, Matrix.mul_one]
  have hRR' : (S * A) * (S * A) = A := by rw [← hcomm]; exact hRR
  have hH : (A * S) * ((S * H * S) * (S * A)) = H := by
    calc (A * S) * ((S * H * S) * (S * A))
        = (A * (S * S)) * H * ((S * S) * A) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  have hnorm1 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A * S)‖ ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := opNorm_sq_le_of_sq hRsymm hRR
  have hnorm2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * A)‖ ^ 2
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := opNorm_sq_le_of_sq hRsymm' hRR'
  have hB0 : (0 : ℝ) ≤ ∑ i, ∑ j, ((S * H * S) i j) ^ 2 := by positivity
  calc ∑ i, ∑ j, (H i j) ^ 2
      = ∑ i, ∑ j, (((A * S) * ((S * H * S) * (S * A))) i j) ^ 2 := by rw [hH]
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A * S)‖ ^ 2
          * ∑ i, ∑ j, (((S * H * S) * (S * A)) i j) ^ 2 := frobenius_mul_left_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A * S)‖ ^ 2
          * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * A)‖ ^ 2
            * ∑ i, ∑ j, ((S * H * S) i j) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (frobenius_mul_right_le _ _ hRsymm') (by positivity)
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖
          * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ∑ i, ∑ j, ((S * H * S) i j) ^ 2) := by
        refine mul_le_mul hnorm1 (mul_le_mul_of_nonneg_right hnorm2 hB0) (by positivity)
          (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ^ 2 * ∑ i, ∑ j, ((S * H * S) i j) ^ 2 := by ring

end Conversion

section Assembly

open D5.S3.Arith.Lattices.Klartag.Completion.GoodEvent

variable {n : ℕ}

/-- **The one-step bound with the unconjugated quadratic gain.**  `GoodEvent.oneStep_of_good`
produces `-‖S H S‖²_F / (2(1+δ)²)`; the conversion turns it into `-‖H‖²_F / (2 M² (1+δ)²)`, which
is the shape whose conditional expectation H3 computes. -/
theorem log_det_step_unconj {A H S : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    {m η δ M : ℝ} (hm : 0 < m)
    (hAlb : ∀ x : EuclideanSpace ℝ (Fin n),
      m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫)
    (hHub : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤ η)
    (hδ : η / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hM : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M) (hM0 : 0 < M) :
    (A + H).PosDef ∧
      Real.log (A + H).det ≤ Real.log A.det + (A⁻¹ * H).trace
        - (∑ i, ∑ j, (H i j) ^ 2) / (2 * M ^ 2 * (1 + δ) ^ 2) := by
  obtain ⟨hpos, hlog⟩ := oneStep_of_good hA hS hSA hH hm hAlb hHub hδ hδ0 hδ1
  refine ⟨hpos, hlog.trans ?_⟩
  have hconv := frobenius_conj_le (H := H) (isSymm_of_isHermitian hA.isHermitian)
    (isSymm_of_isHermitian hS) hSA
  have hB0 : (0 : ℝ) ≤ ∑ i, ∑ j, ((S * H * S) i j) ^ 2 := by positivity
  have hAM : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ^ 2 ≤ M ^ 2 := by
    have := norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
    nlinarith
  have hkey : ∑ i, ∑ j, (H i j) ^ 2 ≤ M ^ 2 * ∑ i, ∑ j, ((S * H * S) i j) ^ 2 :=
    hconv.trans (mul_le_mul_of_nonneg_right hAM hB0)
  have hden : (0 : ℝ) < 2 * (1 + δ) ^ 2 := by nlinarith
  have hden2 : (0 : ℝ) < 2 * M ^ 2 * (1 + δ) ^ 2 := by positivity
  have hstep : (∑ i, ∑ j, (H i j) ^ 2) / (2 * M ^ 2 * (1 + δ) ^ 2)
      ≤ (∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * (1 + δ) ^ 2) := by
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hM0
    have hδne : ((1 : ℝ) + δ) ≠ 0 := by positivity
    have heq : (∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * (1 + δ) ^ 2)
        = (M ^ 2 * ∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * M ^ 2 * (1 + δ) ^ 2) := by
      field_simp
    rw [heq]
    gcongr
  linarith

end Assembly

section Swap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `⟪u, π x⟫ = ⟪π u, x⟫`: the form in which the chain's middle term
`⟪A_k⁻¹, π_k ξ_k⟫ = ⟪π_k A_k⁻¹, ξ_k⟫` is fed to H2, whose `V` is then `π_k A_k⁻¹`. -/
theorem inner_starProjection_swap (K : Submodule ℝ E) [K.HasOrthogonalProjection] (u x : E) :
    ⟪u, K.starProjection x⟫ = ⟪K.starProjection u, x⟫ :=
  (Submodule.inner_starProjection_left_eq_right K u x).symm

end Swap

section AssemblyChain

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {n : ℕ}

end AssemblyChain

end

end D5.S3.Arith.Lattices.Klartag.Walk.StepInputs2
