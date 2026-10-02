/- GID: D5/S3/Resource/SimplexCoverageRoot
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoverageRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analytic line identification and represented spanning root concavity. -/

import D5.S3.Resource.SimplexCoverageInduction
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoverageRoot

open scoped BigOperators Topology
open Matrix SimplexCoveragePolynomial SimplexCoverageInduction Set Filter

variable {Index : Type*} [Fintype Index]

theorem evaluateAt_line_hasDerivAt (polynomial : MvPolynomial Index ℚ)
    (x y : Index → ℝ) (time : ℝ) :
    HasDerivAt (fun parameter => evaluateAt (fun index => x index + parameter * y index)
      polynomial)
      (∑ index, y index * evaluateAt (fun index => x index + time * y index)
        (MvPolynomial.pderiv index polynomial)) time := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
    simpa [evaluateAt] using hasDerivAt_const time ((algebraMap ℚ ℝ) coefficient)
  | add first second first_derivative second_derivative =>
    simpa [evaluateAt, Pi.add_def, mul_add, Finset.sum_add_distrib] using
      first_derivative.add second_derivative
  | mul_X polynomial index derivative =>
    convert derivative.mul
      (((hasDerivAt_id time).mul_const (y index)).const_add (x index)) using 1 <;> try rfl
    · ext parameter
      simp [evaluateAt]
    · have expansion (other : Index) :
          y other * evaluateAt (fun coordinate => x coordinate + time * y coordinate)
              (MvPolynomial.pderiv other (polynomial * MvPolynomial.X index)) =
            (y other * evaluateAt (fun coordinate => x coordinate + time * y coordinate)
              (MvPolynomial.pderiv other polynomial)) * (x index + time * y index) +
              if other = index then y index *
                evaluateAt (fun coordinate => x coordinate + time * y coordinate) polynomial
              else 0 := by
        by_cases same : other = index
        · subst other
          simp [evaluateAt]
          ring
        · simp [evaluateAt, same, Ne.symm same]
          ring
      simp_rw [expansion]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
      ring

variable [DecidableEq Index] {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

-- Keep the elaboration budget local to the nested derivative and boundary-limit proof.
set_option maxHeartbeats 1500000 in
theorem spanningPolynomial_root_concaveOn
    (columns : Index → V) (U : Submodule K V) [FiniteDimensional K (V ⧸ U)]
    (degree : ℕ) (positive_degree : 1 ≤ degree) :
    ConcaveOn ℝ {x : Index → ℝ | ∀ index, 0 ≤ x index}
      (fun x => (evaluateAt x (spanningPolynomial columns U degree)) ^
        (1 / (degree : ℝ))) := by
  classical
  let quotient_columns : Index → (V ⧸ U) := fun index => U.mkQ (columns index)
  have quotient_polynomial : spanningPolynomial columns U degree =
      spanningPolynomial (K := K) quotient_columns ⊥ degree := by
    apply MvPolynomial.ext
    intro alpha
    have spanning_iff : representedSpan columns U alpha = ⊤ ↔
        representedSpan (K := K) quotient_columns ⊥ alpha = ⊤ := by
      simp only [representedSpan, bot_sup_eq]
      rw [← U.map_mkQ_eq_top (Submodule.span K (columns '' (alpha.support : Set Index))),
        Submodule.map_span, Set.image_image]
    simp only [spanningPolynomial_coeff, spanning_iff]
  rw [quotient_polynomial]
  let polynomial := spanningPolynomial (K := K) quotient_columns ⊥ degree
  let power : ℝ := 1 / (degree : ℝ)
  let root : (Index → ℝ) → ℝ := fun x => (evaluateAt x polynomial) ^ power
  have degree_pos : 0 < (degree : ℝ) := by exact_mod_cast (by omega : 0 < degree)
  have power_pos : 0 < power := one_div_pos.mpr degree_pos
  have degree_power : (degree : ℝ) * power = 1 := by
    dsimp [power]
    field_simp
  have nonnegative_convex : Convex ℝ {x : Index → ℝ | ∀ index, 0 ≤ x index} := by
    intro x hx y hy first second hfirst hsecond _ index
    exact add_nonneg (mul_nonneg hfirst (hx index)) (mul_nonneg hsecond (hy index))
  have positive_convex : Convex ℝ {x : Index → ℝ | ∀ index, 0 < x index} := by
    simpa [Set.pi] using
      (convex_pi (s := (Set.univ : Set Index)) (t := fun _ => Set.Ioi (0 : ℝ))
        (fun _ _ => convex_Ioi (0 : ℝ)))
  change ConcaveOn ℝ {x : Index → ℝ | ∀ index, 0 ≤ x index} root
  by_cases polynomial_zero : polynomial = 0
  · simpa [root, polynomial_zero, evaluateAt] using
      (concaveOn_const ((0 : ℝ) ^ power) nonnegative_convex)
  have index_nonempty : Nonempty Index := by
    cases isEmpty_or_nonempty Index with
    | inr nonempty => exact nonempty
    | inl empty =>
      let := empty
      exfalso
      apply polynomial_zero
      apply MvPolynomial.ext
      intro alpha
      have alpha_zero : alpha = 0 := Subsingleton.elim _ _
      simp [polynomial, spanningPolynomial_coeff, alpha_zero,
        show (0 : ℕ) ≠ degree by omega]
  let := index_nonempty
  have spanning : (⊥ : Submodule K (V ⧸ U)) ⊔
      Submodule.span K (Set.range quotient_columns) = ⊤ := by
    by_contra failure
    apply polynomial_zero
    exact spanningPolynomial_eq_zero_of_rank_or_span (K := K)
      quotient_columns ⊥ degree (Or.inr failure)
  have rank_bound : Module.finrank K ((V ⧸ U) ⧸ (⊥ : Submodule K (V ⧸ U))) ≤ degree := by
    by_contra failure
    apply polynomial_zero
    exact spanningPolynomial_eq_zero_of_rank_or_span (K := K)
      quotient_columns ⊥ degree (Or.inl (by omega))
  have evaluation_pos (x : Index → ℝ) (hx : ∀ index, 0 < x index) :
      0 < evaluateAt x polynomial := by
    exact ((spanningPolynomial_positive_iff (K := K) quotient_columns ⊥
      degree x hx spanning).2).mpr rank_bound
  have root_continuous : Continuous root := by
    apply (Real.continuous_rpow_const power_pos.le).comp
    simpa only [evaluateAt, MvPolynomial.eval₂_eq_eval_map] using
      (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℝ) polynomial))
  have positive_concavity : ConcaveOn ℝ {x : Index → ℝ | ∀ index, 0 < x index} root := by
    refine ⟨positive_convex, ?_⟩
    intro x hx y hy first second hfirst hsecond weights
    let direction : Index → ℝ := fun index => y index - x index
    let line : ℝ → (Index → ℝ) := fun time index => x index + time * direction index
    let value : ℝ → ℝ := fun time => evaluateAt (line time) polynomial
    let gradient : ℝ → ℝ := fun time =>
      ∑ index, direction index * evaluateAt (line time) (MvPolynomial.pderiv index polynomial)
    let curvature : ℝ → ℝ := fun time =>
      direction ⬝ᵥ (spanningHessian (K := K) quotient_columns ⊥ degree (line time) *ᵥ direction)
    let first_root : ℝ → ℝ := fun time => gradient time * power * (value time) ^ (power - 1)
    let second_root : ℝ → ℝ := fun time =>
      power * (value time) ^ (power - 2) *
        (value time * curvature time + (power - 1) * (gradient time) ^ 2)
    have affine_line (time : ℝ) : line time = (1 - time) • x + time • y := by
      ext index
      simp [line, direction, Pi.smul_apply, smul_eq_mul]
      ring
    have line_pos (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 1) :
        ∀ index, 0 < line time index := by
      rw [affine_line]
      exact positive_convex hx hy (sub_nonneg.mpr htime.2) htime.1 (by ring)
    have value_derivative (time : ℝ) : HasDerivAt value (gradient time) time :=
      evaluateAt_line_hasDerivAt polynomial x direction time
    have gradient_derivative (time : ℝ) : HasDerivAt gradient (curvature time) time := by
      convert (HasDerivAt.fun_sum (u := Finset.univ) fun index _ =>
        (evaluateAt_line_hasDerivAt (MvPolynomial.pderiv index polynomial)
          x direction time).const_mul (direction index)) using 1 <;> try rfl
      dsimp [curvature, spanningHessian, dotProduct, mulVec]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro column _
      ring
    have root_derivative (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivAt (fun parameter => root (line parameter)) (first_root time) time := by
      exact (value_derivative time).rpow_const
        (Or.inl (ne_of_gt (evaluation_pos (line time) (line_pos time htime))))
    have root_second_derivative (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivAt first_root (second_root time) time := by
      have value_positive : 0 < value time := evaluation_pos (line time) (line_pos time htime)
      have power_identity : (value time) ^ (power - 1) =
          (value time) ^ (power - 2) * value time := by
        calc
          _ = (value time) ^ ((power - 2) + 1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add value_positive, Real.rpow_one]
      convert ((gradient_derivative time).mul_const power).mul
        ((value_derivative time).rpow_const (p := power - 1)
          (Or.inl (ne_of_gt value_positive))) using 1 <;> try rfl
      dsimp [second_root]
      rw [power_identity, show power - 1 - 1 = power - 2 by ring]
      ring
    have root_second_nonpos (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 1) :
        second_root time ≤ 0 := by
      have bound := spanningPolynomial_reverse (K := K) quotient_columns ⊥
        degree (line time) direction (line_pos time htime)
      have gradient_identity :
          ((fun index => evaluateAt (line time) (MvPolynomial.pderiv index polynomial))
            ⬝ᵥ direction) = gradient time := by
        dsimp [gradient, dotProduct]
        apply Finset.sum_congr rfl
        intro index _
        ring
      change (degree : ℝ) * value time * curvature time ≤
        ((degree : ℝ) - 1) *
          (((fun index => evaluateAt (line time) (MvPolynomial.pderiv index polynomial))
            ⬝ᵥ direction) ^ 2) at bound
      rw [gradient_identity] at bound
      have inner_nonpos : value time * curvature time +
          (power - 1) * (gradient time) ^ 2 ≤ 0 := by
        apply nonpos_of_mul_nonpos_left (b := (degree : ℝ)) _ degree_pos
        calc
          (value time * curvature time +
              (power - 1) * (gradient time) ^ 2) * (degree : ℝ) =
              (degree : ℝ) * value time * curvature time +
                ((degree : ℝ) * power - (degree : ℝ)) * (gradient time) ^ 2 := by ring
          _ = (degree : ℝ) * value time * curvature time -
              ((degree : ℝ) - 1) * (gradient time) ^ 2 := by rw [degree_power]; ring
          _ ≤ 0 := sub_nonpos.mpr bound
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg power_pos.le (Real.rpow_nonneg
          (evaluation_pos (line time) (line_pos time htime)).le _)) inner_nonpos
    have segment_concavity : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun time => root (line time)) := by
      apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
        (root_continuous.comp (by dsimp [line]; fun_prop)).continuousOn
      · intro time htime
        exact (root_derivative time (interior_subset htime)).hasDerivWithinAt
      · intro time htime
        exact (root_second_derivative time (interior_subset htime)).hasDerivWithinAt
      · intro time htime
        exact root_second_nonpos time (interior_subset htime)
    have inequality := segment_concavity.2 (x := 0) (y := 1) (by norm_num) (by norm_num)
      hfirst hsecond weights
    have line_zero : line 0 = x := by ext index; simp [line]
    have line_one : line 1 = y := by ext index; simp [line, direction]
    have weighted_line : line second = first • x + second • y := by
      rw [affine_line, show 1 - second = first by linarith]
    simpa only [line_zero, line_one, smul_eq_mul, mul_zero, mul_one, zero_add,
      weighted_line] using inequality
  refine ⟨nonnegative_convex, ?_⟩
  intro x hx y hy first second hfirst hsecond weights
  have left_continuous : Continuous (fun epsilon : ℝ =>
      first * root (fun index => x index + epsilon) +
        second * root (fun index => y index + epsilon)) := by
    fun_prop
  have right_continuous : Continuous (fun epsilon : ℝ =>
      root (first • (fun index => x index + epsilon) +
        second • (fun index => y index + epsilon))) := by
    fun_prop
  have limiting := le_of_tendsto_of_tendsto
    (left_continuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    (right_continuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
    (show ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      first * root (fun index => x index + epsilon) +
        second * root (fun index => y index + epsilon) ≤
          root (first • (fun index => x index + epsilon) +
            second • (fun index => y index + epsilon)) from by
      filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
      exact positive_concavity.2
        (fun index => add_pos_of_nonneg_of_pos (hx index) hepsilon)
        (fun index => add_pos_of_nonneg_of_pos (hy index) hepsilon) hfirst hsecond weights)
  simpa using limiting

#check @evaluateAt_line_hasDerivAt
#check @spanningPolynomial_root_concaveOn
#print axioms evaluateAt_line_hasDerivAt
#print axioms spanningPolynomial_root_concaveOn

end D5.S3.Resource.SimplexCoverageRoot
