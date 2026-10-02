/- GID: D5/S3/Resource/SimplexCoverageOptimality
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoverageOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simplex minimizes original uniform physical iid expected full-span retrieval time. -/

import D5.S3.Resource.SimplexCoverageRoot
import D5.S3.Resource.SimplexCoverageWords
import D5.S3.Resource.SimplexCoverageProbability
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoverageOptimality

open MeasureTheory
open scoped BigOperators ENNReal
open SimplexCoveragePolynomial SimplexCoverageWords MinimumRetrievalTime

set_option maxHeartbeats 1500000 in
theorem result {K : Type*} [Field K] [Fintype K]
    (dimension : ℕ) (dimension_bound : 2 ≤ dimension)
    (generator simplex : Matrix (Fin dimension)
      (Fin ((Fintype.card K ^ dimension - 1) / (Fintype.card K - 1))) K)
    (generator_rank : generator.rank = dimension)
    (simplex_nonzero : ∀ index, simplex.col index ≠ 0)
    (simplex_complete : Function.Bijective
      (fun index => Projectivization.mk K (simplex.col index) (simplex_nonzero index))) :
    letI : Nonempty (Fin ((Fintype.card K ^ dimension - 1) / (Fintype.card K - 1))) := by
      have nonzero : (fun _ : Fin dimension => (1 : K)) ≠ 0 := by
        intro vanishes
        exact one_ne_zero (congrFun vanishes ⟨0, by omega⟩)
      obtain ⟨index, _⟩ := simplex_complete.2 (Projectivization.mk K _ nonzero)
      exact ⟨index⟩
    (∫ sample, (retrievalTime simplex.col (⊤ : Submodule K (Fin dimension → K)) sample).toReal
      ∂uniformSamples (Fin ((Fintype.card K ^ dimension - 1) / (Fintype.card K - 1)))) ≤
    ∫ sample, (retrievalTime generator.col (⊤ : Submodule K (Fin dimension → K)) sample).toReal
      ∂uniformSamples (Fin ((Fintype.card K ^ dimension - 1) / (Fintype.card K - 1))) := by
  classical
  let V := Fin dimension → K
  let P := Projectivization K V
  let length := (Fintype.card K ^ dimension - 1) / (Fintype.card K - 1)
  let Index := Fin length
  let _ : Fintype P := Fintype.ofFinite P
  let _ : MeasurableSpace P := ⊤
  let _ : MeasurableSingletonClass P := ⟨fun _ => MeasurableSet.of_discrete⟩
  let fixed : V := fun _ => 1
  have fixed_nonzero : fixed ≠ 0 := by
    intro vanishes
    exact one_ne_zero (congrFun vanishes ⟨0, by omega⟩)
  let _ : Nonempty P := ⟨Projectivization.mk K fixed fixed_nonzero⟩
  have projective_card : Fintype.card P = length := by
    simpa [P, V, length, Nat.card_eq_fintype_card, Fintype.card_fun] using
      Projectivization.card'' K V
  have length_positive : 0 < length := by
    rw [← projective_card]
    exact Fintype.card_pos
  let _ : NeZero length := ⟨Nat.ne_of_gt length_positive⟩
  have generator_full : Submodule.span K (Set.range generator.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← generator.rank_eq_finrank_span_cols, generator_rank]
    simp
  let replacement : Index → V := fun index =>
    if generator.col index = 0 then fixed else generator.col index
  have replacement_nonzero : ∀ index, replacement index ≠ 0 := by
    intro index
    dsimp [replacement]
    split_ifs with vanishes
    · exact fixed_nonzero
    · exact vanishes
  have prefix_containment (sample : ℕ → Index) (time : ℕ) :
      prefixSpan (K := K) generator.col sample time ≤
        prefixSpan (K := K) replacement sample time := by
    apply Submodule.span_le.mpr
    rintro vector ⟨position, rfl⟩
    change generator.col (sample position) ∈ prefixSpan (K := K) replacement sample time
    by_cases vanishes : generator.col (sample position) = 0
    · rw [vanishes]
      exact Submodule.zero_mem _
    · have unchanged : replacement (sample position) = generator.col (sample position) := by
        simp [replacement, vanishes]
      rw [← unchanged]
      exact Submodule.subset_span ⟨position, rfl⟩
  have global_containment : Submodule.span K (Set.range generator.col) ≤
      Submodule.span K (Set.range replacement) := by
    apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    by_cases vanishes : generator.col index = 0
    · rw [vanishes]
      exact Submodule.zero_mem _
    · have unchanged : replacement index = generator.col index := by
        simp [replacement, vanishes]
      rw [← unchanged]
      exact Submodule.subset_span ⟨index, rfl⟩
  have replacement_full : Submodule.span K (Set.range replacement) = ⊤ := by
    apply top_le_iff.mp
    simpa [generator_full] using global_containment
  let alphabet_equiv : Index ≃ P := Equiv.ofBijective _ simplex_complete
  let representatives : P → V := fun point => simplex.col (alphabet_equiv.symm point)
  have representative_nonzero : ∀ point, representatives point ≠ 0 := by
    intro point
    exact simplex_nonzero _
  have represents : ∀ point,
      Projectivization.mk K (representatives point) (representative_nonzero point) = point := by
    intro point
    exact alphabet_equiv.apply_symm_apply point
  have representative_span (point : P) :
      Submodule.span K {representatives point} = point.submodule := by
    rw [← Projectivization.submodule_mk (representatives point)
      (representative_nonzero point), represents]
  have representatives_full : Submodule.span K (Set.range representatives) = ⊤ := by
    apply top_le_iff.mp
    intro vector _
    by_cases vanishes : vector = 0
    · rw [vanishes]
      exact Submodule.zero_mem _
    · let point := Projectivization.mk K vector vanishes
      have member : vector ∈ Submodule.span K {representatives point} := by
        rw [representative_span, Projectivization.submodule_mk]
        exact Submodule.subset_span (Set.mem_singleton vector)
      have subset : {representatives point} ⊆ Set.range representatives := by
        rintro _ rfl
        exact ⟨point, rfl⟩
      exact (Submodule.span_mono subset) member
  have simplex_full : Submodule.span K (Set.range simplex.col) = ⊤ := by
    apply top_le_iff.mp
    rw [← representatives_full]
    apply Submodule.span_mono
    rintro vector ⟨point, rfl⟩
    exact ⟨alphabet_equiv.symm point, rfl⟩
  have projective_maximum
      (columns : P → V) (nonzero : ∀ point, columns point ≠ 0)
      (represents : ∀ point, Projectivization.mk K (columns point) (nonzero point) = point)
      (degree : ℕ) (x : P → ℝ)
      (nonnegative : ∀ point, 0 ≤ x point) (mass : ∑ point, x point = 1) :
      evaluateAt x (spanningPolynomial columns (⊥ : Submodule K V) degree) ≤
        evaluateAt (fun _ => (Fintype.card P : ℝ)⁻¹)
          (spanningPolynomial columns (⊥ : Submodule K V) degree) := by
    classical
    let _ : Fintype K := Fintype.ofFinite K
    let P := Projectivization K (Fin dimension → K)
    let V := Fin dimension → K
    let G := LinearMap.GeneralLinearGroup K V
    let _ : Fintype G := Fintype.ofEquiv (Matrix.GeneralLinearGroup (Fin dimension) K)
      Matrix.GeneralLinearGroup.toLin.toEquiv
    have : MulAction.IsPretransitive G P :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have : Nonempty P := ⟨Projectivization.mk K (fun _ => (1 : K)) (by
      intro vanishes
      have coordinate := congrFun vanishes ⟨0, by omega⟩
      exact one_ne_zero coordinate)⟩
    let polynomial := spanningPolynomial columns (⊥ : Submodule K V) degree
    have factorial_pos : 0 < (degree.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos degree
    have word_evaluation (weights : P → ℝ) :
        evaluateAt weights (wordPolynomial columns (⊥ : Submodule K V) degree) =
          (degree.factorial : ℝ) * evaluateAt weights polynomial := by
      rw [wordPolynomial_eq_factorial_smul]
      simp [evaluateAt, polynomial, nsmul_eq_mul]
    have eval_nonnegative (weights : P → ℝ) (positive : ∀ point, 0 ≤ weights point) :
        0 ≤ evaluateAt weights polynomial := by
      have word_nonnegative :
          0 ≤ evaluateAt weights (wordPolynomial columns (⊥ : Submodule K V) degree) := by
        simp only [wordPolynomial, evaluateAt, MvPolynomial.eval₂_sum, bot_sup_eq]
        apply Finset.sum_nonneg
        intro word _
        split_ifs
        · simp only [MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]
          exact Finset.prod_nonneg (fun position _ => positive (word position))
        · simp
      rw [word_evaluation] at word_nonnegative
      exact nonneg_of_mul_nonneg_right word_nonnegative factorial_pos
    have singleton_span (point : P) :
        Submodule.span K {columns point} = point.submodule := by
      rw [← Projectivization.submodule_mk (columns point) (nonzero point), represents point]
    have transformed_span (element : G) (word : Fin degree → P) :
        Submodule.span K (Set.range (fun position => columns (element • word position))) =
          (Submodule.span K (Set.range (fun position => columns (word position)))).map
            element.toLinearEquiv.toLinearMap := by
      simp only [Submodule.span_range_eq_iSup, Submodule.map_iSup, singleton_span]
      apply iSup_congr
      intro position
      rw [← Projectivization.mk_rep (word position), Projectivization.smul_mk,
        Projectivization.submodule_mk, Projectivization.submodule_mk,
        Submodule.map_span, Set.image_singleton]
      rfl
    have full_span_invariant (element : G) (word : Fin degree → P) :
        Submodule.span K (Set.range (fun position => columns (element • word position))) = ⊤ ↔
          Submodule.span K (Set.range (fun position => columns (word position))) = ⊤ := by
      rw [transformed_span]
      simp
    have invariant (element : G) (weights : P → ℝ) :
        evaluateAt (fun point => weights (element⁻¹ • point)) polynomial =
          evaluateAt weights polynomial := by
      apply (mul_left_cancel₀ (ne_of_gt factorial_pos))
      rw [← word_evaluation, ← word_evaluation]
      simp only [wordPolynomial, evaluateAt, MvPolynomial.eval₂_sum, bot_sup_eq,
        apply_ite, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero]
      let word_permutation : (Fin degree → P) ≃ (Fin degree → P) :=
        Equiv.piCongrRight (fun _ => MulAction.toPerm element)
      symm
      apply Fintype.sum_equiv word_permutation
      intro word
      change (if Submodule.span K (Set.range (fun position => columns (word position))) = ⊤
        then ∏ position, weights (word position) else 0) =
        (if Submodule.span K (Set.range
          (fun position => columns (element • word position))) = ⊤
        then ∏ position, weights (element⁻¹ • (element • word position)) else 0)
      simp only [full_span_invariant, inv_smul_smul]
    let average : P → ℝ := fun point => (Fintype.card G : ℝ)⁻¹ *
      ∑ element : G, x (element⁻¹ • point)
    have group_card_pos : 0 < (Fintype.card G : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have point_card_pos : 0 < (Fintype.card P : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have average_mass : ∑ point, average point = 1 := by
      simp only [average, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have permuted_mass (element : G) : ∑ point : P, x (element⁻¹ • point) = 1 := by
        rw [← mass]
        apply Fintype.sum_equiv (MulAction.toPerm element⁻¹)
        intro point
        rfl
      simp_rw [permuted_mass]
      simp [ne_of_gt group_card_pos]
    have average_invariant (element : G) (point : P) :
        average (element • point) = average point := by
      dsimp [average]
      congr 1
      symm
      apply Fintype.sum_equiv (Equiv.mulLeft element)
      intro other
      simp [mul_smul]
    have average_constant (first second : P) : average first = average second := by
      obtain ⟨element, equality⟩ := MulAction.exists_smul_eq G first second
      rw [← equality, average_invariant]
    have average_uniform : average = fun _ => (Fintype.card P : ℝ)⁻¹ := by
      funext point
      have mass_at_point : (Fintype.card P : ℝ) * average point = 1 := by
        calc
          (Fintype.card P : ℝ) * average point = ∑ other : P, average point := by simp
          _ = ∑ other : P, average other := by
            apply Finset.sum_congr rfl
            intro other _
            exact average_constant point other
          _ = 1 := average_mass
      apply (mul_left_cancel₀ (ne_of_gt point_card_pos))
      rw [mass_at_point, mul_inv_cancel₀ (ne_of_gt point_card_pos)]
    by_cases degree_zero : degree = 0
    · subst degree
      apply le_of_eq
      apply (mul_left_cancel₀ (ne_of_gt factorial_pos))
      rw [← word_evaluation, ← word_evaluation]
      simp [wordPolynomial, evaluateAt, apply_ite]
    · have positive_degree : 1 ≤ degree := by omega
      have exponent_pos : 0 < 1 / (degree : ℝ) := by
        apply one_div_pos.mpr
        exact_mod_cast (by omega : 0 < degree)
      have jensen :=
        (SimplexCoverageRoot.spanningPolynomial_root_concaveOn columns
          (⊥ : Submodule K V) degree positive_degree).le_map_sum
          (t := Finset.univ) (w := fun _ : G => (Fintype.card G : ℝ)⁻¹)
          (p := fun element point => x (element⁻¹ • point))
          (fun _ _ => (inv_pos.mpr group_card_pos).le)
          (by simp [ne_of_gt group_card_pos])
          (fun element _ point => nonnegative (element⁻¹ • point))
      have vector_average :
          (∑ element : G, (Fintype.card G : ℝ)⁻¹ •
            (fun point => x (element⁻¹ • point))) = average := by
        ext point
        simp [average, Finset.sum_apply, ← Finset.mul_sum]
      change (∑ element : G, (Fintype.card G : ℝ)⁻¹ •
        (evaluateAt (fun point => x (element⁻¹ • point)) polynomial) ^ (1 / (degree : ℝ))) ≤
        (evaluateAt (∑ element : G, (Fintype.card G : ℝ)⁻¹ •
          (fun point => x (element⁻¹ • point))) polynomial) ^ (1 / (degree : ℝ)) at jensen
      have orbit_root_sum :
          (∑ element : G, (Fintype.card G : ℝ)⁻¹ •
            (evaluateAt (fun point => x (element⁻¹ • point)) polynomial) ^
              (1 / (degree : ℝ))) =
            (evaluateAt x polynomial) ^ (1 / (degree : ℝ)) := by
        calc
          _ = ∑ _ : G, (Fintype.card G : ℝ)⁻¹ •
              (evaluateAt x polynomial) ^ (1 / (degree : ℝ)) := by
            apply Finset.sum_congr rfl
            intro element _
            rw [invariant element x]
          _ = _ := by simp [smul_eq_mul, ne_of_gt group_card_pos]
      rw [orbit_root_sum] at jensen
      rw [vector_average, average_uniform] at jensen
      have root_comparison :
          (evaluateAt x polynomial) ^ (1 / (degree : ℝ)) ≤
            (evaluateAt (fun _ => (Fintype.card P : ℝ)⁻¹) polynomial) ^
              (1 / (degree : ℝ)) := by
        simpa [polynomial, smul_eq_mul, ← Finset.sum_mul, ne_of_gt group_card_pos] using jensen
      exact (Real.rpow_le_rpow_iff (eval_nonnegative x nonnegative)
        (eval_nonnegative _ (fun _ => (inv_pos.mpr point_card_pos).le))
          exponent_pos).mp root_comparison
  have physical_comparison (columns : Index → V) (nonzero : ∀ index, columns index ≠ 0)
      (representatives : P → V) (representative_nonzero : ∀ point, representatives point ≠ 0)
      (represents : ∀ point,
        Projectivization.mk K (representatives point) (representative_nonzero point) = point)
      (time : ℕ) :
      uniformSamples Index {sample | recovered columns (⊤ : Submodule K V) time sample} =
        ENNReal.ofReal ((time.factorial : ℝ) *
          evaluateAt (fun point => ∑ index : Index,
            if Projectivization.mk K (columns index) (nonzero index) = point
            then (Fintype.card Index : ℝ)⁻¹ else 0)
            (spanningPolynomial representatives (⊥ : Submodule K V) time)) ∧
      uniformSamples Index {sample | recovered columns (⊤ : Submodule K V) time sample} ≤
        uniformSamples P {sample | recovered representatives (⊤ : Submodule K V) time sample} := by
    classical
    let P := Projectivization K (Fin dimension → K)
    let V := Fin dimension → K
    let ray : Index → P := fun index => Projectivization.mk K (columns index) (nonzero index)
    let weights : P → ℝ := fun point => ∑ index,
      if ray index = point then (Fintype.card Index : ℝ)⁻¹ else 0
    have index_card_pos : 0 < (Fintype.card Index : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have weight_nonnegative : ∀ point, 0 ≤ weights point := by
      intro point
      apply Finset.sum_nonneg
      intro index _
      split_ifs <;> positivity
    have weight_mass : ∑ point, weights point = 1 := by
      dsimp [weights, ray]
      rw [Finset.sum_comm]
      simp [ne_of_gt index_card_pos]
    have physical_span (word : Fin time → Index) :
        Submodule.span K (Set.range (fun position => columns (word position))) =
          Submodule.span K (Set.range
            (fun position => representatives (ray (word position)))) := by
      simp only [Submodule.span_range_eq_iSup]
      apply iSup_congr
      intro position
      rw [← Projectivization.submodule_mk (columns (word position)) (nonzero (word position)),
        ← Projectivization.submodule_mk (representatives (ray (word position)))
          (representative_nonzero (ray (word position))), represents]
    have transport (physical_weights : Index → ℝ) :
        evaluateAt physical_weights (wordPolynomial columns (⊥ : Submodule K V) time) =
          evaluateAt (fun point => ∑ index, if ray index = point then physical_weights index else 0)
            (wordPolynomial representatives (⊥ : Submodule K V) time) := by
      have fiber_product (word : Fin time → P) :
          (∏ position, ∑ index, if ray index = word position then physical_weights index else 0) =
            ∑ physical_word : Fin time → Index,
              if (fun position => ray (physical_word position)) = word
              then ∏ position, physical_weights (physical_word position) else 0 := by
        rw [Fintype.prod_sum]
        apply Finset.sum_congr rfl
        intro physical_word _
        by_cases same : (fun position => ray (physical_word position)) = word
        · simp only [if_pos same]
          apply Finset.prod_congr rfl
          intro position _
          rw [show ray (physical_word position) = word position from congrFun same position,
            if_pos rfl]
        · rw [if_neg same]
          obtain ⟨position, different⟩ := Function.ne_iff.mp same
          apply Finset.prod_eq_zero (Finset.mem_univ position)
          exact if_neg different
      simp only [wordPolynomial, evaluateAt, MvPolynomial.eval₂_sum, bot_sup_eq,
        apply_ite, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero]
      symm
      calc
        (∑ word : Fin time → P,
          if Submodule.span K (Set.range (fun position => representatives (word position))) = ⊤
          then ∏ position, ∑ index,
            if ray index = word position then physical_weights index else 0 else 0) =
          ∑ word : Fin time → P, ∑ physical_word : Fin time → Index,
            if (fun position => ray (physical_word position)) = word then
              (if Submodule.span K
                (Set.range (fun position => representatives (word position))) = ⊤
              then ∏ position, physical_weights (physical_word position) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro word _
          rw [fiber_product]
          by_cases spanning : Submodule.span K
              (Set.range (fun position => representatives (word position))) = ⊤
          · simp [spanning]
          · simp [spanning]
        _ = ∑ physical_word : Fin time → Index,
            if Submodule.span K
              (Set.range (fun position => representatives (ray (physical_word position)))) = ⊤
            then ∏ position, physical_weights (physical_word position) else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro physical_word _
          simp
        _ = _ := by
          apply Finset.sum_congr rfl
          intro physical_word _
          rw [physical_span]
    have weighted_polynomial :
        evaluateAt (fun _ => (Fintype.card Index : ℝ)⁻¹)
            (spanningPolynomial columns (⊥ : Submodule K V) time) =
          evaluateAt weights (spanningPolynomial representatives (⊥ : Submodule K V) time) := by
      have word_transport := transport (fun _ => (Fintype.card Index : ℝ)⁻¹)
      change evaluateAt (fun _ => (Fintype.card Index : ℝ)⁻¹)
          (wordPolynomial columns (⊥ : Submodule K V) time) =
        evaluateAt weights (wordPolynomial representatives (⊥ : Submodule K V) time)
          at word_transport
      rw [wordPolynomial_eq_factorial_smul, wordPolynomial_eq_factorial_smul] at word_transport
      have factorial_pos : 0 < (time.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos time
      apply (mul_left_cancel₀ (ne_of_gt factorial_pos))
      simpa [evaluateAt, nsmul_eq_mul] using word_transport
    have comparison := projective_maximum
      representatives representative_nonzero represents time weights
        weight_nonnegative weight_mass
    constructor
    · rw [SimplexCoverageProbability.uniformSamples_recovered_top, weighted_polynomial]
    · rw [SimplexCoverageProbability.uniformSamples_recovered_top,
        SimplexCoverageProbability.uniformSamples_recovered_top, weighted_polynomial]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left comparison (Nat.cast_nonneg _)
  have simplex_weights : (fun point : P => ∑ index : Index,
      if Projectivization.mk K (simplex.col index) (simplex_nonzero index) = point
      then (Fintype.card Index : ℝ)⁻¹ else 0) =
      fun _ => (Fintype.card P : ℝ)⁻¹ := by
    funext point
    change (∑ index : Index, if alphabet_equiv index = point
      then (Fintype.card Index : ℝ)⁻¹ else 0) = _
    have reindex : (∑ index : Index, if alphabet_equiv index = point
        then (Fintype.card Index : ℝ)⁻¹ else 0) =
        ∑ other : P, if other = point then (Fintype.card Index : ℝ)⁻¹ else 0 := by
      apply Fintype.sum_equiv alphabet_equiv
      intro index
      rfl
    rw [reindex]
    simp [Fintype.card_congr alphabet_equiv]
  have simplex_probability (time : ℕ) :
      uniformSamples Index {sample | recovered simplex.col (⊤ : Submodule K V) time sample} =
        uniformSamples P {sample | recovered representatives (⊤ : Submodule K V) time sample} := by
    rw [(physical_comparison simplex.col simplex_nonzero representatives
      representative_nonzero represents time).1, simplex_weights,
      SimplexCoverageProbability.uniformSamples_recovered_top]
  have recovery_comparison (time : ℕ) :
      uniformSamples Index {sample | recovered generator.col (⊤ : Submodule K V) time sample} ≤
        uniformSamples Index {sample | recovered simplex.col (⊤ : Submodule K V) time sample} := by
    calc
      _ ≤ uniformSamples Index
          {sample | recovered replacement (⊤ : Submodule K V) time sample} := by
        apply measure_mono
        intro sample recovery
        exact recovery.trans (prefix_containment sample time)
      _ ≤ uniformSamples P
          {sample | recovered representatives (⊤ : Submodule K V) time sample} :=
        (physical_comparison replacement replacement_nonzero representatives
          representative_nonzero represents time).2
      _ = _ := (simplex_probability time).symm
  have recovery_measurable (columns : Index → V) (time : ℕ) :
      MeasurableSet {sample | recovered columns (⊤ : Submodule K V) time sample} := by
    let words : Set (Fin time → Index) :=
      {word | (⊤ : Submodule K V) ≤
        Submodule.span K (Set.range (fun position => columns (word position)))}
    have prefix_measurable : Measurable (fun sample : ℕ → Index =>
        fun position : Fin time => sample position.val) :=
      measurable_pi_iff.mpr (fun position => measurable_pi_apply position.val)
    simpa only [words, recovered, prefixSpan, Set.preimage, Set.mem_ofPred_eq] using
      words.to_countable.measurableSet.preimage prefix_measurable
  have failure_comparison (time : ℕ) :
      uniformSamples Index {sample | ¬ recovered simplex.col (⊤ : Submodule K V) time sample} ≤
        uniformSamples Index
          {sample | ¬ recovered generator.col (⊤ : Submodule K V) time sample} := by
    let _ : IsProbabilityMeasure (uniformSamples Index) := by
      unfold uniformSamples
      infer_instance
    have simplex_complement := measure_compl (recovery_measurable simplex.col time)
      (measure_ne_top (uniformSamples Index) _)
    have generator_complement := measure_compl (recovery_measurable generator.col time)
      (measure_ne_top (uniformSamples Index) _)
    change uniformSamples Index
        ({sample | recovered simplex.col (⊤ : Submodule K V) time sample}ᶜ) ≤
      uniformSamples Index
        ({sample | recovered generator.col (⊤ : Submodule K V) time sample}ᶜ)
    rw [simplex_complement, generator_complement]
    exact tsub_le_tsub_left (recovery_comparison time) _
  obtain ⟨_, _, generator_tail, _, _, generator_finite, _, generator_real⟩ :=
    retrieval_time_probability_bridge generator.col (⊤ : Submodule K V)
      (by rw [generator_full])
  obtain ⟨_, _, simplex_tail, _, _, _, _, simplex_real⟩ :=
    retrieval_time_probability_bridge simplex.col (⊤ : Submodule K V)
      (by rw [simplex_full])
  rw [simplex_real, generator_real]
  apply ENNReal.toReal_mono (ne_of_lt generator_finite)
  rw [simplex_tail, generator_tail]
  exact ENNReal.tsum_le_tsum failure_comparison

end D5.S3.Resource.SimplexCoverageOptimality
