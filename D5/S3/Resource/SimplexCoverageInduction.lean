/- GID: D5/S3/Resource/SimplexCoverageInduction
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoverageInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree induction for the actual represented spanning-polynomial reverse Hessian bound. -/

import D5.S3.Resource.SimplexCoveragePolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoverageInduction

open scoped BigOperators
open Matrix SimplexCoveragePolynomial

variable {K V Index : Type*}
variable [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype Index] [DecidableEq Index]

set_option maxHeartbeats 2000000 in
theorem spanningPolynomial_reverse
    (columns : Index → V) (U : Submodule K V) (degree : ℕ) (x y : Index → ℝ)
    (positive : ∀ index, 0 < x index) :
    (degree : ℝ) * evaluateAt x (spanningPolynomial columns U degree) *
        (y ⬝ᵥ (spanningHessian columns U degree x *ᵥ y)) ≤
      ((degree : ℝ) - 1) *
        ((fun index => evaluateAt x (MvPolynomial.pderiv index
          (spanningPolynomial columns U degree))) ⬝ᵥ y) ^ 2 := by
  classical
  have homogeneous (W : Submodule K V) (order : ℕ) :
      (spanningPolynomial columns W order).IsHomogeneous order := by
    intro alpha coefficient
    change Finsupp.weight (fun _ : Index => (1 : ℕ)) alpha = order
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
    by_contra wrong_degree
    rw [spanningPolynomial_coeff, if_neg (by
      intro conditions
      exact wrong_degree conditions.1)] at coefficient
    exact coefficient rfl
  have euler (polynomial : MvPolynomial Index ℚ) (order : ℕ)
      (homogeneity : polynomial.IsHomogeneous order) :
      (∑ index, x index * evaluateAt x (MvPolynomial.pderiv index polynomial)) =
        (order : ℝ) * evaluateAt x polynomial := by
    have identity := congrArg (evaluateAt x) homogeneity.sum_X_mul_pderiv
    simpa [evaluateAt, MvPolynomial.eval₂_sum, nsmul_eq_mul] using identity
  have constant_derivative (W : Submodule K V) (index : Index) :
      MvPolynomial.pderiv index (spanningPolynomial columns W 0) = 0 := by
    have degree_zero : (spanningPolynomial columns W 0).totalDegree = 0 := by
      rw [MvPolynomial.totalDegree_zero_iff_isHomogeneous]
      exact homogeneous W 0
    have constant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp degree_zero
    rw [constant, MvPolynomial.pderiv_C]
  cases isEmpty_or_nonempty Index with
  | inl empty =>
    let := empty
    simp [dotProduct, mulVec]
  | inr nonempty =>
    let := nonempty
    induction degree using Nat.strong_induction_on generalizing U y with
    | h degree induction =>
      by_cases spanning : U ⊔ Submodule.span K (Set.range columns) = ⊤
      · by_cases small : degree < 2
        · interval_cases degree
          · simp [constant_derivative, evaluateAt, dotProduct]
          · have hessian_zero : spanningHessian columns U 1 x = 0 := by
              ext row column
              simp [spanningHessian, spanningPolynomial_pderiv,
                constant_derivative, evaluateAt]
            simp [hessian_zero]
        · by_cases base : degree = 2
          · subst degree
            simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
              using spanningPolynomial_degree_two_reverse columns U x y
                (fun index => (positive index).le)
          · obtain ⟨order, rfl⟩ : ∃ order, degree = order + 3 := by
              exact ⟨degree - 3, by omega⟩
            let extension (index : Index) := U ⊔ Submodule.span K {columns index}
            let value := evaluateAt x (spanningPolynomial columns U (order + 3))
            let gradient (index : Index) :=
              evaluateAt x (spanningPolynomial columns (extension index) (order + 2))
            let hessian := spanningHessian columns U (order + 3) x
            let contracted (index : Index) :=
              spanningHessian columns (extension index) (order + 2) x
            have enlarged_spanning (W : Submodule K V) (containment : U ≤ W) :
                W ⊔ Submodule.span K (Set.range columns) = ⊤ := by
              apply top_unique
              rw [← spanning]
              exact sup_le_sup containment le_rfl
            have gradient_identity (index : Index) :
                evaluateAt x (MvPolynomial.pderiv index
                  (spanningPolynomial columns U (order + 3))) = gradient index := by
              exact congrArg (evaluateAt x)
                (spanningPolynomial_pderiv columns U (order + 2) index)
            have hessian_entry (row column : Index) :
                hessian row column = evaluateAt x (spanningPolynomial columns
                  (extension column ⊔ Submodule.span K {columns row}) (order + 1)) := by
              dsimp [hessian, spanningHessian]
              rw [show order + 3 = (order + 2) + 1 by omega, spanningPolynomial_pderiv,
                show order + 2 = (order + 1) + 1 by omega, spanningPolynomial_pderiv]
            have symmetric_entries (row column : Index) :
                hessian row column = hessian column row := by
              rw [hessian_entry, hessian_entry]
              congr 2
              dsimp [extension]
              ac_rfl
            have hessian_nonnegative (row column : Index) : 0 ≤ hessian row column := by
              rw [hessian_entry]
              exact (spanningPolynomial_positive_iff columns _ (order + 1) x positive
                (enlarged_spanning _ (le_sup_left.trans le_sup_left))).1
            have gradient_nonnegative (index : Index) : 0 ≤ gradient index := by
              exact (spanningPolynomial_positive_iff columns _ (order + 2) x positive
                (enlarged_spanning _ le_sup_left)).1
            have gradient_euler : (∑ index, x index * gradient index) =
                ((order : ℝ) + 3) * value := by
              simpa only [gradient_identity, Nat.cast_add, Nat.cast_ofNat] using
                euler _ (order + 3) (homogeneous U (order + 3))
            have lower_gradient (index column : Index) :
                evaluateAt x (MvPolynomial.pderiv column
                  (spanningPolynomial columns (extension index) (order + 2))) =
                    hessian index column := by
              rw [symmetric_entries, hessian_entry]
              exact congrArg (evaluateAt x)
                (spanningPolynomial_pderiv columns (extension index) (order + 1) column)
            have hessian_euler (row : Index) :
                (hessian *ᵥ x) row = ((order : ℝ) + 2) * gradient row := by
              have identity := euler _ (order + 2) (homogeneous (extension row) (order + 2))
              simp only [lower_gradient, Nat.cast_add, Nat.cast_ofNat] at identity
              simpa only [mulVec, dotProduct, mul_comm] using identity
            have inactive_zero (index : Index) (inactive : ¬0 < gradient index) :
                spanningPolynomial columns (extension index) (order + 2) = 0 := by
              have criterion := (spanningPolynomial_positive_iff columns (extension index)
                (order + 2) x positive
                (enlarged_spanning (extension index) le_sup_left)).2
              have obstruction : order + 2 < Module.finrank K (V ⧸ extension index) := by
                exact Nat.lt_of_not_ge (fun bound => inactive (criterion.mpr bound))
              exact spanningPolynomial_eq_zero_of_rank_or_span columns _ _ (Or.inl obstruction)
            have inactive_row (index : Index) (inactive : ¬0 < gradient index)
                (column : Index) : hessian index column = 0 := by
              rw [← lower_gradient, inactive_zero index inactive]
              simp [evaluateAt]
            have inactive_contracted (index : Index) (inactive : ¬0 < gradient index) :
                contracted index = 0 := by
              ext row column
              simp [contracted, spanningHessian, inactive_zero index inactive, evaluateAt]
            have contracted_entry (index row column : Index) :
                contracted index row column = evaluateAt x (spanningPolynomial columns
                  ((extension index ⊔ Submodule.span K {columns column}) ⊔
                    Submodule.span K {columns row}) order) := by
              dsimp [contracted, spanningHessian]
              rw [show order + 2 = (order + 1) + 1 by omega, spanningPolynomial_pderiv,
                spanningPolynomial_pderiv]
            have third_euler (row column : Index) :
                (∑ index, x index * contracted index row column) =
                  ((order : ℝ) + 1) * hessian row column := by
              rw [hessian_entry]
              have identity := euler _ (order + 1)
                (homogeneous (extension column ⊔ Submodule.span K {columns row}) (order + 1))
              simp only [spanningPolynomial_pderiv, Nat.cast_add, Nat.cast_one] at identity
              rw [← identity]
              apply Finset.sum_congr rfl
              intro index _
              rw [contracted_entry]
              congr 3
              dsimp [extension]
              ac_rfl
            have quadratic_euler (vector : Index → ℝ) :
                (∑ index, x index * (vector ⬝ᵥ (contracted index *ᵥ vector))) =
                  ((order : ℝ) + 1) * (vector ⬝ᵥ (hessian *ᵥ vector)) := by
              simp only [dotProduct, mulVec, Finset.mul_sum]
              rw [Finset.sum_comm]
              calc
                _ = ∑ row, ∑ column, vector row *
                    (∑ index, x index * contracted index row column) * vector column := by
                  apply Finset.sum_congr rfl
                  intro row _
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro column _
                  simp only [Finset.sum_mul, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro index _
                  ring
                _ = _ := by
                  simp only [third_euler]
                  apply Finset.sum_congr rfl
                  intro row _
                  apply Finset.sum_congr rfl
                  intro column _
                  ring
            let diagonal (index : Index) :=
              if 0 < gradient index then x index / (((order : ℝ) + 2) * gradient index)
              else 0
            have quadratic_bootstrap (vector : Index → ℝ) :
                vector ⬝ᵥ (hessian *ᵥ vector) ≤
                  ∑ index, diagonal index * ((hessian *ᵥ vector) index) ^ 2 := by
              have term_bound (index : Index) :
                  x index * (vector ⬝ᵥ (contracted index *ᵥ vector)) ≤
                    ((order : ℝ) + 1) * diagonal index *
                      ((hessian *ᵥ vector) index) ^ 2 := by
                by_cases active : 0 < gradient index
                · have lower := induction (order + 2) (by omega) (extension index) vector
                  simp only [Nat.cast_add, Nat.cast_ofNat, lower_gradient] at lower
                  change ((order : ℝ) + 2) * gradient index *
                    (vector ⬝ᵥ (contracted index *ᵥ vector)) ≤
                      ((order : ℝ) + 2 - 1) * ((hessian *ᵥ vector) index) ^ 2 at lower
                  have denominator : 0 < ((order : ℝ) + 2) * gradient index := by positivity
                  have scaled := mul_le_mul_of_nonneg_left lower
                    (div_nonneg (positive index).le denominator.le)
                  dsimp [diagonal]
                  rw [if_pos active]
                  calc
                    _ = (x index / (((order : ℝ) + 2) * gradient index)) *
                        (((order : ℝ) + 2) * gradient index *
                          (vector ⬝ᵥ (contracted index *ᵥ vector))) := by
                      rw [← mul_assoc, div_mul_cancel₀ _ denominator.ne']
                    _ ≤ _ := scaled
                    _ = _ := by ring
                · rw [inactive_contracted index active]
                  simp [diagonal, active]
              have summed := Finset.sum_le_sum (fun index (_ : index ∈ Finset.univ) =>
                term_bound index)
              rw [quadratic_euler] at summed
              simp only [mul_assoc, ← Finset.mul_sum] at summed
              exact (mul_le_mul_iff_right₀ (show 0 < (order : ℝ) + 1 by positivity)).mp summed
            by_cases value_positive : 0 < value
            · let Active := {index : Index // 0 < gradient index}
              have active_exists : ∃ index, 0 < gradient index := by
                by_contra absent
                have all_zero : ∀ index, gradient index = 0 := by
                  intro index
                  exact le_antisymm (le_of_not_gt (fun active => absent ⟨index, active⟩))
                    (gradient_nonnegative index)
                simp only [all_zero, mul_zero, Finset.sum_const_zero] at gradient_euler
                have degree_positive : 0 < (order : ℝ) + 3 := by positivity
                nlinarith
              have : Nonempty Active := by
                obtain ⟨index, active⟩ := active_exists
                exact ⟨⟨index, active⟩⟩
              have active_sum (function : Index → ℝ)
                  (vanishing : ∀ index, ¬0 < gradient index → function index = 0) :
                  (∑ index : Active, function index.1) = ∑ index, function index := by
                have split := Fintype.sum_subtype_add_sum_subtype
                  (fun index => 0 < gradient index) function
                have complement_zero :
                    (∑ index : {index : Index // ¬0 < gradient index}, function index.1) = 0 := by
                  apply Finset.sum_eq_zero
                  intro index _
                  exact vanishing index.1 index.2
                simpa only [complement_zero, add_zero] using split
              let scale (index : Index) := Real.sqrt (diagonal index)
              have diagonal_positive (index : Active) : 0 < diagonal index.1 := by
                dsimp [diagonal]
                rw [if_pos index.2]
                exact div_pos (positive index.1) (mul_pos (by positivity) index.2)
              have scale_positive (index : Active) : 0 < scale index.1 :=
                Real.sqrt_pos.mpr (diagonal_positive index)
              have scale_square (index : Active) :
                  scale index.1 * scale index.1 = diagonal index.1 :=
                Real.mul_self_sqrt (diagonal_positive index).le
              have scale_balance (index : Active) :
                  scale index.1 * scale index.1 *
                    (((order : ℝ) + 2) * gradient index.1) = x index.1 := by
                rw [scale_square]
                dsimp [diagonal]
                rw [if_pos index.2, div_mul_cancel₀]
                exact (mul_pos (by positivity) index.2).ne'
              let normalized : Matrix Active Active ℝ :=
                fun row column => scale row.1 * hessian row.1 column.1 * scale column.1
              let fixed_vector (index : Active) := x index.1 / scale index.1
              have normalized_symmetric : normalized.IsSymm := by
                ext row column
                change scale column.1 * hessian column.1 row.1 * scale row.1 =
                  scale row.1 * hessian row.1 column.1 * scale column.1
                rw [symmetric_entries column.1 row.1]
                ring
              have normalized_nonnegative (row column : Active) :
                  0 ≤ normalized row column := by
                exact mul_nonneg (mul_nonneg (scale_positive row).le
                  (hessian_nonnegative row.1 column.1)) (scale_positive column).le
              have fixed_positive (index : Active) : 0 < fixed_vector index :=
                div_pos (positive index.1) (scale_positive index)
              have normalized_fixed : normalized *ᵥ fixed_vector = fixed_vector := by
                funext row
                calc
                  (normalized *ᵥ fixed_vector) row = scale row.1 *
                      (∑ column : Active, hessian row.1 column.1 * x column.1) := by
                    simp only [mulVec, dotProduct, normalized, fixed_vector, Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro column _
                    field_simp [(scale_positive column).ne']
                  _ = scale row.1 * (hessian *ᵥ x) row.1 := by
                    rw [active_sum (fun column => hessian row.1 column * x column)
                      (fun column inactive => by
                        rw [symmetric_entries, inactive_row column inactive, zero_mul])]
                    rfl
                  _ = fixed_vector row := by
                    rw [hessian_euler]
                    dsimp [fixed_vector]
                    apply (eq_div_iff (scale_positive row).ne').mpr
                    nlinarith [scale_balance row]
              have normalized_connected (support : Finset Active)
                  (support_nonempty : support.Nonempty) (proper : support ≠ Finset.univ) :
                  ∃ row ∈ support, ∃ column ∉ support, 0 < normalized row column := by
                let equivalence : Active ≃ {index : Index // 0 < evaluateAt x
                    (MvPolynomial.pderiv index (spanningPolynomial columns U (order + 3)))} :=
                  { toFun := fun index => ⟨index.1, by rw [gradient_identity]; exact index.2⟩
                    invFun := fun index => ⟨index.1, by
                      have property := index.2
                      rw [gradient_identity] at property
                      exact property⟩
                    left_inv := fun _ => rfl
                    right_inv := fun _ => rfl }
                have mapped_proper : support.map equivalence.toEmbedding ≠ Finset.univ := by
                  intro equality
                  apply proper
                  apply Finset.eq_univ_iff_forall.mpr
                  intro index
                  have member : equivalence index ∈ support.map equivalence.toEmbedding := by
                    rw [equality]
                    exact Finset.mem_univ _
                  simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using member
                obtain ⟨row, row_member, column, column_absent, crossing⟩ :=
                  spanningHessian_active_connected columns U (order + 1) x positive spanning
                    (support.map equivalence.toEmbedding)
                    support_nonempty.map mapped_proper
                refine ⟨equivalence.symm row, Finset.mem_map_equiv.mp row_member,
                  equivalence.symm column, ?_, ?_⟩
                · exact fun member => column_absent (Finset.mem_map_equiv.mpr member)
                · exact mul_pos (mul_pos (scale_positive (equivalence.symm row)) crossing)
                    (scale_positive (equivalence.symm column))
              let lift (vector : Active → ℝ) (index : Index) :=
                if active : 0 < gradient index then scale index * vector ⟨index, active⟩ else 0
              have lift_active (vector : Active → ℝ) (index : Active) :
                  lift vector index.1 = scale index.1 * vector index := by
                simp only [lift, dif_pos index.2]
                rfl
              have lift_inactive (vector : Active → ℝ) (index : Index)
                  (inactive : ¬0 < gradient index) : lift vector index = 0 := by
                simp only [lift, dif_neg inactive]
              have normalized_mul (vector : Active → ℝ) (row : Active) :
                  (normalized *ᵥ vector) row = scale row.1 * (hessian *ᵥ lift vector) row.1 := by
                calc
                  _ = scale row.1 *
                      (∑ column : Active, hessian row.1 column.1 * lift vector column.1) := by
                    simp only [mulVec, dotProduct, normalized, lift_active, Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro column _
                    ring
                  _ = _ := by
                    rw [active_sum (fun column => hessian row.1 column * lift vector column)
                      (fun column inactive => by
                        rw [lift_inactive vector column inactive, mul_zero])]
                    rfl
              have normalized_quadratic (vector : Active → ℝ) :
                  vector ⬝ᵥ (normalized *ᵥ vector) =
                    lift vector ⬝ᵥ (hessian *ᵥ lift vector) := by
                simp only [dotProduct, normalized_mul]
                rw [← active_sum (fun index => lift vector index *
                  (hessian *ᵥ lift vector) index) (fun index inactive => by
                    rw [lift_inactive vector index inactive, zero_mul])]
                apply Finset.sum_congr rfl
                intro index _
                rw [lift_active]
                ring
              have normalized_square (vector : Active → ℝ) :
                  vector ⬝ᵥ ((normalized * normalized) *ᵥ vector) =
                    ∑ index, diagonal index * ((hessian *ᵥ lift vector) index) ^ 2 := by
                rw [← mulVec_mulVec]
                have pairing (left right : Active → ℝ) :
                    left ⬝ᵥ (normalized *ᵥ right) = right ⬝ᵥ (normalized *ᵥ left) := by
                  calc
                    _ = left ⬝ᵥ (normalizedᵀ *ᵥ right) := by rw [normalized_symmetric]
                    _ = _ := dotProduct_transpose_mulVec _ _ _
                rw [pairing]
                simp only [dotProduct, normalized_mul]
                rw [← active_sum (fun index => diagonal index *
                  ((hessian *ᵥ lift vector) index) ^ 2) (fun index inactive => by
                    simp [diagonal, inactive])]
                apply Finset.sum_congr rfl
                intro index _
                rw [← scale_square index]
                ring
              have normalized_bootstrap (vector : Active → ℝ) :
                  vector ⬝ᵥ (normalized *ᵥ vector) ≤
                    vector ⬝ᵥ ((normalized * normalized) *ᵥ vector) := by
                rw [normalized_quadratic, normalized_square]
                exact quadratic_bootstrap (lift vector)
              have transverse (vector : Index → ℝ)
                  (perpendicular : gradient ⬝ᵥ vector = 0) :
                  vector ⬝ᵥ (hessian *ᵥ vector) ≤ 0 := by
                let normalized_vector (index : Active) := vector index.1 / scale index.1
                have normalized_perpendicular : normalized_vector ⬝ᵥ fixed_vector = 0 := by
                  calc
                    _ = ((order : ℝ) + 2) *
                        (∑ index : Active, gradient index.1 * vector index.1) := by
                      simp only [dotProduct, normalized_vector, fixed_vector, Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro index _
                      rw [← scale_balance index]
                      field_simp [(scale_positive index).ne']
                    _ = ((order : ℝ) + 2) * (gradient ⬝ᵥ vector) := by
                      rw [active_sum (fun index => gradient index * vector index)
                        (fun index inactive => by
                          have zero : gradient index = 0 := le_antisymm
                            (le_of_not_gt inactive) (gradient_nonnegative index)
                          rw [zero, zero_mul])]
                      rfl
                    _ = 0 := by rw [perpendicular, mul_zero]
                have bound := SimplexCoverageHessian.quadratic_nonpos_of_connected_normalization
                  normalized fixed_vector normalized_symmetric normalized_nonnegative
                  fixed_positive normalized_fixed normalized_connected normalized_bootstrap
                  normalized_vector normalized_perpendicular
                have active_lift (index : Active) :
                    lift normalized_vector index.1 = vector index.1 := by
                  rw [lift_active]
                  dsimp [normalized_vector]
                  exact mul_div_cancel₀ _ (scale_positive index).ne'
                have action_equal : hessian *ᵥ lift normalized_vector = hessian *ᵥ vector := by
                  funext row
                  apply Finset.sum_congr rfl
                  intro column _
                  change hessian row column * lift normalized_vector column =
                    hessian row column * vector column
                  by_cases active : 0 < gradient column
                  · rw [active_lift ⟨column, active⟩]
                  · rw [symmetric_entries, inactive_row column active]
                    simp
                rw [normalized_quadratic, action_equal] at bound
                have quadratic_equal : lift normalized_vector ⬝ᵥ (hessian *ᵥ vector) =
                    vector ⬝ᵥ (hessian *ᵥ vector) := by
                  apply Finset.sum_congr rfl
                  intro index _
                  by_cases active : 0 < gradient index
                  · rw [active_lift ⟨index, active⟩]
                  · have row_zero : (hessian *ᵥ vector) index = 0 := by
                      simp only [mulVec, dotProduct, inactive_row index active,
                        zero_mul, Finset.sum_const_zero]
                    rw [row_zero]
                    simp
                rwa [quadratic_equal] at bound
              have symmetric_pairing (left right : Index → ℝ) :
                  left ⬝ᵥ (hessian *ᵥ right) = right ⬝ᵥ (hessian *ᵥ left) := by
                simp only [dotProduct, mulVec, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro row _
                apply Finset.sum_congr rfl
                intro column _
                rw [symmetric_entries]
                ring
              have gradient_x : gradient ⬝ᵥ x = ((order : ℝ) + 3) * value := by
                rw [dotProduct_comm]
                exact gradient_euler
              have mixed (vector : Index → ℝ) :
                  x ⬝ᵥ (hessian *ᵥ vector) = ((order : ℝ) + 2) * (gradient ⬝ᵥ vector) := by
                rw [symmetric_pairing]
                simp only [dotProduct, hessian_euler, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro index _
                ring
              have quadratic_x : x ⬝ᵥ (hessian *ᵥ x) =
                  ((order : ℝ) + 3) * ((order : ℝ) + 2) * value := by
                rw [mixed, gradient_x]
                ring
              let scalar := (gradient ⬝ᵥ y) / (((order : ℝ) + 3) * value)
              have denominator_positive : 0 < ((order : ℝ) + 3) * value := by positivity
              have scalar_identity : scalar * (((order : ℝ) + 3) * value) =
                  gradient ⬝ᵥ y := div_mul_cancel₀ _ denominator_positive.ne'
              have perpendicular : gradient ⬝ᵥ (y - scalar • x) = 0 := by
                simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, gradient_x,
                  scalar_identity, sub_self]
              have expansion : (y - scalar • x) ⬝ᵥ (hessian *ᵥ (y - scalar • x)) =
                  y ⬝ᵥ (hessian *ᵥ y) - 2 * scalar * ((order : ℝ) + 2) *
                    (gradient ⬝ᵥ y) + scalar ^ 2 *
                      (((order : ℝ) + 3) * ((order : ℝ) + 2) * value) := by
                simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
                  smul_dotProduct, dotProduct_smul, smul_eq_mul]
                rw [symmetric_pairing y x, mixed, quadratic_x]
                ring
              have scaled := mul_le_mul_of_nonneg_left
                (transverse (y - scalar • x) perpendicular) denominator_positive.le
              rw [expansion, mul_zero] at scaled
              have cancellation : ((order : ℝ) + 3) * value *
                  (y ⬝ᵥ (hessian *ᵥ y) - 2 * scalar * ((order : ℝ) + 2) *
                    (gradient ⬝ᵥ y) + scalar ^ 2 *
                      (((order : ℝ) + 3) * ((order : ℝ) + 2) * value)) =
                  ((order : ℝ) + 3) * value * (y ⬝ᵥ (hessian *ᵥ y)) -
                    ((order : ℝ) + 2) * (gradient ⬝ᵥ y) ^ 2 := by
                calc
                  _ = ((order : ℝ) + 3) * value * (y ⬝ᵥ (hessian *ᵥ y)) -
                      2 * ((order : ℝ) + 2) *
                        (scalar * (((order : ℝ) + 3) * value)) * (gradient ⬝ᵥ y) +
                      ((order : ℝ) + 2) *
                        (scalar * (((order : ℝ) + 3) * value)) ^ 2 := by ring
                  _ = _ := by rw [scalar_identity]; ring
              rw [cancellation] at scaled
              simp only [Nat.cast_add, Nat.cast_ofNat, gradient_identity]
              change ((order : ℝ) + 3) * value * (y ⬝ᵥ (hessian *ᵥ y)) ≤
                ((order : ℝ) + 3 - 1) * (gradient ⬝ᵥ y) ^ 2
              linarith
            · have value_zero : value = 0 := le_antisymm (le_of_not_gt value_positive)
                (spanningPolynomial_positive_iff columns U (order + 3) x positive spanning).1
              change ((order + 3 : ℕ) : ℝ) * value * _ ≤ _
              rw [value_zero, mul_zero, zero_mul]
              apply mul_nonneg
              · simp only [Nat.cast_add, Nat.cast_ofNat]
                have order_nonnegative : (0 : ℝ) ≤ order := Nat.cast_nonneg _
                linarith
              · exact sq_nonneg _
      · have zero := spanningPolynomial_eq_zero_of_rank_or_span columns U degree
          (Or.inr spanning)
        simp [zero, evaluateAt, dotProduct]

end D5.S3.Resource.SimplexCoverageInduction

#check @D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse
#print axioms D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse
