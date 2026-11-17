/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticCubicExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second and third moments split into distinct-index sums under a quadratic relation. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.IndexEqualityPatterns

/-! Quadratic relations evaluate the repeated-index contributions to finite moments. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing A] [Algebra ℝ A]

private lemma linear_algebraMap (ℓ : A →ₗ[ℝ] ℝ) (h1 : ℓ 1 = 1) (c : ℝ) :
    ℓ (algebraMap ℝ A c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul, mul_one]

/-- The second moment is the ordered distinct-index sum plus its diagonal contribution. -/
theorem quadratic_second_moment_eq
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g : ι → ℝ) :
    quadraticFamilyMoment ℓ Y ![f, g] = distinctIndexMoment ℓ Y ![f, g] + b * indexSum (f * g) := by
  classical
  rw [quadraticFamilyMoment_eq_tuple_sum, ← Finset.sum_filter_add_sum_filter_not _ Function.Injective]
  change distinctIndexMoment ℓ Y ![f, g] + _ = _
  congr 1
  have hdiag : (∑ x : Fin 2 → ι with ¬Function.Injective x,
      (∏ i, (![f, g] : Fin 2 → ι → ℝ) i (x i)) * ℓ (∏ i, Y (x i))) =
      ∑ d, (f d * g d) * ℓ (Y d ^ 2) := by
    symm
    apply Finset.sum_bij (fun d _ => fun _ : Fin 2 => d)
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hi
      exact Fin.zero_ne_one (hi (show d = d from rfl))
    · intro d hd e he hde
      exact congrFun hde 0
    · intro x hx
      have hx' : x 0 = x 1 := by
        by_contra hn
        apply (Finset.mem_filter.mp hx).2
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      refine ⟨x 0, Finset.mem_univ _, ?_⟩
      funext i
      fin_cases i <;> simp [hx']
    · intro d hd
      simp [Fin.prod_univ_two, pow_two]
  rw [hdiag]
  simp_rw [hquad, map_add, map_smul, h0, linear_algebraMap ℓ h1,
    smul_eq_mul, mul_zero, zero_add]
  simp only [indexSum, Pi.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The cubic moment splits into distinct triples, three repeated-pair terms,
and the contribution with all three indices equal. -/
theorem quadratic_third_moment_eq
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g h : ι → ℝ) :
    quadraticFamilyMoment ℓ Y ![f, g, h] = distinctIndexMoment ℓ Y ![f, g, h] +
      a * (distinctIndexMoment ℓ Y ![f * g, h] + distinctIndexMoment ℓ Y ![f * h, g] + distinctIndexMoment ℓ Y ![g * h, f]) +
      a * b * indexSum (f * g * h) := by
  classical
  have hsquare (d : ι) : ℓ (Y d ^ 2) = b := by
    simp [hquad, h0, linear_algebraMap ℓ h1]
  have hpair (d e : ι) : ℓ (Y d ^ 2 * Y e) = a * ℓ (Y d * Y e) := by
    rw [hquad, add_mul, smul_mul_assoc, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, map_add, map_smul, map_smul, h0]
    simp
  have hcube (d : ι) : ℓ (Y d ^ 3) = a * b := by
    rw [pow_succ, hquad, add_mul, smul_mul_assoc,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_add, map_smul, map_smul, ← pow_two, hsquare, h0]
    simp
  let F : (Fin 3 → ι) → ℝ := fun x =>
    (∏ i, (![f, g, h] : Fin 3 → ι → ℝ) i (x i)) * ℓ (∏ i, Y (x i))
  have h012 : patternSum3 (r := 3) ![0, 1, 2] F = distinctIndexMoment ℓ Y ![f, g, h] := by
    unfold patternSum3 distinctIndexMoment
    apply Finset.sum_congr rfl
    intro x hx
    simp [F, Fin.prod_univ_three, Function.comp_def]
  have h001 : patternSum3 (r := 2) ![0, 0, 1] F = a * distinctIndexMoment ℓ Y ![f * g, h] := by
    unfold patternSum3 distinctIndexMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_three, Fin.prod_univ_two, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    rw [← pow_two, hpair]
    ring
  have h010 : patternSum3 (r := 2) ![0, 1, 0] F = a * distinctIndexMoment ℓ Y ![f * h, g] := by
    unfold patternSum3 distinctIndexMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_three, Fin.prod_univ_two, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    rw [show Y (x 0) * Y (x 1) * Y (x 0) = Y (x 0) ^ 2 * Y (x 1) by ring, hpair]
    ring
  have h011 : patternSum3 (r := 2) ![0, 1, 1] F = a * distinctIndexMoment ℓ Y ![g * h, f] := by
    rw [distinctIndexMoment_pair_comm ℓ Y (g * h) f]
    unfold patternSum3 distinctIndexMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_three, Fin.prod_univ_two, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    rw [show Y (x 0) * Y (x 1) * Y (x 1) = Y (x 1) ^ 2 * Y (x 0) by ring,
      hpair, mul_comm (Y (x 1)) (Y (x 0))]
    ring
  have h000 : patternSum3 (r := 1) ![0, 0, 0] F = a * b * indexSum (f * g * h) := by
    unfold patternSum3
    have hi : ∀ x : Fin 1 → ι, Function.Injective x := fun _ _ _ _ => Subsingleton.elim _ _
    simp only [hi, Finset.filter_true]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp only [F, Fin.prod_univ_three, Function.comp_apply,
      Equiv.funUnique_symm_apply, uniqueElim_const,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp_rw [← pow_two, ← pow_succ, hcube]
    simp only [indexSum, Pi.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [quadraticFamilyMoment_eq_tuple_sum]
  change (∑ x, F x) = _
  rw [sum_fin_three_eq_pattern_sums, h012, h001, h010, h011, h000]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
