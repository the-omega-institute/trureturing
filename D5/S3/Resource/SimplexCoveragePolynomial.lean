/- GID: D5/S3/Resource/SimplexCoveragePolynomial
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoveragePolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reciprocal-factorial polynomial consumer keeps represented columns and contracts by actual spans. -/

import D5.S3.Resource.SimplexCoverageHessian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoveragePolynomial

open scoped BigOperators
open Matrix
attribute [local instance] Classical.propDecidable

variable {K V Index : Type*}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Fintype Index] [DecidableEq Index]

def representedSpan (columns : Index → V) (U : Submodule K V)
    (alpha : Index →₀ ℕ) : Submodule K V :=
  U ⊔ Submodule.span K (columns '' (alpha.support : Set Index))

def countVector (Index : Type*) [Fintype Index] (m : ℕ) :=
  {alpha : Index → Fin (m + 1) // ∑ i, (alpha i).val = m}

instance countVectorFintype (m : ℕ) : Fintype (countVector Index m) :=
  inferInstanceAs (Fintype {alpha : Index → Fin (m + 1) // ∑ i, (alpha i).val = m})

instance countVectorZeroUnique : Unique (countVector Index 0) where
  default := ⟨fun _ => 0, by simp⟩
  uniq beta := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hle : (beta.1 i).val ≤ ∑ j, (beta.1 j).val := by
      exact Finset.single_le_sum (f := fun j => (beta.1 j).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hi : (beta.1 i).val = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [beta.2] using hle)
    exact hi

def countVectorFinsupp {Index : Type*} [Fintype Index] {m : ℕ}
    (alpha : countVector Index m) : Index →₀ ℕ :=
  (Finsupp.equivFunOnFinite : (Index →₀ ℕ) ≃ (Index → ℕ)).symm
    (fun i => (alpha.1 i).val)

def reciprocalFactorial (alpha : Index →₀ ℕ) : ℚ :=
  ∏ i, ((Nat.factorial (alpha i) : ℚ)⁻¹)

def evaluateAt (x : Index → ℝ) (polynomial : MvPolynomial Index ℚ) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) x polynomial

def spanningPolynomial (columns : Index → V) (U : Submodule K V) (m : ℕ) :
    MvPolynomial Index ℚ :=
  ∑ alpha : countVector Index m,
    if representedSpan columns U (countVectorFinsupp alpha) = ⊤ then
      MvPolynomial.monomial (countVectorFinsupp alpha)
        (reciprocalFactorial (countVectorFinsupp alpha))
    else 0

def spanningHessian (columns : Index → V) (U : Submodule K V) (m : ℕ)
    (x : Index → ℝ) : Matrix Index Index ℝ :=
  fun row column =>
    evaluateAt x
      (MvPolynomial.pderiv row (MvPolynomial.pderiv column
        (spanningPolynomial columns U m)))

theorem spanningPolynomial_coeff (columns : Index → V) (U : Submodule K V)
    (m : ℕ) (alpha : Index →₀ ℕ) :
    MvPolynomial.coeff alpha (spanningPolynomial columns U m) =
      if (∑ i, alpha i) = m ∧ representedSpan columns U alpha = ⊤ then
        reciprocalFactorial alpha else 0 := by
  classical
  have injective : Function.Injective
      (countVectorFinsupp : countVector Index m → Index →₀ ℕ) := by
    intro beta gamma equality
    apply Subtype.ext
    funext i
    apply Fin.ext
    have coordinate := congrArg (fun exponent : Index →₀ ℕ => exponent i) equality
    simpa [countVectorFinsupp] using coordinate
  have total (beta : countVector Index m) :
      (∑ i, countVectorFinsupp beta i) = m := by
    simpa [countVectorFinsupp] using beta.2
  rw [spanningPolynomial, MvPolynomial.coeff_sum]
  by_cases degree : (∑ i, alpha i) = m
  · let beta : countVector Index m :=
      ⟨fun i => ⟨alpha i, by
        have bound : alpha i ≤ ∑ j, alpha j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega⟩, degree⟩
    have exponent : countVectorFinsupp beta = alpha := by
      ext i
      simp [countVectorFinsupp, beta]
    rw [Finset.sum_eq_single beta]
    · simp only [exponent, degree, true_and]
      split_ifs <;> simp
    · intro gamma _ distinct
      have different : countVectorFinsupp gamma ≠ alpha := by
        intro equality
        exact distinct (injective (equality.trans exponent.symm))
      split_ifs <;> simp [MvPolynomial.coeff_monomial, different]
    · simp
  · have absent (beta : countVector Index m) : countVectorFinsupp beta ≠ alpha := by
      intro equality
      exact degree (equality ▸ total beta)
    rw [if_neg (fun conditions => degree conditions.1)]
    apply Finset.sum_eq_zero
    intro beta _
    split_ifs <;> simp [MvPolynomial.coeff_monomial, absent beta]

theorem spanningPolynomial_pderiv (columns : Index → V) (U : Submodule K V)
    (m : ℕ) (i : Index) :
    MvPolynomial.pderiv i (spanningPolynomial columns U (m + 1)) =
      spanningPolynomial columns (U ⊔ Submodule.span K {columns i}) m := by
  classical
  apply MvPolynomial.ext
  intro alpha
  have span_contraction :
      representedSpan columns U (alpha + Finsupp.single i 1) =
        representedSpan columns (U ⊔ Submodule.span K {columns i}) alpha := by
    simp only [representedSpan, Finsupp.support_add_eq_union,
      Finsupp.support_single i (by decide : (1 : ℕ) ≠ 0),
      Finset.coe_union, Finset.coe_singleton, Set.image_union,
      Set.image_singleton, Submodule.span_union]
    ac_rfl
  have total_increment :
      (∑ j, (alpha + Finsupp.single i 1 : Index →₀ ℕ) j) =
        (∑ j, alpha j) + 1 := by
    simp [Finset.sum_add_distrib]
  have factorial_cancellation :
      reciprocalFactorial (alpha + Finsupp.single i 1) * (alpha i + 1 : ℚ) =
        reciprocalFactorial alpha := by
    have outside :
        (∏ j ∈ Finset.univ.erase i,
          ((Nat.factorial ((alpha + Finsupp.single i 1 : Index →₀ ℕ) j) : ℚ)⁻¹)) =
        ∏ j ∈ Finset.univ.erase i, ((Nat.factorial (alpha j) : ℚ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro j membership
      have different : j ≠ i := (Finset.mem_erase.mp membership).1
      simp [different]
    unfold reciprocalFactorial
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ
        (fun j => ((Nat.factorial (alpha j) : ℚ)⁻¹)) (Finset.mem_univ i)]
    rw [outside]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, _root_.mul_inv_rev]
    have successor_nonzero : (alpha i + 1 : ℚ) ≠ 0 := by positivity
    have factorial_nonzero : (Nat.factorial (alpha i) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (alpha i)
    field_simp
  rw [MvPolynomial.coeff_pderiv, spanningPolynomial_coeff,
    spanningPolynomial_coeff, span_contraction, total_increment]
  by_cases admissible :
      (∑ j, alpha j) = m ∧
        representedSpan columns (U ⊔ Submodule.span K {columns i}) alpha = ⊤
  · rw [if_pos admissible, if_pos ⟨by omega, admissible.2⟩]
    exact factorial_cancellation
  · rw [if_neg admissible, if_neg (by
      intro conditions
      exact admissible ⟨by omega, conditions.2⟩)]
    simp

theorem spanningHessian_degree_two_classification [FiniteDimensional K V]
    (columns : Index → V) (U : Submodule K V) (x : Index → ℝ) (i j : Index) :
    spanningHessian columns U 2 x i j =
      if Module.finrank K (V ⧸ U) = 0 then 1
      else if Module.finrank K (V ⧸ U) = 1 then
        if columns i ∈ U ∧ columns j ∈ U then 0 else 1
      else if Module.finrank K (V ⧸ U) = 2 then
        if columns i ∉ U ∧ columns j ∉ U ∧
          U ⊔ Submodule.span K {columns i} ≠ U ⊔ Submodule.span K {columns j}
        then 1 else 0
      else 0 := by
  classical
  let extension (index : Index) := U ⊔ Submodule.span K {columns index}
  have extension_eq (index : Index) (membership : columns index ∈ U) :
      extension index = U :=
    sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr membership)
  have extension_mem (index : Index) : columns index ∈ extension index :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have extension_rank (index : Index) :
      Module.finrank K (extension index) = Module.finrank K U +
        if columns index ∈ U then 0 else 1 := by
    split_ifs with membership
    · rw [extension_eq index membership, add_zero]
    · exact Submodule.finrank_sup_span_singleton membership
  have ambient_rank := U.finrank_quotient_add_finrank
  have pair_top : extension i ⊔ Submodule.span K {columns j} = ⊤ ↔
      (if columns i ∈ U then 0 else 1) +
        (if columns j ∈ extension i then 0 else 1) = Module.finrank K (V ⧸ U) := by
    rw [Submodule.eq_top_iff_finrank_eq]
    by_cases membership : columns j ∈ extension i
    · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr membership),
        extension_rank, if_pos membership]
      omega
    · rw [Submodule.finrank_sup_span_singleton membership, extension_rank,
        if_neg membership]
      omega
  have flats (nonloop_i : columns i ∉ U) (nonloop_j : columns j ∉ U) :
      columns j ∈ extension i ↔ extension i = extension j := by
    constructor
    · intro membership
      have containment : extension j ≤ extension i :=
        sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr membership)
      exact (Submodule.eq_of_le_of_finrank_eq containment (by
        rw [extension_rank, extension_rank, if_neg nonloop_j, if_neg nonloop_i])).symm
    · intro equality
      rw [equality]
      exact extension_mem j
  have indicator : spanningHessian columns U 2 x i j =
      if extension i ⊔ Submodule.span K {columns j} = ⊤ then 1 else 0 := by
    have zero_exponent :
        (Finsupp.equivFunOnFinite : (Index →₀ ℕ) ≃ (Index → ℕ)).symm
          (fun _ => 0) = 0 := by
      ext index
      simp
    have polynomial_zero (W : Submodule K V) :
        spanningPolynomial columns W 0 =
          if W = ⊤ then (1 : MvPolynomial Index ℚ) else 0 := by
      simp [spanningPolynomial, countVectorFinsupp, representedSpan,
        reciprocalFactorial, zero_exponent]
    unfold spanningHessian
    rw [show 2 = 1 + 1 from rfl, spanningPolynomial_pderiv,
      show 1 = 0 + 1 from rfl, spanningPolynomial_pderiv, polynomial_zero]
    have reordered : (U ⊔ Submodule.span K {columns j}) ⊔
        Submodule.span K {columns i} = extension i ⊔ Submodule.span K {columns j} := by
      dsimp [extension]
      ac_rfl
    rw [reordered]
    split_ifs <;> simp [evaluateAt]
  rw [indicator]
  by_cases rank_zero : Module.finrank K (V ⧸ U) = 0
  · have top : U = ⊤ := Submodule.eq_top_iff_finrank_eq.mpr (by omega)
    simp [rank_zero, extension, top]
  rw [if_neg rank_zero]
  by_cases loop_i : columns i ∈ U
  · have pair_equiv : extension i ⊔ Submodule.span K {columns j} = ⊤ ↔
        Module.finrank K (V ⧸ U) = 1 ∧ columns j ∉ U := by
      rw [pair_top, extension_eq i loop_i, if_pos loop_i]
      by_cases loop_j : columns j ∈ U <;> simp [loop_j] <;> omega
    simp only [pair_equiv]
    by_cases rank_one : Module.finrank K (V ⧸ U) = 1 <;>
      simp [rank_one, loop_i]
  · by_cases loop_j : columns j ∈ U
    · have inside : columns j ∈ extension i :=
        (show U ≤ extension i from le_sup_left) loop_j
      simp only [pair_top, if_neg loop_i, if_pos inside]
      by_cases rank_one : Module.finrank K (V ⧸ U) = 1 <;>
        simp [rank_one, loop_j, loop_i, eq_comm]
    · simp only [pair_top, if_neg loop_i, flats loop_i loop_j]
      change (if 1 + (if extension i = extension j then 0 else 1) =
        Module.finrank K (V ⧸ U) then 1 else 0) = _
      have flat_comparison :
          (U ⊔ Submodule.span K {columns i} = U ⊔ Submodule.span K {columns j}) ↔
            extension i = extension j := Iff.rfl
      by_cases equal_flats : extension i = extension j
      · simp [flat_comparison, equal_flats, loop_i, loop_j, eq_comm]
      · have not_one : Module.finrank K (V ⧸ U) ≠ 1 := by
          intro rank_one
          have top_i : extension i = ⊤ := Submodule.eq_top_iff_finrank_eq.mpr (by
            rw [extension_rank, if_neg loop_i]
            omega)
          have top_j : extension j = ⊤ := Submodule.eq_top_iff_finrank_eq.mpr (by
            rw [extension_rank, if_neg loop_j]
            omega)
          exact equal_flats (top_i.trans top_j.symm)
        simp [flat_comparison, equal_flats, loop_i, loop_j, eq_comm, not_one]

theorem spanningPolynomial_degree_two_reverse [FiniteDimensional K V]
    (columns : Index → V) (U : Submodule K V) (x y : Index → ℝ)
    (nonnegative : ∀ i, 0 ≤ x i) :
    2 * evaluateAt x (spanningPolynomial columns U 2) *
        (y ⬝ᵥ (spanningHessian columns U 2 x *ᵥ y)) ≤
      ((fun i => evaluateAt x (MvPolynomial.pderiv i
        (spanningPolynomial columns U 2))) ⬝ᵥ y) ^ 2 := by
  classical
  let hessian := spanningHessian columns U 2 x
  let quadratic (vector : Index → ℝ) := vector ⬝ᵥ (hessian *ᵥ vector)
  let extension (index : Index) := U ⊔ Submodule.span K {columns index}
  have symmetric_entries (i j : Index) : hessian i j = hessian j i := by
    simp [hessian, spanningHessian_degree_two_classification, and_comm,
      and_left_comm, ne_comm]
  have symmetric_pairing (left right : Index → ℝ) :
      left ⬝ᵥ (hessian *ᵥ right) = right ⬝ᵥ (hessian *ᵥ left) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symmetric_entries]
    ring
  have homogeneous (W : Submodule K V) (degree : ℕ) :
      (spanningPolynomial columns W degree).IsHomogeneous degree := by
    intro alpha coefficient
    change Finsupp.weight (fun _ : Index => (1 : ℕ)) alpha = degree
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
    by_contra wrong_degree
    rw [spanningPolynomial_coeff, if_neg (by
      intro conditions
      exact wrong_degree conditions.1)] at coefficient
    exact coefficient rfl
  have euler (W : Submodule K V) (degree : ℕ) :
      (∑ i, x i * evaluateAt x (MvPolynomial.pderiv i
        (spanningPolynomial columns W degree))) =
          (degree : ℝ) * evaluateAt x (spanningPolynomial columns W degree) := by
    have identity := congrArg (evaluateAt x) ((homogeneous W degree).sum_X_mul_pderiv)
    simpa [evaluateAt, MvPolynomial.eval₂_sum, nsmul_eq_mul] using identity
  have gradient (i : Index) :
      (hessian *ᵥ x) i = evaluateAt x
        (MvPolynomial.pderiv i (spanningPolynomial columns U 2)) := by
    rw [show 2 = 1 + 1 from rfl, spanningPolynomial_pderiv]
    have degree_one := euler (extension i) 1
    simp only [Nat.cast_one, one_mul] at degree_one
    rw [← degree_one]
    simp only [mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [symmetric_entries]
    change evaluateAt x (MvPolynomial.pderiv j (MvPolynomial.pderiv i
      (spanningPolynomial columns U (1 + 1)))) * x j = _
    rw [spanningPolynomial_pderiv]
    ring
  have quadratic_value : quadratic x =
      2 * evaluateAt x (spanningPolynomial columns U 2) := by
    dsimp [quadratic]
    simp only [dotProduct, gradient]
    simpa using euler U 2
  have entries_nonnegative (i j : Index) : 0 ≤ hessian i j := by
    dsimp [hessian]
    rw [spanningHessian_degree_two_classification]
    split_ifs <;> norm_num
  have quadratic_nonnegative : 0 ≤ quadratic x := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (nonnegative i)
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (entries_nonnegative i j) (nonnegative j)
  have one_direction : ∃ weight : Index → ℝ, ∀ vector : Index → ℝ,
      quadratic vector ≤ (weight ⬝ᵥ vector) ^ 2 := by
    by_cases rank_zero : Module.finrank K (V ⧸ U) = 0
    · refine ⟨fun _ => 1, fun vector => ?_⟩
      have entries (i j : Index) : hessian i j = 1 := by
        simp [hessian, spanningHessian_degree_two_classification, rank_zero]
      simp [quadratic, dotProduct, mulVec, entries, ← Finset.sum_mul, pow_two]
    by_cases rank_one : Module.finrank K (V ⧸ U) = 1
    · refine ⟨fun _ => 1, fun vector => ?_⟩
      let loop_part (i : Index) : ℝ := if columns i ∈ U then vector i else 0
      have entries (i j : Index) :
          vector i * (hessian i j * vector j) =
            vector i * vector j - loop_part i * loop_part j := by
        by_cases loop_i : columns i ∈ U <;> by_cases loop_j : columns j ∈ U <;>
          simp [hessian, spanningHessian_degree_two_classification,
            rank_one, loop_part, loop_i, loop_j]
      have form : quadratic vector =
          (∑ i, vector i) ^ 2 - (∑ i, loop_part i) ^ 2 := by
        simp only [quadratic, dotProduct, mulVec, Finset.mul_sum, entries,
          Finset.sum_sub_distrib]
        simp [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
      rw [form]
      simp only [dotProduct, one_mul]
      nlinarith [sq_nonneg (∑ i, loop_part i)]
    by_cases rank_two : Module.finrank K (V ⧸ U) = 2
    · refine ⟨fun i => if columns i ∈ U then 0 else 1, fun vector => ?_⟩
      let active_part (i : Index) : ℝ := if columns i ∈ U then 0 else vector i
      let classes : Finset (Submodule K V) := Finset.univ.image extension
      let block (W : Submodule K V) : ℝ :=
        ∑ i, if extension i = W then active_part i else 0
      have entries (i j : Index) :
          vector i * (hessian i j * vector j) =
            active_part i * active_part j -
              if extension i = extension j then active_part i * active_part j else 0 := by
        by_cases loop_i : columns i ∈ U <;> by_cases loop_j : columns j ∈ U <;>
          by_cases equal_flats : extension i = extension j <;>
          simp [hessian, spanningHessian_degree_two_classification,
            rank_two, active_part, loop_i, loop_j,
            show (U ⊔ Submodule.span K {columns i} =
              U ⊔ Submodule.span K {columns j}) ↔ extension i = extension j from Iff.rfl,
            equal_flats]
      have same_class (i : Index) :
          (∑ j, if extension i = extension j then active_part i * active_part j else 0) =
            active_part i * block (extension i) := by
        simp [block, Finset.mul_sum, mul_ite, eq_comm]
      have grouped :
          (∑ i, active_part i * block (extension i)) = ∑ W ∈ classes, (block W) ^ 2 := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (show ∀ i ∈ (Finset.univ : Finset Index), extension i ∈ classes from
            fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
        apply Finset.sum_congr rfl
        intro W _
        simp only [Finset.sum_filter]
        have terms (i : Index) :
            (if extension i = W then active_part i * block (extension i) else 0) =
              (if extension i = W then active_part i else 0) * block W := by
          split_ifs with equality
          · rw [equality]
          · simp
        simp_rw [terms]
        rw [← Finset.sum_mul]
        simp [block, pow_two]
      have form : quadratic vector =
          (∑ i, active_part i) ^ 2 - ∑ W ∈ classes, (block W) ^ 2 := by
        simp only [quadratic, dotProduct, mulVec, Finset.mul_sum, entries,
          Finset.sum_sub_distrib, same_class, grouped]
        simp [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
      have weight_sum :
          (fun i => if columns i ∈ U then (0 : ℝ) else 1) ⬝ᵥ vector =
            ∑ i, active_part i := by
        simp [dotProduct, active_part, ite_mul]
      rw [form, weight_sum]
      have squares : 0 ≤ ∑ W ∈ classes, (block W) ^ 2 :=
        Finset.sum_nonneg (fun W _ => sq_nonneg (block W))
      linarith
    · refine ⟨fun _ => 0, fun vector => ?_⟩
      have entries (i j : Index) : hessian i j = 0 := by
        simp [hessian, spanningHessian_degree_two_classification, rank_zero, rank_one, rank_two]
      simp [quadratic, dotProduct, mulVec, entries]
  obtain ⟨weight, hyperplane_bound⟩ := one_direction
  have expansion (left right : Index → ℝ) (scalar : ℝ) :
      quadratic (left - scalar • right) = quadratic left -
        2 * scalar * (left ⬝ᵥ (hessian *ᵥ right)) + scalar ^ 2 * quadratic right := by
    simp only [quadratic, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [symmetric_pairing right left]
    ring
  have positive_case (positive : 0 < quadratic x) :
      quadratic x * quadratic y ≤ (x ⬝ᵥ (hessian *ᵥ y)) ^ 2 := by
    have weight_nonzero : weight ⬝ᵥ x ≠ 0 := by
      intro equality
      have bound := hyperplane_bound x
      rw [equality] at bound
      norm_num at bound
      linarith
    have transverse (vector : Index → ℝ)
        (perpendicular : x ⬝ᵥ (hessian *ᵥ vector) = 0) : quadratic vector ≤ 0 := by
      by_contra not_nonpositive
      have vector_positive : 0 < quadratic vector := lt_of_not_ge not_nonpositive
      let scalar : ℝ := (weight ⬝ᵥ vector) / (weight ⬝ᵥ x)
      have weight_zero : weight ⬝ᵥ (vector - scalar • x) = 0 := by
        simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        dsimp [scalar]
        field_simp
        ring
      have bound := hyperplane_bound (vector - scalar • x)
      rw [weight_zero, expansion, symmetric_pairing vector x, perpendicular] at bound
      have square_term : 0 ≤ scalar ^ 2 * quadratic x :=
        mul_nonneg (sq_nonneg scalar) positive.le
      nlinarith
    let scalar : ℝ := (x ⬝ᵥ (hessian *ᵥ y)) / quadratic x
    have perpendicular : x ⬝ᵥ (hessian *ᵥ (y - scalar • x)) = 0 := by
      simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      change x ⬝ᵥ (hessian *ᵥ y) - scalar * quadratic x = 0
      dsimp [scalar]
      field_simp
      ring
    have bound := transverse (y - scalar • x) perpendicular
    rw [expansion, symmetric_pairing y x] at bound
    have scalar_identity : scalar * quadratic x = x ⬝ᵥ (hessian *ᵥ y) := by
      dsimp [scalar]
      exact div_mul_cancel₀ _ positive.ne'
    have scaled := mul_le_mul_of_nonneg_left bound positive.le
    nlinarith [sq_nonneg (x ⬝ᵥ (hessian *ᵥ y) - scalar * quadratic x)]
  have gradient_pairing :
      ((fun i => evaluateAt x (MvPolynomial.pderiv i
        (spanningPolynomial columns U 2))) ⬝ᵥ y) = x ⬝ᵥ (hessian *ᵥ y) := by
    simp_rw [← gradient]
    rw [dotProduct_comm, symmetric_pairing]
  rw [gradient_pairing, ← quadratic_value]
  change quadratic x * quadratic y ≤ _
  rcases eq_or_lt_of_le quadratic_nonnegative with zero | positive
  · rw [← zero, zero_mul]
    exact sq_nonneg _
  · exact positive_case positive

theorem spanningPolynomial_positive_iff [FiniteDimensional K V] [Nonempty Index]
    (columns : Index → V) (U : Submodule K V) (degree : ℕ) (x : Index → ℝ)
    (positive : ∀ i, 0 < x i)
    (spanning : U ⊔ Submodule.span K (Set.range columns) = ⊤) :
    0 ≤ evaluateAt x (spanningPolynomial columns U degree) ∧
      (0 < evaluateAt x (spanningPolynomial columns U degree) ↔
        Module.finrank K (V ⧸ U) ≤ degree) := by
  classical
  have nonnegative (W : Submodule K V) (m : ℕ) :
      0 ≤ evaluateAt x (spanningPolynomial columns W m) := by
    simp only [spanningPolynomial, evaluateAt, MvPolynomial.eval₂_sum]
    apply Finset.sum_nonneg
    intro alpha _
    split_ifs
    · rw [MvPolynomial.eval₂_monomial]
      apply mul_nonneg
      · have coefficient_nonnegative : 0 ≤ reciprocalFactorial (countVectorFinsupp alpha) :=
          Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
        change 0 ≤ (reciprocalFactorial (countVectorFinsupp alpha) : ℝ)
        exact Rat.cast_nonneg.mpr coefficient_nonnegative
      · apply Finset.prod_nonneg
        intro i _
        exact pow_nonneg (positive i).le _
    · simp
  have homogeneous (W : Submodule K V) (m : ℕ) :
      (spanningPolynomial columns W m).IsHomogeneous m := by
    intro alpha coefficient
    change Finsupp.weight (fun _ : Index => (1 : ℕ)) alpha = m
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
    by_contra wrong_degree
    rw [spanningPolynomial_coeff, if_neg (by
      intro conditions
      exact wrong_degree conditions.1)] at coefficient
    exact coefficient rfl
  refine ⟨nonnegative U degree, ?_⟩
  induction degree generalizing U with
  | zero =>
    have zero_exponent :
        (Finsupp.equivFunOnFinite : (Index →₀ ℕ) ≃ (Index → ℕ)).symm
          (fun _ => 0) = 0 := by
      ext index
      simp
    have polynomial_zero : spanningPolynomial columns U 0 =
        if U = ⊤ then (1 : MvPolynomial Index ℚ) else 0 := by
      simp [spanningPolynomial, countVectorFinsupp, representedSpan,
        reciprocalFactorial, zero_exponent]
    have quotient_zero : Module.finrank K (V ⧸ U) = 0 ↔ U = ⊤ := by
      rw [Submodule.eq_top_iff_finrank_eq]
      have ambient_rank := U.finrank_quotient_add_finrank
      omega
    rw [polynomial_zero]
    by_cases top : U = ⊤ <;>
      simp [evaluateAt, quotient_zero, top]
  | succ degree induction =>
    let extension (i : Index) := U ⊔ Submodule.span K {columns i}
    have extension_spanning (i : Index) :
        extension i ⊔ Submodule.span K (Set.range columns) = ⊤ := by
      apply top_unique
      rw [← spanning]
      exact sup_le_sup le_sup_left le_rfl
    have extension_rank (i : Index) :
        Module.finrank K (V ⧸ extension i) + (if columns i ∈ U then 0 else 1) =
          Module.finrank K (V ⧸ U) := by
      have ambient_rank := U.finrank_quotient_add_finrank
      have new_rank := (extension i).finrank_quotient_add_finrank
      by_cases membership : columns i ∈ U
      · have equality : extension i = U :=
          sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr membership)
        rw [equality, if_pos membership, add_zero]
      · have increment := Submodule.finrank_sup_span_singleton membership
        change Module.finrank K (extension i) = Module.finrank K U + 1 at increment
        rw [if_neg membership]
        omega
    have euler : (∑ i, x i * evaluateAt x
        (spanningPolynomial columns (extension i) degree)) =
          (degree + 1 : ℝ) * evaluateAt x (spanningPolynomial columns U (degree + 1)) := by
      have identity := congrArg (evaluateAt x)
        ((homogeneous U (degree + 1)).sum_X_mul_pderiv)
      simp_rw [spanningPolynomial_pderiv] at identity
      simpa [evaluateAt, MvPolynomial.eval₂_sum, nsmul_eq_mul, extension] using identity
    have terms_nonnegative (i : Index) (_ : i ∈ (Finset.univ : Finset Index)) :
        0 ≤ x i * evaluateAt x (spanningPolynomial columns (extension i) degree) :=
      mul_nonneg (positive i).le (nonnegative (extension i) degree)
    constructor
    · intro evaluation_positive
      have sum_positive : 0 < ∑ i, x i * evaluateAt x
          (spanningPolynomial columns (extension i) degree) := by
        rw [euler]
        exact mul_pos (by positivity) evaluation_positive
      obtain ⟨i, _, term_positive⟩ :=
        (Finset.sum_pos_iff_of_nonneg terms_nonnegative).mp sum_positive
      have derivative_positive := (mul_pos_iff_of_pos_left (positive i)).mp term_positive
      have rank_bound :=
        (induction (extension i) (extension_spanning i)).mp derivative_positive
      have rank_identity := extension_rank i
      split_ifs at rank_identity <;> omega
    · intro rank_bound
      have choice : ∃ i, Module.finrank K (V ⧸ extension i) ≤ degree := by
        by_cases top : U = ⊤
        · refine ⟨Classical.arbitrary Index, ?_⟩
          have quotient_zero : Module.finrank K (V ⧸ U) = 0 := by
            have ambient_rank := U.finrank_quotient_add_finrank
            have top_rank := (Submodule.eq_top_iff_finrank_eq (W := U)).mp top
            omega
          have rank_identity := extension_rank (Classical.arbitrary Index)
          split_ifs at rank_identity <;> omega
        · have outside : ∃ i, columns i ∉ U := by
            by_contra absent
            have inside : ∀ i, columns i ∈ U := by simpa using absent
            have containment : Submodule.span K (Set.range columns) ≤ U := by
              rw [Submodule.span_le]
              rintro _ ⟨i, rfl⟩
              exact inside i
            exact top (by simpa [sup_eq_left.mpr containment] using spanning)
          obtain ⟨i, outside⟩ := outside
          refine ⟨i, ?_⟩
          have rank_identity := extension_rank i
          rw [if_neg outside] at rank_identity
          omega
      obtain ⟨i, contracted_rank⟩ := choice
      have derivative_positive :=
        (induction (extension i) (extension_spanning i)).mpr contracted_rank
      have sum_positive : 0 < ∑ j, x j * evaluateAt x
          (spanningPolynomial columns (extension j) degree) :=
        (Finset.sum_pos_iff_of_nonneg terms_nonnegative).mpr
          ⟨i, Finset.mem_univ i, mul_pos (positive i) derivative_positive⟩
      rw [euler] at sum_positive
      exact (mul_pos_iff_of_pos_left (by positivity : 0 < (degree + 1 : ℝ))).mp sum_positive

theorem spanningHessian_active_connected [FiniteDimensional K V] [Nonempty Index]
    (columns : Index → V) (U : Submodule K V) (m : ℕ) (x : Index → ℝ)
    (positive : ∀ i, 0 < x i)
    (spanning : U ⊔ Submodule.span K (Set.range columns) = ⊤)
    (support : Finset {i : Index // 0 < evaluateAt x
      (MvPolynomial.pderiv i (spanningPolynomial columns U (m + 2)))})
    (nonempty : support.Nonempty) (proper : support ≠ Finset.univ) :
    ∃ i ∈ support, ∃ j ∉ support, 0 < spanningHessian columns U (m + 2) x i.1 j.1 := by
  classical
  let extension (i : Index) := U ⊔ Submodule.span K {columns i}
  let hessian := spanningHessian columns U (m + 2) x
  have enlarged_spanning (W : Submodule K V) (containment : U ≤ W) :
      W ⊔ Submodule.span K (Set.range columns) = ⊤ := by
    apply top_unique
    rw [← spanning]
    exact sup_le_sup containment le_rfl
  have rank_step (W : Submodule K V) (i : Index) :
      Module.finrank K (V ⧸ (W ⊔ Submodule.span K {columns i})) +
        (if columns i ∈ W then 0 else 1) = Module.finrank K (V ⧸ W) := by
    have ambient_rank := W.finrank_quotient_add_finrank
    have new_rank := (W ⊔ Submodule.span K {columns i}).finrank_quotient_add_finrank
    by_cases membership : columns i ∈ W
    · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr membership),
        if_pos membership, add_zero]
    · have increment := Submodule.finrank_sup_span_singleton membership
      rw [if_neg membership]
      omega
  have extension_eq (i : Index) (membership : columns i ∈ U) : extension i = U :=
    sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr membership)
  have activity (i : Index) :
      (0 < evaluateAt x (MvPolynomial.pderiv i
        (spanningPolynomial columns U (m + 2)))) ↔
          Module.finrank K (V ⧸ extension i) ≤ m + 1 := by
    rw [show m + 2 = (m + 1) + 1 from by omega, spanningPolynomial_pderiv]
    exact (spanningPolynomial_positive_iff columns (extension i) (m + 1) x positive
      (enlarged_spanning (extension i) le_sup_left)).2
  have edge (i j : Index) : 0 < hessian i j ↔
      Module.finrank K (V ⧸ (extension i ⊔ Submodule.span K {columns j})) ≤ m := by
    dsimp [hessian, spanningHessian]
    rw [show m + 2 = (m + 1) + 1 from by omega, spanningPolynomial_pderiv,
      spanningPolynomial_pderiv]
    have reordered : (U ⊔ Submodule.span K {columns j}) ⊔
        Submodule.span K {columns i} = extension i ⊔ Submodule.span K {columns j} := by
      dsimp [extension]
      ac_rfl
    rw [reordered]
    exact (spanningPolynomial_positive_iff columns
      (extension i ⊔ Submodule.span K {columns j}) m x positive
        (enlarged_spanning _ (le_sup_left.trans le_sup_left))).2
  have edge_symmetric (i j : Index) : 0 < hessian i j ↔ 0 < hessian j i := by
    rw [edge, edge]
    have reordered : extension i ⊔ Submodule.span K {columns j} =
        extension j ⊔ Submodule.span K {columns i} := by
      dsimp [extension]
      ac_rfl
    rw [reordered]
  have active_of_edge (i j : Index) (adjacent : 0 < hessian i j) :
      0 < evaluateAt x (MvPolynomial.pderiv i
        (spanningPolynomial columns U (m + 2))) := by
    apply (activity i).mpr
    have pair_bound := (edge i j).mp adjacent
    have pair_rank := rank_step (extension i) j
    split_ifs at pair_rank <;> omega
  have outside (W : Submodule K V)
      (full_span : W ⊔ Submodule.span K (Set.range columns) = ⊤)
      (positive_rank : 0 < Module.finrank K (V ⧸ W)) : ∃ i, columns i ∉ W := by
    by_contra absent
    have inside : ∀ i, columns i ∈ W := by simpa using absent
    have containment : Submodule.span K (Set.range columns) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact inside i
    have top : W = ⊤ := by simpa [sup_eq_left.mpr containment] using full_span
    have ambient_rank := W.finrank_quotient_add_finrank
    have top_rank := (Submodule.eq_top_iff_finrank_eq (W := W)).mp top
    omega
  have completion (i j : Index)
      (active_i : 0 < evaluateAt x (MvPolynomial.pderiv i
        (spanningPolynomial columns U (m + 2))))
      (active_j : 0 < evaluateAt x (MvPolynomial.pderiv j
        (spanningPolynomial columns U (m + 2)))) :
      0 < hessian i j ∨ ∃ k,
        0 < evaluateAt x (MvPolynomial.pderiv k (spanningPolynomial columns U (m + 2))) ∧
          0 < hessian i k ∧ 0 < hessian j k := by
    have bound_i := (activity i).mp active_i
    have bound_j := (activity j).mp active_j
    have step_i := rank_step U i
    have step_j := rank_step U j
    change Module.finrank K (V ⧸ extension i) + (if columns i ∈ U then 0 else 1) = _ at step_i
    change Module.finrank K (V ⧸ extension j) + (if columns j ∈ U then 0 else 1) = _ at step_j
    by_cases low_rank : Module.finrank K (V ⧸ U) ≤ m
    · left
      apply (edge i j).mpr
      have pair_rank := rank_step (extension i) j
      split_ifs at step_i pair_rank <;> omega
    have rank_cases : Module.finrank K (V ⧸ U) = m + 1 ∨
        Module.finrank K (V ⧸ U) = m + 2 := by
      split_ifs at step_i <;> omega
    rcases rank_cases with rank_one | rank_two
    · by_cases loop_i : columns i ∈ U
      · by_cases loop_j : columns j ∈ U
        · obtain ⟨k, nonloop_k⟩ := outside U spanning (by omega)
          have step_k := rank_step U k
          rw [if_neg nonloop_k] at step_k
          have adjacent_i : 0 < hessian i k := by
            apply (edge i k).mpr
            rw [extension_eq i loop_i]
            omega
          have adjacent_j : 0 < hessian j k := by
            apply (edge j k).mpr
            rw [extension_eq j loop_j]
            omega
          exact Or.inr ⟨k, active_of_edge k i ((edge_symmetric i k).mp adjacent_i),
            adjacent_i, adjacent_j⟩
        · left
          apply (edge_symmetric j i).mp
          apply (edge j i).mpr
          rw [if_neg loop_j] at step_j
          have pair_rank := rank_step (extension j) i
          split_ifs at pair_rank <;> omega
      · left
        apply (edge i j).mpr
        rw [if_neg loop_i] at step_i
        have pair_rank := rank_step (extension i) j
        split_ifs at pair_rank <;> omega
    · have nonloop_i : columns i ∉ U := by
        intro loop_i
        rw [if_pos loop_i] at step_i
        omega
      have nonloop_j : columns j ∉ U := by
        intro loop_j
        rw [if_pos loop_j] at step_j
        omega
      rw [if_neg nonloop_i] at step_i
      rw [if_neg nonloop_j] at step_j
      by_cases inside_j : columns j ∈ extension i
      · have containment : extension j ≤ extension i :=
          sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).mpr inside_j)
        have equal_flats : extension i = extension j :=
          (Submodule.eq_of_le_of_finrank_eq containment (by
            have rank_i := Submodule.finrank_sup_span_singleton nonloop_i
            have rank_j := Submodule.finrank_sup_span_singleton nonloop_j
            exact rank_j.trans rank_i.symm)).symm
        obtain ⟨k, outside_i⟩ := outside (extension i)
          (enlarged_spanning (extension i) le_sup_left) (by omega)
        have adjacent_i : 0 < hessian i k := by
          apply (edge i k).mpr
          have pair_rank := rank_step (extension i) k
          rw [if_neg outside_i] at pair_rank
          omega
        have adjacent_j : 0 < hessian j k := by
          apply (edge j k).mpr
          have outside_j : columns k ∉ extension j := by rwa [← equal_flats]
          have pair_rank := rank_step (extension j) k
          rw [if_neg outside_j] at pair_rank
          omega
        exact Or.inr ⟨k, active_of_edge k i ((edge_symmetric i k).mp adjacent_i),
          adjacent_i, adjacent_j⟩
      · left
        apply (edge i j).mpr
        have pair_rank := rank_step (extension i) j
        rw [if_neg inside_j] at pair_rank
        omega
  obtain ⟨i, membership_i⟩ := nonempty
  have missing : ∃ j, j ∉ support := by
    by_contra absent
    apply proper
    apply Finset.eq_univ_iff_forall.mpr
    simpa using absent
  obtain ⟨j, outside_j⟩ := missing
  rcases completion i.1 j.1 i.2 j.2 with adjacent | ⟨k, active_k, adjacent_i, adjacent_j⟩
  · exact ⟨i, membership_i, j, outside_j, adjacent⟩
  · let active_index : {i : Index // 0 < evaluateAt x
        (MvPolynomial.pderiv i (spanningPolynomial columns U (m + 2)))} := ⟨k, active_k⟩
    by_cases membership_k : active_index ∈ support
    · exact ⟨active_index, membership_k, j, outside_j, (edge_symmetric j k).mp adjacent_j⟩
    · exact ⟨i, membership_i, active_index, membership_k, adjacent_i⟩

theorem spanningPolynomial_eq_zero_of_rank_or_span [FiniteDimensional K V]
    (columns : Index → V) (U : Submodule K V) (degree : ℕ)
    (obstruction : degree < Module.finrank K (V ⧸ U) ∨
      U ⊔ Submodule.span K (Set.range columns) ≠ ⊤) :
    spanningPolynomial columns U degree = 0 := by
  classical
  rcases obstruction with rank_obstruction | span_obstruction
  · induction degree generalizing U with
    | zero =>
      have zero_exponent :
          (Finsupp.equivFunOnFinite : (Index →₀ ℕ) ≃ (Index → ℕ)).symm
            (fun _ => 0) = 0 := by
        ext index
        simp
      have polynomial_zero : spanningPolynomial columns U 0 =
          if U = ⊤ then (1 : MvPolynomial Index ℚ) else 0 := by
        simp [spanningPolynomial, countVectorFinsupp, representedSpan,
          reciprocalFactorial, zero_exponent]
      have not_top : U ≠ ⊤ := by
        intro top
        have ambient_rank := U.finrank_quotient_add_finrank
        have top_rank := Submodule.eq_top_iff_finrank_eq.mp top
        omega
      simp [polynomial_zero, not_top]
    | succ degree induction =>
      have contractions (i : Index) :
          spanningPolynomial columns (U ⊔ Submodule.span K {columns i}) degree = 0 := by
        apply induction
        have ambient_rank := U.finrank_quotient_add_finrank
        have new_rank := (U ⊔ Submodule.span K {columns i}).finrank_quotient_add_finrank
        by_cases membership : columns i ∈ U
        · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr membership)]
          omega
        · have increment := Submodule.finrank_sup_span_singleton membership
          omega
      have homogeneous : (spanningPolynomial columns U (degree + 1)).IsHomogeneous
          (degree + 1) := by
        intro alpha coefficient
        change Finsupp.weight (fun _ : Index => (1 : ℕ)) alpha = degree + 1
        rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
        by_contra wrong_degree
        rw [spanningPolynomial_coeff, if_neg (by
          intro conditions
          exact wrong_degree conditions.1)] at coefficient
        exact coefficient rfl
      have identity := homogeneous.sum_X_mul_pderiv
      simp only [spanningPolynomial_pderiv, contractions, mul_zero,
        Finset.sum_const_zero] at identity
      have scalar_zero : ((degree + 1 : ℕ) : ℚ) •
          spanningPolynomial columns U (degree + 1) = 0 := by
        simpa only [Nat.cast_smul_eq_nsmul] using identity.symm
      exact (smul_eq_zero.mp scalar_zero).resolve_left (by positivity)
  · apply MvPolynomial.ext
    intro alpha
    have containment : representedSpan columns U alpha ≤
        U ⊔ Submodule.span K (Set.range columns) := by
      apply sup_le_sup le_rfl
      apply Submodule.span_mono
      rintro _ ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    rw [spanningPolynomial_coeff, if_neg (by
      intro conditions
      exact span_obstruction (top_unique (conditions.2 ▸ containment)))]
    simp

end D5.S3.Resource.SimplexCoveragePolynomial

#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial_coeff
#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial_pderiv
#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningHessian_degree_two_classification
#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial_degree_two_reverse
#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial_positive_iff
#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningHessian_active_connected
#print axioms D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial_eq_zero_of_rank_or_span
