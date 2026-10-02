/- GID: D5/S3/Resource/SimplexCoverageWords
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoverageWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Filtered physical words normalize the actual spanning polynomial at every horizon. -/

import D5.S3.Resource.SimplexCoveragePolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoverageWords

open scoped BigOperators
open D5.S3.Resource.SimplexCoveragePolynomial

variable {K V Index : Type*}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Fintype Index]

open Classical in
def wordPolynomial (columns : Index → V) (U : Submodule K V) (time : ℕ) :
    MvPolynomial Index ℚ :=
  ∑ word : Fin time → Index,
    if U ⊔ Submodule.span K (Set.range (fun position => columns (word position))) = ⊤
    then ∏ position, MvPolynomial.X (word position) else 0

theorem wordPolynomial_eq_factorial_smul (columns : Index → V)
    [DecidableEq Index] (U : Submodule K V) (time : ℕ) :
    wordPolynomial columns U time = time.factorial • spanningPolynomial columns U time := by
  classical
  have wordPolynomial_succ_local :
      ∀ (U : Submodule K V) (time : ℕ),
        wordPolynomial columns U (time + 1) =
          ∑ index, MvPolynomial.X index *
            wordPolynomial columns (U ⊔ Submodule.span K {columns index}) time := by
    intro U time
    have span_cons (index : Index) (word : Fin time → Index) :
        U ⊔ Submodule.span K
          (Set.range (fun position : Fin (time + 1) =>
            columns ((Fin.cons index word : Fin (time + 1) → Index) position))) =
        (U ⊔ Submodule.span K {columns index}) ⊔
          Submodule.span K (Set.range (fun position => columns (word position))) := by
      have range_cons :
          Set.range (fun position : Fin (time + 1) =>
            columns ((Fin.cons index word : Fin (time + 1) → Index) position)) =
            insert (columns index) (Set.range (fun position => columns (word position))) := by
        rw [← Fin.range_cons (columns index) (fun position => columns (word position))]
        congr 1
        funext position
        refine Fin.cases ?_ (fun tail => ?_) position <;> simp
      rw [range_cons, Submodule.span_insert, sup_assoc]
    unfold wordPolynomial
    rw [← (Fin.consEquiv (fun _ : Fin (time + 1) => Index)).sum_comp
      (fun word : Fin (time + 1) → Index =>
        if U ⊔ Submodule.span K (Set.range (fun position => columns (word position))) = ⊤
        then ∏ position, MvPolynomial.X (word position) else 0),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro index _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    change (if U ⊔ Submodule.span K
        (Set.range (fun position : Fin (time + 1) =>
          columns ((Fin.cons index word : Fin (time + 1) → Index) position))) = ⊤
      then ∏ position, MvPolynomial.X (R := ℚ)
        ((Fin.cons index word : Fin (time + 1) → Index) position) else 0) = _
    rw [span_cons]
    split_ifs <;> simp [Fin.prod_univ_succ]
  induction time generalizing U with
  | zero =>
    have zero_exponent :
        (Finsupp.equivFunOnFinite : (Index →₀ ℕ) ≃ (Index → ℕ)).symm
          (fun _ => 0) = 0 := by
      ext index
      simp
    simp [wordPolynomial, spanningPolynomial, countVectorFinsupp, representedSpan,
      reciprocalFactorial, zero_exponent]
  | succ time induction =>
    have homogeneous : (spanningPolynomial columns U (time + 1)).IsHomogeneous
        (time + 1) := by
      intro alpha coefficient
      change Finsupp.weight (fun _ : Index => (1 : ℕ)) alpha = time + 1
      rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
      by_contra wrong_degree
      rw [spanningPolynomial_coeff, if_neg (by
        intro conditions
        exact wrong_degree conditions.1)] at coefficient
      exact coefficient rfl
    have euler := homogeneous.sum_X_mul_pderiv
    simp_rw [spanningPolynomial_pderiv] at euler
    rw [wordPolynomial_succ_local U time]
    simp_rw [induction, mul_smul_comm]
    rw [← Finset.smul_sum, euler, smul_smul, Nat.factorial_succ]
    congr 1
    exact Nat.mul_comm _ _

end D5.S3.Resource.SimplexCoverageWords
