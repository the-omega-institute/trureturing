/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pair-dependent locality clears arbitrary-input words with finite total-exponent slices. -/

/-
proof_shape: weighted_clearing_kills: bind-only
proof_shape: clear_adjacent_fields_lt: bind-only
proof_shape: clear_adjacent_fields: bind-only
proof_shape: clear_permutation_fields_context: content
proof_shape: difference_lower_bound: content
proof_shape: difference_power_lower_bound: bind-only
proof_shape: weighted_clearing_lower_bound: content
proof_shape: finite_laurent_simplex: content
proof_shape: common_cleared_fields: content
admission_basis: escape-witness
escape_witness: Pair-specific operator locality yields contextual permutation
invariance on arbitrary actual input vectors. Moving each label to the rightmost
position imports its pointwise truncation bound; finite clearing preserves all
these bounds, and a signed finite-simplex argument bounds every fixed-total slice.
Neither a common cleared array nor its support is a hypothesis. No vacuum,
creation, grading, uniform locality order or positivity of the total is assumed.
The bind-only helpers are consumed by adjacent exchange, permutation invariance
and preservation of the coordinate bounds in common_cleared_fields.
-/

import D5.S3.VertexAlgebra.SupportedWordRationalCollision

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.WeightedLocalCorrelator

open scoped BigOperators VertexOperator
open D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open D5.S3.VertexAlgebra.FieldNormalProductLocality (commutator deltaEnd)
open D5.S3.VertexAlgebra.SupportedFieldWords.ActualFieldWordAdapter (word_append_adapter)

noncomputable section

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Pair-dependent clearing orders; labels keep their original orientation. -/
def weightedClearingPolynomial (orders : Fin N × Fin N → ℕ) : LaurentPolynomial N :=
  ∏ p ∈ labelledPairs N, pairPolynomial p.1 p.2 ^ orders p

private theorem weighted_clearing_kills (orders : Fin N × Fin N → ℕ)
    (i j : Fin N) (hij : i < j) (F : Distribution N V)
    (hF : (difference i j ^ orders (i, j)) F = 0) :
    polynomialAction (weightedClearingPolynomial orders) F = 0 := by
  have hm : (i, j) ∈ labelledPairs N := by simp [labelledPairs, hij]
  have factor := Finset.prod_erase_mul (labelledPairs N)
    (fun p => pairPolynomial p.1 p.2 ^ orders p) hm
  change polynomialAction (∏ p ∈ labelledPairs N, pairPolynomial p.1 p.2 ^ orders p) F = 0
  rw [← factor, map_mul, map_pow, action_pair, Module.End.mul_apply, hF, map_zero]

private theorem clear_adjacent_fields_lt (A : Fin N → VertexOperator ℂ V)
    (vector : V) (P : Module.End ℂ V) (orders : Fin N × Fin N → ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ orders (i, j)) (commutator (A i) (A j)) = 0)
    (pre post : List (Fin N)) (i j : Fin N) (hij : i < j)
    (hip : i ∉ pre) (hjp : j ∉ pre) (his : i ∉ post) (hjs : j ∉ post) :
    polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P (pre ++ i :: j :: post)) =
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P (pre ++ j :: i :: post)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← liftPair_commutator]
  apply weighted_clearing_kills orders i j hij
  rw [intertwine_power deltaEnd (difference i j) (liftPair A vector P pre post i j)
    (liftPair_difference A vector P pre post i j (ne_of_lt hij) hip hjp his hjs),
    locality i j hij, map_zero]

private theorem clear_adjacent_fields (A : Fin N → VertexOperator ℂ V)
    (vector : V) (P : Module.End ℂ V) (orders : Fin N × Fin N → ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ orders (i, j)) (commutator (A i) (A j)) = 0)
    (pre post : List (Fin N)) (i j : Fin N)
    (hn : (pre ++ i :: j :: post).Nodup) :
    polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P (pre ++ i :: j :: post)) =
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P (pre ++ j :: i :: post)) := by
  have hs := (List.nodup_append.mp hn).2.1
  have hcross := (List.nodup_append.mp hn).2.2
  have hip : i ∉ pre := by intro hi; exact hcross i hi i (by simp) rfl
  have hjp : j ∉ pre := by intro hj; exact hcross j hj j (by simp) rfl
  have his : i ∉ post := fun hi => (List.nodup_cons.mp hs).1 (by simp [hi])
  have hjs : j ∉ post := (List.nodup_cons.mp (List.nodup_cons.mp hs).2).1
  have hne : i ≠ j := by intro he; exact (List.nodup_cons.mp hs).1 (by simp [he])
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact clear_adjacent_fields_lt A vector P orders locality pre post i j hij hip hjp his hjs
  · exact (clear_adjacent_fields_lt A vector P orders locality pre post j i hji hjp hip hjs his).symm

private theorem clear_permutation_fields_context (A : Fin N → VertexOperator ℂ V)
    (vector : V) (P : Module.End ℂ V) (orders : Fin N × Fin N → ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ orders (i, j)) (commutator (A i) (A j)) = 0)
    {l r : List (Fin N)} (hp : l.Perm r)
    (pre post : List (Fin N)) (hn : (pre ++ l ++ post).Nodup) :
    polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P (pre ++ l ++ post)) =
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P (pre ++ r ++ post)) := by
  induction hp generalizing pre post with
  | nil => rfl
  | cons i hp ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [i]) post (by simpa [List.append_assoc] using hn)
  | swap i j tail =>
    simpa only [List.cons_append, List.append_assoc] using
      clear_adjacent_fields A vector P orders locality pre (tail ++ post) j i
        (by simpa [List.append_assoc] using hn)
  | trans hp hq ihp ihq =>
    exact (ihp pre post hn).trans (ihq pre post
      (((hp.append_left pre).append_right post).nodup_iff.mp hn))
/-- A coordinate lower bound is pointwise on the actual input, not uniform in vectors. -/
def LowerBoundIn (F : Distribution N V) (i : Fin N) (lower : ℤ) : Prop :=
  ∀ e, e i < lower → F e = 0

private theorem difference_lower_bound (F : Distribution N V) (i j k : Fin N)
    (lower : ℤ) (hF : LowerBoundIn F i lower) :
    LowerBoundIn (difference j k F) i lower := by
  intro e he
  have hj : (e - Pi.single j 1 : Exponent N) i < lower := by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> omega
  have hk : (e - Pi.single k 1 : Exponent N) i < lower := by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> omega
  change F (e - Pi.single j 1) - F (e - Pi.single k 1) = 0
  rw [hF _ hj, hF _ hk, sub_self]

private theorem difference_power_lower_bound (F : Distribution N V) (i j k : Fin N)
    (n : ℕ) (lower : ℤ) (hF : LowerBoundIn F i lower) :
    LowerBoundIn ((difference j k ^ n) F) i lower := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact difference_lower_bound _ i j k lower ih

private theorem weighted_clearing_lower_bound (orders : Fin N × Fin N → ℕ)
    (F : Distribution N V) (i : Fin N) (lower : ℤ)
    (hF : LowerBoundIn F i lower) :
    LowerBoundIn (polynomialAction (weightedClearingPolynomial orders) F) i lower := by
  have general (s : Finset (Fin N × Fin N)) :
      LowerBoundIn (polynomialAction (∏ p ∈ s, pairPolynomial p.1 p.2 ^ orders p) F) i lower := by
    induction s using Finset.induction_on with
    | empty => simpa using hF
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp, map_mul, map_pow, action_pair, Module.End.mul_apply]
      exact difference_power_lower_bound _ i p.1 p.2 (orders p) lower ih
  exact general (labelledPairs N)

private theorem finite_laurent_simplex (lower : Fin N → ℤ) (total : ℤ) :
    {e : Exponent N | totalExponent e = total ∧ ∀ i, lower i ≤ e i}.Finite := by
  have finiteBox :
      (Set.univ.pi (fun i : Fin N => Set.Icc (lower i)
        (total - (∑ j, lower j) + lower i))).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  apply finiteBox.subset
  intro e he i _
  refine ⟨he.2 i, ?_⟩
  have bound : e i - lower i ≤ ∑ j, (e j - lower j) :=
    Finset.single_le_sum (fun j _ => sub_nonneg.mpr (he.2 j)) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib, show (∑ j, e j) = total from he.1] at bound
  omega

/-- Finite pair clearing gives one array in every order, with all coordinate
lower bounds simultaneously, on an arbitrary actual vector. -/
theorem common_cleared_fields (A : Fin N → VertexOperator ℂ V)
    (vector : V) (P : Module.End ℂ V) (orders : Fin N × Fin N → ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ orders (i, j)) (commutator (A i) (A j)) = 0)
    (l : List (Fin N)) (hn : l.Nodup) (hall : ∀ i, i ∈ l) :
    (∀ r, l.Perm r →
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l) =
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P r)) ∧
    (∀ i, LowerBoundIn
      (polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l)) i
      (((HahnModule.of ℂ).symm (A i vector)).order)) ∧
    (∀ total : ℤ, {e : Exponent N | totalExponent e = total ∧
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l) e ≠ 0}.Finite) := by
  have perm (r : List (Fin N)) (hp : l.Perm r) :
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l) =
      polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P r) := by
    simpa only [List.nil_append, List.append_nil] using
      clear_permutation_fields_context A vector P orders locality hp [] []
        (by simpa using hn)
  have lower : ∀ i, LowerBoundIn
      (polynomialAction (weightedClearingPolynomial orders)
        (coefficientDistribution A vector P l)) i
      (((HahnModule.of ℂ).symm (A i vector)).order) := by
    intro i
    have hp : l.Perm (l.erase i ++ [i]) :=
      (List.perm_cons_erase (hall i)).trans (by
        simpa using (List.perm_append_comm (l₁ := [i]) (l₂ := l.erase i)))
    rw [perm _ hp]
    apply weighted_clearing_lower_bound
    intro e he
    have zero : (A i [[-e i - 1]]) vector = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      simpa using he
    simp [coefficientDistribution, word_append_adapter, word, Module.End.mul_apply, zero]

  refine ⟨perm, lower, ?_⟩
  intro total
  apply (finite_laurent_simplex
    (fun i => ((HahnModule.of ℂ).symm (A i vector)).order) total).subset
  intro e he
  refine ⟨he.1, ?_⟩
  intro i
  by_contra below
  exact he.2 (lower i e (lt_of_not_ge below))

end

end D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.WeightedLocalCorrelator
