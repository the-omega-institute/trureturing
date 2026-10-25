/- GID: D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Locality and statewise truncation give common infinite vector word series. -/

import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
Classical formal-variable locality, with the Matsuo--Nagatomo and Carnahan
attributions retained in the imported suppliers. The contextual-exchange
proof is generalized from the imported public pair lift and intertwining laws.
The frozen graded supplier remains unchanged.
proof_shape: content
admission_basis: escape-witness
escape_witness: after clearing, each label can be moved rightmost. Its actual
truncation on the original input bounds that coordinate independently of all
other signed exponents. Intersecting those bounds yields a rectangle, without
energy, finite support, homogeneous states, or a common-product premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.UngradedLocalWordSeries

open UniformGradedLocalCorrelator
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Finite Laurent convolution commutes with a linear vector readout. -/
theorem polynomialAction_map {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (q : LaurentPolynomial N) (F : Distribution N V)
    (e : Exponent N) :
    f (polynomialAction q F e) =
      polynomialAction q (fun d => f (F d)) e := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
    simpa only [map_add, LinearMap.add_apply, Pi.add_apply, hq, hr]
  | single b c =>
    change f (c • F (e - b)) = c • f (F (e - b))
    exact f.map_smul c _

/-- Strict lower support in one labelled coordinate; other exponents are arbitrary. -/
private def BelowIn (F : Distribution N V) (i : Fin N) (b : ℤ) : Prop :=
  ∀ e, e i < b → F e = 0

private theorem word_append (A : Fin N → VertexOperator ℂ V)
    (l r : List (Fin N)) (e : Exponent N) : word A (l ++ r) e = word A l e * word A r e := by
  induction l with
  | nil => simp [word]
  | cons i l ih => simp [word, ih, mul_assoc]

private theorem clearing_kills (i j : Fin N) (k : ℕ) (hij : i < j)
    (F : Distribution N V) (hF : (difference i j ^ k) F = 0) :
    polynomialAction (clearingPolynomial N k) F = 0 := by
  have hm : (i, j) ∈ labelledPairs N := by simp [labelledPairs, hij]
  have factor := Finset.prod_erase_mul (labelledPairs N)
    (fun p => pairPolynomial p.1 p.2 ^ k) hm
  change polynomialAction (∏ p ∈ labelledPairs N, pairPolynomial p.1 p.2 ^ k) F = 0
  rw [← factor, map_mul, map_pow, action_pair, Module.End.mul_apply, hF, map_zero]

private theorem clear_adjacent_lt (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (k : ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ k) (commutator (A i) (A j)) = 0)
    (pre post : List (Fin N)) (i j : Fin N) (hij : i < j)
    (hip : i ∉ pre) (hjp : j ∉ pre) (his : i ∉ post) (hjs : j ∉ post) :
    polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A Ω P (pre ++ i :: j :: post)) =
      polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A Ω P (pre ++ j :: i :: post)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← liftPair_commutator]
  apply clearing_kills i j k hij
  rw [intertwine_power deltaEnd (difference i j) (liftPair A Ω P pre post i j)
    (liftPair_difference A Ω P pre post i j (ne_of_lt hij) hip hjp his hjs),
    locality i j hij, map_zero]

private theorem clear_adjacent (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (k : ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ k) (commutator (A i) (A j)) = 0)
    (pre post : List (Fin N)) (i j : Fin N)
    (hn : (pre ++ i :: j :: post).Nodup) :
    polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A Ω P (pre ++ i :: j :: post)) =
      polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A Ω P (pre ++ j :: i :: post)) := by
  have hs := (List.nodup_append.mp hn).2.1
  have hcross := (List.nodup_append.mp hn).2.2
  have hip : i ∉ pre := by intro hi; exact hcross i hi i (by simp) rfl
  have hjp : j ∉ pre := by intro hj; exact hcross j hj j (by simp) rfl
  have his : i ∉ post := fun hi => (List.nodup_cons.mp hs).1 (by simp [hi])
  have hjs : j ∉ post := (List.nodup_cons.mp (List.nodup_cons.mp hs).2).1
  have hne : i ≠ j := by intro he; exact (List.nodup_cons.mp hs).1 (by simp [he])
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact clear_adjacent_lt A Ω P k locality pre post i j hij hip hjp his hjs
  · exact (clear_adjacent_lt A Ω P k locality pre post j i hji hjp hip hjs his).symm

/-- Contextual exchange requires only actual operator locality. Labels, rather
than field values, are distinct. No vacuum, grading or creation law is used. -/
private theorem clear_permutation_context (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (k : ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ k) (commutator (A i) (A j)) = 0)
    {l r : List (Fin N)} (hp : l.Perm r)
    (pre post : List (Fin N)) (hn : (pre ++ l ++ post).Nodup) :
    polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A Ω P (pre ++ l ++ post)) =
      polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A Ω P (pre ++ r ++ post)) := by
  induction hp generalizing pre post with
  | nil => rfl
  | cons i hp ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [i]) post (by simpa [List.append_assoc] using hn)
  | swap i j tail =>
    simpa only [List.cons_append, List.append_assoc] using
      clear_adjacent A Ω P k locality pre (tail ++ post) j i
        (by simpa [List.append_assoc] using hn)
  | trans hp hq ihp ihq =>
    exact (ihp pre post hn).trans (ihq pre post
      (((hp.append_left pre).append_right post).nodup_iff.mp hn))

private theorem difference_below (F : Distribution N V) (i j l : Fin N)
    (b : ℤ) (hF : BelowIn F i b) : BelowIn (difference j l F) i b := by
  intro e he
  have hj : (e - Pi.single j 1 : Exponent N) i < b := by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> omega
  have hl : (e - Pi.single l 1 : Exponent N) i < b := by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> omega
  change F (e - Pi.single j 1) - F (e - Pi.single l 1) = 0
  rw [hF _ hj, hF _ hl, sub_self]

private theorem difference_power_below (F : Distribution N V) (i j l : Fin N)
    (b : ℤ) (n : ℕ) (hF : BelowIn F i b) :
    BelowIn ((difference j l ^ n) F) i b := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact difference_below _ i j l b ih

private theorem clearing_below (k : ℕ) (F : Distribution N V) (i : Fin N)
    (b : ℤ) (hF : BelowIn F i b) :
    BelowIn (polynomialAction (clearingPolynomial N k) F) i b := by
  have general (s : Finset (Fin N × Fin N)) :
      BelowIn (polynomialAction (∏ p ∈ s, pairPolynomial p.1 p.2 ^ k) F) i b := by
    induction s using Finset.induction_on with
    | empty => simpa using hF
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp, map_mul, map_pow, action_pair, Module.End.mul_apply]
      exact difference_power_below _ i p.1 p.2 b k ih
  exact general (labelledPairs N)

/-- Move each label rightmost, use its truncation on the original input Ω,
and preserve that bound under the clearing polynomial's nonnegative shifts.
The bound on one coordinate is uniform in every other signed exponent. -/
private theorem clear_all_below (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (k : ℕ)
    (locality : ∀ i j : Fin N, i < j →
      (deltaEnd ^ k) (commutator (A i) (A j)) = 0)
    (l : List (Fin N)) (hn : l.Nodup) (hall : ∀ i, i ∈ l)
    (b : Exponent N)
    (truncation : ∀ (i : Fin N) (n : ℤ), -b i ≤ n → (A i [[n]]) Ω = 0)
    (i : Fin N) :
    BelowIn (polynomialAction (clearingPolynomial N k)
      (coefficientDistribution A Ω P l)) i (b i) := by
  have hp : l.Perm (l.erase i ++ [i]) :=
    (List.perm_cons_erase (hall i)).trans (by
      simpa using (List.perm_append_comm (l₁ := [i]) (l₂ := l.erase i)))
  have eq := clear_permutation_context A Ω P k locality hp [] [] (by simpa using hn)
  simp only [List.nil_append, List.append_nil] at eq
  rw [eq]
  apply clearing_below
  intro e he
  have zero : (A i [[-e i - 1]]) Ω = 0 := truncation i _ (by omega)
  simp [coefficientDistribution, word_append, word, Module.End.mul_apply, zero]

/-- The native finitely supported multi-index on a finite label type.
This is an index, not a finite-support assertion about the power series. -/
def signedIndex (e : Exponent N) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i).toNat)

/-- Zero extension of the native vector-valued MvPowerSeries to every signed
multi-index. P d is its native coefficient function; the named Mathlib coeff
linear map would unnecessarily require a semiring structure on V. -/
def signedExtend (P : MvPowerSeries (Fin N) V) (e : Exponent N) : V :=
  if ∀ i, 0 ≤ e i then P (signedIndex e) else 0

/-- Signed extension commutes with vector readouts, with no target multiplication. -/
theorem signedExtend_map {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (P : MvPowerSeries (Fin N) V) (e : Exponent N) :
    f (signedExtend P e) = signedExtend (fun d => f (P d)) e := by
  classical
  by_cases h : ∀ i, 0 ≤ e i <;> simp [signedExtend, h]

private theorem power_kills_of_le {X : Type*} [AddCommGroup X] [Module ℂ X]
    (E : Module.End ℂ X) (x : X) {r k : ℕ} (hrk : r ≤ k)
    (hx : (E ^ r) x = 0) : (E ^ k) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrk
  rw [add_comm r d, pow_add, Module.End.mul_apply, hx, map_zero]

/-- Pairwise locality orders have a finite common upper order. It is selected
from the labelled fields alone, before an input vector is supplied. -/
private theorem uniform_locality_order (A : Fin N → VertexOperator ℂ V)
    (locality : ∀ i j : Fin N, i < j →
      ∃ r : ℕ, (deltaEnd ^ r) (commutator (A i) (A j)) = 0) :
    ∃ k : ℕ, ∀ i j : Fin N, i < j →
      (deltaEnd ^ k) (commutator (A i) (A j)) = 0 := by
  classical
  let r : Fin N × Fin N → ℕ := fun p =>
    if h : p.1 < p.2 then Classical.choose (locality p.1 p.2 h) else 0
  let k : ℕ := ∑ p ∈ labelledPairs N, r p
  refine ⟨k, ?_⟩
  intro i j hij
  have member : (i, j) ∈ labelledPairs N := by simp [labelledPairs, hij]
  have bound : r (i, j) ≤ k :=
    Finset.single_le_sum (fun p _ => Nat.zero_le (r p)) member
  have killed : (deltaEnd ^ r (i, j)) (commutator (A i) (A j)) = 0 := by
    simpa only [r, dif_pos hij] using Classical.choose_spec (locality i j hij)
  exact power_kills_of_le deltaEnd _ bound killed

/-- An arbitrary finite complete labelled word of mutually local actual fields
has a common, generally infinite, vector power series after polynomial clearing
and a statewise nonnegative monomial shift.

The order k is chosen before w. The tuple a comes only from truncation A_i on w.
The rectangle and common cleared product are conclusions. All signed regions,
including below support, and all permutations of distinct labels are covered.
Field values may repeat. For N=0 use order=[]; every construction is still total.
No polynomial inverse or cancellation on unrestricted distributions occurs. -/
theorem ungraded_local_word_common_series
    (A : Fin N → VertexOperator ℂ V) (order : List (Fin N))
    (nodup : order.Nodup) (all_labels : ∀ i, i ∈ order)
    (locality : ∀ i j : Fin N, i < j →
      ∃ r : ℕ, (deltaEnd ^ r) (commutator (A i) (A j)) = 0) :
    ∃ k : ℕ,
      (∀ i j : Fin N, i < j →
        (deltaEnd ^ k) (commutator (A i) (A j)) = 0) ∧
      ∀ w : V, ∃ a : Fin N → ℕ, ∃ P : MvPowerSeries (Fin N) V,
        (∀ (i : Fin N) (n : ℤ), (a i : ℤ) ≤ n → (A i [[n]]) w = 0) ∧
        (∀ (other : List (Fin N)), order.Perm other → ∀ e : Exponent N,
          (∃ i, e i < -(a i : ℤ)) →
          polynomialAction (clearingPolynomial N k)
            (coefficientDistribution A w 1 other) e = 0) ∧
        ∀ (other : List (Fin N)), order.Perm other → ∀ e : Exponent N,
          polynomialAction (clearingPolynomial N k)
            (coefficientDistribution A w 1 other) (fun i => e i - a i) =
              signedExtend P e := by
  classical
  obtain ⟨k, hk⟩ := uniform_locality_order A locality
  refine ⟨k, hk, ?_⟩
  intro w
  let a : Fin N → ℕ := fun i =>
    (-((HahnModule.of ℂ).symm (A i w)).order).toNat
  have truncation : ∀ (i : Fin N) (n : ℤ),
      (a i : ℤ) ≤ n → (A i [[n]]) w = 0 := by
    intro i n hn
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    dsimp only [a] at hn
    omega
  let F : Distribution N V := polynomialAction (clearingPolynomial N k)
    (coefficientDistribution A w 1 order)
  have below (i : Fin N) : BelowIn F i (-(a i : ℤ)) := by
    apply clear_all_below A w 1 k hk order nodup all_labels
      (fun j => -(a j : ℤ))
    intro j n hn
    exact truncation j n (by simpa using hn)
  have equal (other : List (Fin N)) (hp : order.Perm other) :
      F = polynomialAction (clearingPolynomial N k)
        (coefficientDistribution A w 1 other) := by
    simpa only [List.nil_append, List.append_nil] using
      clear_permutation_context A w 1 k hk hp [] [] (by simpa using nodup)
  let P : MvPowerSeries (Fin N) V := fun d => F (fun i => (d i : ℤ) - a i)
  refine ⟨a, P, truncation, ?_, ?_⟩
  · intro other hp e low
    rw [← equal other hp]
    obtain ⟨i, hi⟩ := low
    exact below i e hi
  · intro other hp e
    rw [← equal other hp]
    by_cases h : ∀ i, 0 ≤ e i
    · rw [signedExtend, if_pos h]
      change F (fun i => e i - a i) =
        F (fun i => ((signedIndex e) i : ℤ) - a i)
      congr 1
      funext i
      simp [signedIndex, Int.toNat_of_nonneg (h i)]
    · rw [signedExtend, if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact below i _ (by dsimp; omega)

#print axioms ungraded_local_word_common_series

end
end D5.S3.VertexAlgebra.UngradedLocalWordSeries
