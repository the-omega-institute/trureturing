/- GID: D5/S3/VertexAlgebra/UniformGradedLocalCorrelator
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/UniformGradedLocalCorrelator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite homogeneous numerators of actual graded local field products. -/

/-
proof_shape: uniform_graded_local_correlator: content
admission_basis: escape-witness
escape_witness: Actual pairwise operator locality yields the common labelled
cleared distribution through contextual adjacent exchanges and arbitrary list
permutations. Creation in each rightmost ordering and energy covariance then
produce nonnegative homogeneous support and a finite-box Finsupp numerator.
No finite-support or cleared-permutation certificate is among the field laws.
The uniform locality order is an actual operator law, not a weight-bound claim.
This is a generic field theorem, with no moonshine carrier identification.
-/

import D5.S3.VertexAlgebra.FieldNormalProductLocality
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.UniformGradedLocalCorrelator

open scoped BigOperators VertexOperator
open D5.S3.VertexAlgebra.FieldNormalProductLocality (commutator deltaEnd)

noncomputable section

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev Exponent (N : ℕ) := Fin N → ℤ
abbrev Distribution (N : ℕ) (V : Type*) := Exponent N → V
abbrev LaurentPolynomial (N : ℕ) := AddMonoidAlgebra ℂ (Exponent N)
abbrev VectorPolynomial (N : ℕ) (V : Type*) [Zero V] := (Fin N → ℕ) →₀ V

/-- Translation of exponents is multiplication by a labelled Laurent monomial. -/
def shift (b : Exponent N) : Module.End ℂ (Distribution N V) where
  toFun F := fun e => F (e - b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def shifts : Multiplicative (Exponent N) →* Module.End ℂ (Distribution N V) where
  toFun b := shift b.toAdd
  map_one' := by ext F e; simp [shift]
  map_mul' b c := by
    ext F e
    change F (e - (b.toAdd + c.toAdd)) = F ((e - b.toAdd) - c.toAdd)
    congr 1
    abel

/-- Finite convolution, defined on all coefficient distributions. -/
def polynomialAction : LaurentPolynomial N →ₐ[ℂ] Module.End ℂ (Distribution N V) :=
  AddMonoidAlgebra.lift ℂ _ _ shifts

def variablePolynomial (i : Fin N) : LaurentPolynomial N :=
  AddMonoidAlgebra.single (Pi.single i 1) 1

def pairPolynomial (i j : Fin N) : LaurentPolynomial N :=
  variablePolynomial i - variablePolynomial j

def difference (i j : Fin N) : Module.End ℂ (Distribution N V) :=
  shift (Pi.single i 1) - shift (Pi.single j 1)

private theorem action_pair (i j : Fin N) :
    (polynomialAction (V := V)) (pairPolynomial i j) = difference i j := by
  simp [polynomialAction, pairPolynomial, variablePolynomial, difference,
    AddMonoidAlgebra.lift_single, shifts]

def labelledPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- The labels stay fixed: Q is the product over i < j of (z_i - z_j)^k. -/
def clearingPolynomial (N k : ℕ) : LaurentPolynomial N :=
  ∏ p ∈ labelledPairs N, pairPolynomial p.1 p.2 ^ k

/-- Successive application of the actual modes; e corresponds to mode -e-1. -/
def word (A : Fin N → VertexOperator ℂ V) : List (Fin N) → Exponent N → Module.End ℂ V
  | [], _ => 1
  | i :: tail, e => (A i [[-e i - 1]]) * word A tail e

def coefficientDistribution (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (order : List (Fin N)) : Distribution N V :=
  fun e => P (word A order e Ω)

/-- Laws of actual fields, with a uniform locality order, not a product certificate. -/
structure GradedLocalFields (N : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] where
  field : Fin N → VertexOperator ℂ V
  weight : Fin N → ℕ
  vacuum : V
  energy : Module.End ℂ V
  vacuum_grade : energy vacuum = 0
  covariance : ∀ (i : Fin N) (e : ℤ),
    energy * (field i [[-e - 1]]) - (field i [[-e - 1]]) * energy =
      (((weight i : ℤ) + e : ℤ) : ℂ) • (field i [[-e - 1]])
  creation : ∀ (i : Fin N) (n : ℤ), 0 ≤ n → (field i [[n]]) vacuum = 0
  localityOrder : ℕ
  locality : ∀ (i j : Fin N), i < j →
    (deltaEnd ^ localityOrder) (commutator (field i) (field j)) = 0

/-- An actual projection onto the energy-d eigenspace. -/
structure OutputGradeSelector (H : Module.End ℂ V) (d : ℤ) where
  map : Module.End ℂ V
  idempotent : map * map = map
  output_grade : H * map = (d : ℂ) • map
  input_grade : map * H = (d : ℂ) • map
  fixes_grade : ∀ v, H v = (d : ℂ) • v → map v = v

def totalExponent (e : Exponent N) : ℤ := ∑ i, e i

def Homogeneous (F : Distribution N V) (D : ℤ) : Prop :=
  ∀ e, totalExponent e ≠ D → F e = 0

def NonnegativeIn (F : Distribution N V) (i : Fin N) : Prop :=
  ∀ e, e i < 0 → F e = 0

private theorem word_append (A : Fin N → VertexOperator ℂ V)
    (l r : List (Fin N)) (e : Exponent N) : word A (l ++ r) e = word A l e * word A r e := by
  induction l with
  | nil => simp [word]
  | cons i l ih => simp [word, ih, mul_assoc]

private theorem word_congr (A : Fin N → VertexOperator ℂ V) (l : List (Fin N))
    (e f : Exponent N) (h : ∀ i ∈ l, e i = f i) : word A l e = word A l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [word, h i (by simp), ih (fun j hj => h j (by simp [hj]))]

private theorem word_shift (A : Fin N → VertexOperator ℂ V) (l : List (Fin N))
    (e : Exponent N) (i : Fin N) (hi : i ∉ l) :
    word A l (e - Pi.single i 1) = word A l e := by
  apply word_congr
  intro j hj
  have ne : j ≠ i := by rintro rfl; exact hi hj
  simp [ne]

private def liftPair (A : Fin N → VertexOperator ℂ V) (Ω : V) (P : Module.End ℂ V)
    (pre post : List (Fin N)) (i j : Fin N) :
    (ℤ → ℤ → Module.End ℂ V) →ₗ[ℂ] Distribution N V where
  toFun C := fun e => P (word A pre e (C (-e i - 1) (-e j - 1) (word A post e Ω)))
  map_add' C E := by ext e; simp [map_add]
  map_smul' c C := by ext e; simp [map_smul]

private theorem liftPair_difference (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (pre post : List (Fin N)) (i j : Fin N) (hne : i ≠ j)
    (hip : i ∉ pre) (hjp : j ∉ pre) (his : i ∉ post) (hjs : j ∉ post)
    (C : ℤ → ℤ → Module.End ℂ V) :
    difference i j (liftPair A Ω P pre post i j C) =
      liftPair A Ω P pre post i j (deltaEnd C) := by
  ext e
  have ii : -(e i - 1) - 1 = (-e i - 1) + 1 := by omega
  have jj : -(e j - 1) - 1 = (-e j - 1) + 1 := by omega
  simp only [difference, LinearMap.sub_apply, shift, LinearMap.coe_mk, AddHom.coe_mk,
    liftPair, word_shift A pre e i hip, word_shift A pre e j hjp,
    word_shift A post e i his, word_shift A post e j hjs,
    deltaEnd, D5.S3.VertexAlgebra.FieldNormalProductLocality.delta, map_sub,
    Pi.sub_apply, LinearMap.sub_apply]
  simp only [Pi.single_apply, hne, hne.symm, if_false, if_true, sub_zero, ii, jj]

private theorem intertwine_power {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (a : Module.End ℂ X) (b : Module.End ℂ Y)
    (L : X →ₗ[ℂ] Y) (law : ∀ x, b (L x) = L (a x)) (k : ℕ) (x : X) :
    (b ^ k) (L x) = L ((a ^ k) x) := by
  have h : Function.Semiconj L a b := fun x => (law x).symm
  simpa only [Module.End.pow_apply] using (h.iterate_right k x).symm

private theorem liftPair_commutator (A : Fin N → VertexOperator ℂ V) (Ω : V)
    (P : Module.End ℂ V) (pre post : List (Fin N)) (i j : Fin N) :
    liftPair A Ω P pre post i j (commutator (A i) (A j)) =
      coefficientDistribution A Ω P (pre ++ i :: j :: post) -
        coefficientDistribution A Ω P (pre ++ j :: i :: post) := by
  ext e
  simp [liftPair, coefficientDistribution, word_append, word,
    D5.S3.VertexAlgebra.FieldNormalProductLocality.commutator,
    Module.End.mul_apply, map_sub]

private theorem clearing_kills (i j : Fin N) (k : ℕ) (hij : i < j)
    (F : Distribution N V) (hF : (difference i j ^ k) F = 0) :
    polynomialAction (clearingPolynomial N k) F = 0 := by
  have hm : (i, j) ∈ labelledPairs N := by simp [labelledPairs, hij]
  have factor := Finset.prod_erase_mul (labelledPairs N)
    (fun p => pairPolynomial p.1 p.2 ^ k) hm
  change polynomialAction (∏ p ∈ labelledPairs N, pairPolynomial p.1 p.2 ^ k) F = 0
  rw [← factor, map_mul, map_pow, action_pair, Module.End.mul_apply, hF, map_zero]

private theorem clear_adjacent_lt (D : GradedLocalFields N V) (P : Module.End ℂ V)
    (pre post : List (Fin N)) (i j : Fin N) (hij : i < j)
    (hip : i ∉ pre) (hjp : j ∉ pre) (his : i ∉ post) (hjs : j ∉ post) :
    polynomialAction (clearingPolynomial N D.localityOrder)
        (coefficientDistribution D.field D.vacuum P (pre ++ i :: j :: post)) =
      polynomialAction (clearingPolynomial N D.localityOrder)
        (coefficientDistribution D.field D.vacuum P (pre ++ j :: i :: post)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← liftPair_commutator]
  apply clearing_kills i j D.localityOrder hij
  rw [intertwine_power deltaEnd (difference i j) (liftPair D.field D.vacuum P pre post i j)
    (liftPair_difference D.field D.vacuum P pre post i j (ne_of_lt hij) hip hjp his hjs),
    D.locality i j hij, map_zero]

private theorem clear_adjacent (D : GradedLocalFields N V) (P : Module.End ℂ V)
    (pre post : List (Fin N)) (i j : Fin N)
    (hn : (pre ++ i :: j :: post).Nodup) :
    polynomialAction (clearingPolynomial N D.localityOrder)
        (coefficientDistribution D.field D.vacuum P (pre ++ i :: j :: post)) =
      polynomialAction (clearingPolynomial N D.localityOrder)
        (coefficientDistribution D.field D.vacuum P (pre ++ j :: i :: post)) := by
  have hs := (List.nodup_append.mp hn).2.1
  have hcross := (List.nodup_append.mp hn).2.2
  have hip : i ∉ pre := by intro hi; exact hcross i hi i (by simp) rfl
  have hjp : j ∉ pre := by intro hj; exact hcross j hj j (by simp) rfl
  have his : i ∉ post := fun hi => (List.nodup_cons.mp hs).1 (by simp [hi])
  have hjs : j ∉ post := (List.nodup_cons.mp (List.nodup_cons.mp hs).2).1
  have hne : i ≠ j := by intro he; exact (List.nodup_cons.mp hs).1 (by simp [he])
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact clear_adjacent_lt D P pre post i j hij hip hjp his hjs
  · exact (clear_adjacent_lt D P pre post j i hji hjp hip hjs his).symm

private theorem clear_permutation_context (D : GradedLocalFields N V)
    (P : Module.End ℂ V) {l r : List (Fin N)} (hp : l.Perm r)
    (pre post : List (Fin N)) (hn : (pre ++ l ++ post).Nodup) :
    polynomialAction (clearingPolynomial N D.localityOrder)
        (coefficientDistribution D.field D.vacuum P (pre ++ l ++ post)) =
      polynomialAction (clearingPolynomial N D.localityOrder)
        (coefficientDistribution D.field D.vacuum P (pre ++ r ++ post)) := by
  induction hp generalizing pre post with
  | nil => rfl
  | cons i hp ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [i]) post (by simpa [List.append_assoc] using hn)
  | swap i j tail =>
    simpa only [List.cons_append, List.append_assoc] using clear_adjacent D P pre
      (tail ++ post) j i (by simpa [List.append_assoc] using hn)
  | trans hp hq ihp ihq =>
    exact (ihp pre post hn).trans (ihq pre post
      (((hp.append_left pre).append_right post).nodup_iff.mp hn))

private theorem difference_nonnegative (F : Distribution N V) (i j k : Fin N)
    (hF : NonnegativeIn F i) : NonnegativeIn (difference j k F) i := by
  intro e he
  have hj : (e - Pi.single j 1 : Exponent N) i < 0 := by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> omega
  have hk : (e - Pi.single k 1 : Exponent N) i < 0 := by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> omega
  change F (e - Pi.single j 1) - F (e - Pi.single k 1) = 0
  rw [hF _ hj, hF _ hk, sub_self]

private theorem difference_power_nonnegative (F : Distribution N V) (i j k : Fin N)
    (n : ℕ) (hF : NonnegativeIn F i) : NonnegativeIn ((difference j k ^ n) F) i := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact difference_nonnegative _ i j k ih

private theorem clearing_nonnegative (k : ℕ) (F : Distribution N V) (i : Fin N)
    (hF : NonnegativeIn F i) :
    NonnegativeIn (polynomialAction (clearingPolynomial N k) F) i := by
  have general (s : Finset (Fin N × Fin N)) :
      NonnegativeIn (polynomialAction (∏ p ∈ s, pairPolynomial p.1 p.2 ^ k) F) i := by
    induction s using Finset.induction_on with
    | empty => simpa using hF
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp, map_mul, map_pow, action_pair, Module.End.mul_apply]
      exact difference_power_nonnegative _ i p.1 p.2 k ih
  exact general (labelledPairs N)

private theorem clear_all_nonnegative (D : GradedLocalFields N V) (P : Module.End ℂ V)
    (l : List (Fin N)) (hn : l.Nodup) (hall : ∀ i, i ∈ l) (i : Fin N) :
    NonnegativeIn (polynomialAction (clearingPolynomial N D.localityOrder)
      (coefficientDistribution D.field D.vacuum P l)) i := by
  have hp : l.Perm (l.erase i ++ [i]) :=
    (List.perm_cons_erase (hall i)).trans (by
      simpa using (List.perm_append_comm (l₁ := [i]) (l₂ := l.erase i)))
  have eq := clear_permutation_context D P hp [] [] (by simpa using hn)
  simp only [List.nil_append, List.append_nil] at eq
  rw [eq]
  apply clearing_nonnegative
  intro e he
  have zero : (D.field i [[-e i - 1]]) D.vacuum = 0 := D.creation i _ (by omega)
  simp [coefficientDistribution, word_append, word, Module.End.mul_apply, zero]

private theorem word_energy (D : GradedLocalFields N V) (l : List (Fin N))
    (e : Exponent N) :
    D.energy (word D.field l e D.vacuum) =
      (((l.map (fun i => (D.weight i : ℤ) + e i)).sum : ℤ) : ℂ) •
        word D.field l e D.vacuum := by
  induction l with
  | nil => simpa [word] using D.vacuum_grade
  | cons i l ih =>
    have hc := congrArg (fun T : Module.End ℂ V => T (word D.field l e D.vacuum))
      (D.covariance i (e i))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, ih,
      map_smul] at hc
    have eq := sub_eq_iff_eq_add.mp hc
    simp only [word, Module.End.mul_apply, List.map_cons, List.sum_cons, Int.cast_add]
    rw [add_smul]
    simpa only [Int.cast_add] using eq

private theorem distribution_homogeneous (D : GradedLocalFields N V) (d : ℤ)
    (P : OutputGradeSelector D.energy d) (l : List (Fin N)) (hn : l.Nodup)
    (hall : ∀ i, i ∈ l) :
    Homogeneous (coefficientDistribution D.field D.vacuum P.map l)
      (d - ∑ i, (D.weight i : ℤ)) := by
  intro e he
  have full : l.toFinset = Finset.univ := by ext i; simp [hall i]
  have sumEq : (l.map (fun i => (D.weight i : ℤ) + e i)).sum =
      (∑ i, (D.weight i : ℤ)) + totalExponent e := by
    rw [← List.sum_toFinset _ hn, full, Finset.sum_add_distrib]
    rfl
  have hc := congrArg (fun T : Module.End ℂ V => T (word D.field l e D.vacuum)) P.input_grade
  simp only [Module.End.mul_apply, LinearMap.smul_apply, word_energy, map_smul, sumEq] at hc
  have hz : ((((∑ i, (D.weight i : ℤ)) + totalExponent e : ℤ) : ℂ) - (d : ℂ)) •
      P.map (word D.field l e D.vacuum) = 0 := by rw [sub_smul, hc, sub_self]
  have ne : (((∑ i, (D.weight i : ℤ)) + totalExponent e : ℤ) : ℂ) - (d : ℂ) ≠ 0 := by
    intro h
    have hi : (∑ i, (D.weight i : ℤ)) + totalExponent e = d := by
      exact_mod_cast sub_eq_zero.mp h
    apply he
    omega
  exact (smul_eq_zero.mp hz).resolve_left ne

private theorem total_shift (e : Exponent N) (i : Fin N) :
    totalExponent (e - Pi.single i 1) = totalExponent e - 1 := by
  simp [totalExponent, Finset.sum_sub_distrib]

private theorem difference_homogeneous (F : Distribution N V) (D : ℤ)
    (i j : Fin N) (hF : Homogeneous F D) : Homogeneous (difference i j F) (D + 1) := by
  intro e he
  change F (e - Pi.single i 1) - F (e - Pi.single j 1) = 0
  rw [hF _ (by rw [total_shift]; omega), hF _ (by rw [total_shift]; omega), sub_self]

private theorem difference_power_homogeneous (F : Distribution N V) (D : ℤ)
    (i j : Fin N) (k : ℕ) (hF : Homogeneous F D) :
    Homogeneous ((difference i j ^ k) F) (D + k) := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa [Nat.cast_add, add_assoc] using difference_homogeneous _ (D + k) i j ih

private theorem clearing_homogeneous (F : Distribution N V) (D : ℤ) (k : ℕ)
    (hF : Homogeneous F D) :
    Homogeneous (polynomialAction (clearingPolynomial N k) F)
      (D + (k * (labelledPairs N).card : ℕ)) := by
  have general (s : Finset (Fin N × Fin N)) :
      Homogeneous (polynomialAction (∏ p ∈ s, pairPolynomial p.1 p.2 ^ k) F)
        (D + (k * s.card : ℕ)) := by
    induction s using Finset.induction_on with
    | empty => simpa using hF
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp, map_mul, map_pow, action_pair, Module.End.mul_apply]
      have hh := difference_power_homogeneous _ (D + (k * s.card : ℕ)) p.1 p.2 k ih
      simpa [Finset.card_insert_of_notMem hp, Nat.mul_add, Nat.cast_add, add_assoc] using hh
  exact general (labelledPairs N)

private theorem action_submodule (q : LaurentPolynomial N) (F : Distribution N V)
    (W : Submodule ℂ V) (hF : ∀ e, F e ∈ W) : ∀ e, polynomialAction q F e ∈ W := by
  intro e
  rw [polynomialAction, AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, shifts,
    MonoidHom.coe_mk, OneHom.coe_mk, shift, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply]
  exact W.sum_mem (fun b hb => W.smul_mem _ (hF (e - b)))

def naturalExponent (a : Fin N → ℕ) : Exponent N := fun i => a i

omit [Module ℂ V] in
private theorem homogeneous_finite_support (F : Distribution N V) (D : ℤ)
    (hF : Homogeneous F D) :
    (Function.support (fun a : Fin N → ℕ => F (naturalExponent a))).Finite := by
  have finiteBox : (Set.univ.pi (fun _ : Fin N => Set.Icc 0 D.toNat)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  apply finiteBox.subset
  intro a ha
  have hdegree : totalExponent (naturalExponent a) = D := by
    by_contra he
    exact ha (hF _ he)
  intro i hi
  refine ⟨Nat.zero_le _, ?_⟩
  have leSum : (a i : ℤ) ≤ totalExponent (naturalExponent a) := by
    apply Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ i)
    exact Int.natCast_nonneg _
  have bound : (a i : ℤ) ≤ D := by simpa only [hdegree] using leSum
  have natBound := Int.toNat_le_toNat bound
  simpa using natBound

def numeratorDegree (D : GradedLocalFields N V) (d : ℤ) : ℤ :=
  d - ∑ i, (D.weight i : ℤ) + (D.localityOrder * (labelledPairs N).card : ℕ)

/-- The uniform finite-numerator certificate for actual graded local fields.
The support and common cleared product are conclusions of locality, creation and covariance.
The coefficient space W need only contain one ordering. No factor is cancelled in distributions. -/
theorem uniform_graded_local_correlator (D : GradedLocalFields N V) (d : ℤ)
    (P : OutputGradeSelector D.energy d) (order : List (Fin N))
    (nodup : order.Nodup) (all_labels : ∀ i, i ∈ order)
    (W : Submodule ℂ V)
    (in_W : ∀ e, coefficientDistribution D.field D.vacuum P.map order e ∈ W) :
    ∃ numerator : VectorPolynomial N V,
      (∀ other : List (Fin N), order.Perm other → ∀ e : Exponent N,
        polynomialAction (clearingPolynomial N D.localityOrder)
            (coefficientDistribution D.field D.vacuum P.map other) e =
          if ∀ i, 0 ≤ e i then numerator (fun i => (e i).toNat) else 0) ∧
      (∀ a : Fin N → ℕ, numerator a ≠ 0 →
        totalExponent (naturalExponent a) = numeratorDegree D d) ∧
      (∀ a, numerator a ∈ W) ∧
      (numeratorDegree D d < 0 → numerator = 0) := by
  let F : Distribution N V := polynomialAction (clearingPolynomial N D.localityOrder)
    (coefficientDistribution D.field D.vacuum P.map order)
  have hhom : Homogeneous F (numeratorDegree D d) :=
    clearing_homogeneous _ _ D.localityOrder
      (distribution_homogeneous D d P order nodup all_labels)
  have hnonneg : ∀ i, NonnegativeIn F i := clear_all_nonnegative D P.map order nodup all_labels
  let numerator : VectorPolynomial N V := Finsupp.ofSupportFinite
    (fun a => F (naturalExponent a)) (homogeneous_finite_support F _ hhom)
  have eval (a : Fin N → ℕ) : numerator a = F (naturalExponent a) := rfl
  refine ⟨numerator, ?_, ?_, ?_, ?_⟩
  · intro other hp e
    have heq := clear_permutation_context D P.map hp [] [] (by simpa using nodup)
    simp only [List.nil_append, List.append_nil] at heq
    rw [← heq]
    change F e = _
    split_ifs with he
    · rw [eval]
      congr 1
      funext i
      exact (Int.toNat_of_nonneg (he i)).symm
    · push Not at he
      obtain ⟨i, hi⟩ := he
      exact hnonneg i e hi
  · intro a ha
    by_contra he
    exact ha ((eval a).trans (hhom _ he))
  · intro a
    rw [eval]
    exact action_submodule _ _ W in_W _
  · intro hd
    ext a
    rw [eval]
    apply hhom
    have positive : 0 ≤ totalExponent (naturalExponent a) :=
      Finset.sum_nonneg (fun i _ => Int.natCast_nonneg _)
    omega

#print axioms uniform_graded_local_correlator

end

end D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
