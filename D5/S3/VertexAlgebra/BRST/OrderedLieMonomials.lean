/- GID: D5/S3/VertexAlgebra/BRST/OrderedLieMonomials
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OrderedLieMonomials
   mirror-E: none(waiver:elementary-ordered-spanning)
   anchors: []
   utility: none
   digest: Ordered spanning in each degree and the free associative algebra dimension bound. -/

import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Ordered products of Lie basis elements

The commutator expansion in §6.3 of the direct Monster presentation argument
(2026-11-24) gives spanning in each weight. A reversed adjacent pair is replaced
by the swapped pair and a finite basis expansion of its bracket.
-/

set_option autoImplicit false

open Module

namespace D5.S3.VertexAlgebra.OrderedLieMonomials

variable {K L A ι X : Type*}

/-- The total weight of a word, with the empty word of weight zero. -/
def wordWeight (d : ι → ℕ) (w : List ι) : ℕ :=
  (w.map d).sum

@[simp] private theorem wordWeight_nil (d : ι → ℕ) : wordWeight d [] = 0 := rfl

@[simp] private theorem wordWeight_cons (d : ι → ℕ) (i : ι) (w : List ι) :
    wordWeight d (i :: w) = d i + wordWeight d w := rfl

@[simp] private theorem wordWeight_append (d : ι → ℕ) (p q : List ι) :
    wordWeight d (p ++ q) = wordWeight d p + wordWeight d q := by
  simp [wordWeight, List.sum_append]

/-- Evaluate the word in an associative algebra, in list order. -/
def monomial [Monoid A] (v : ι → A) (w : List ι) : A :=
  (w.map v).prod

@[simp] private theorem monomial_nil [Monoid A] (v : ι → A) : monomial v [] = 1 := rfl

@[simp] private theorem monomial_cons [Monoid A] (v : ι → A) (i : ι) (w : List ι) :
    monomial v (i :: w) = v i * monomial v w := rfl

@[simp] private theorem monomial_append [Monoid A] (v : ι → A) (p q : List ι) :
    monomial v (p ++ q) = monomial v p * monomial v q := by
  simp [monomial, List.prod_append]

/-- Weakly increasing words of a specified total weight. -/
abbrev OrderedWords [LinearOrder ι] (d : ι → ℕ) (n : ℕ) :=
  {w : List ι // w.SortedLE ∧ wordWeight d w = n}

/-- The linear span of the ordered products of total weight `n`. -/
def orderedSpan (K : Type*) [CommRing K] [Ring A] [Algebra K A] [LinearOrder ι]
    (v : ι → A) (d : ι → ℕ) (n : ℕ) : Submodule K A :=
  Submodule.span K (Set.range fun w : OrderedWords d n => monomial v w.val)

private def inversions [LinearOrder ι] : List ι → ℕ
  | [] => 0
  | i :: w => (w.countP fun j => decide (j < i)) + inversions w

private theorem inversions_swap [LinearOrder ι] (p q : List ι) {i j : ι} (h : j < i) :
    inversions (p ++ j :: i :: q) < inversions (p ++ i :: j :: q) := by
  induction p with
  | nil =>
    simp only [List.nil_append, inversions, List.countP_cons, decide_eq_true_eq, h,
      not_lt.mpr h.le, ite_true, ite_false]
    omega
  | cons a p ih =>
    have perm : (p ++ j :: i :: q).Perm (p ++ i :: j :: q) :=
      (List.Perm.swap i j q).append_left p
    simp only [List.cons_append, inversions]
    rw [perm.countP_eq]
    omega

private theorem exists_adjacent_inversion [LinearOrder ι] (w : List ι) (h : ¬w.IsChain (· ≤ ·)) :
    ∃ (p q : List ι) (i j : ι), w = p ++ i :: j :: q ∧ j < i := by
  induction w with
  | nil => simp at h
  | cons i w ih =>
    cases w with
    | nil => simp at h
    | cons j q =>
      by_cases hij : i ≤ j
      · have ht : ¬ (j :: q).IsChain (· ≤ ·) := fun ht =>
          h (List.isChain_cons_cons.mpr ⟨hij, ht⟩)
        obtain ⟨p, r, a, b, hw, hab⟩ := ih ht
        exact ⟨i :: p, r, a, b, congrArg (List.cons i) hw, hab⟩
      · exact ⟨[], q, i, j, rfl, lt_of_not_ge hij⟩

section Basis

attribute [local instance 100] LieRing.ofAssociativeRing

variable [CommRing K] [LieRing L] [LieAlgebra K L] [Ring A] [Algebra K A]
  [LinearOrder ι]

omit [LinearOrder ι] in
private theorem linearMap_apply_mem_of_basis_support (b : Basis ι K L)
    (g : L →ₗ[K] A) (x : L) (S : Submodule K A)
    (h : ∀ i ∈ (b.repr x).support, g (b i) ∈ S) : g x ∈ S := by
  have hx : ∑ i ∈ (b.repr x).support, b.repr x i • b i = x :=
    b.linearCombination_repr x
  rw [← hx, map_sum]
  exact Submodule.sum_mem S fun i hi => by
    rw [map_smul]
    exact S.smul_mem _ (h i hi)

/-- The bracket coefficients are supported in the sum of the two basis weights. -/
def BracketHomogeneous (b : Basis ι K L) (d : ι → ℕ) : Prop :=
  ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → d k = d i + d j

/-- A basis product lies in the span of the ordered products of its own total weight.
The proof sorts actual products by adjacent swaps, with shorter bracket terms. -/
theorem monomial_mem_orderedSpan (b : Basis ι K L) (f : L →ₗ⁅K⁆ A) (d : ι → ℕ)
    (hbr : BracketHomogeneous b d) (w : List ι) :
    monomial (fun i => f (b i)) w ∈
      orderedSpan K (fun i => f (b i)) d (wordWeight d w) := by
  classical
  let v : ι → A := fun i => f (b i)
  suffices aux : ∀ (length : ℕ) (w : List ι), w.length = length →
      monomial v w ∈ orderedSpan K v d (wordWeight d w) from aux w.length w rfl
  intro length
  induction length using Nat.strong_induction_on with
  | h length shorter =>
    suffices aux : ∀ (count : ℕ) (w : List ι), w.length = length → inversions w = count →
        monomial v w ∈ orderedSpan K v d (wordWeight d w) by
      exact fun w hw => aux (inversions w) w hw rfl
    intro count
    induction count using Nat.strong_induction_on with
    | h count fewer =>
      intro w hlen hcount
      by_cases hsorted : w.SortedLE
      · exact Submodule.subset_span ⟨⟨w, hsorted, rfl⟩, rfl⟩
      obtain ⟨p, q, i, j, rfl, hij⟩ := exists_adjacent_inversion w
        (fun h => hsorted (List.sortedLE_iff_isChain.mpr h))
      let S := orderedSpan K v d (wordWeight d (p ++ i :: j :: q))
      have hswapLen : (p ++ j :: i :: q).length = length := by
        simpa using hlen
      have hswapInv : inversions (p ++ j :: i :: q) < count :=
        hcount ▸ inversions_swap p q hij
      have hswapWeight : wordWeight d (p ++ j :: i :: q) =
          wordWeight d (p ++ i :: j :: q) := by
        simp [add_left_comm (d j) (d i)]
      have hswap : monomial v (p ++ j :: i :: q) ∈ S := by
        change _ ∈ orderedSpan K v d (wordWeight d (p ++ i :: j :: q))
        rw [← hswapWeight]
        exact fewer _ hswapInv _ hswapLen rfl
      let g : L →ₗ[K] A :=
        (LinearMap.mulLeft K (monomial v p)).comp
          ((LinearMap.mulRight K (monomial v q)).comp f.toLinearMap)
      have hcomm : g ⁅b i, b j⁆ ∈ S := by
        apply linearMap_apply_mem_of_basis_support b g _ S
        intro k hk
        have hkWeight := hbr i j k (Finsupp.mem_support_iff.mp hk)
        have hkLen : (p ++ k :: q).length < length := by
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        have hlower := shorter _ hkLen (p ++ k :: q) rfl
        have hweight : wordWeight d (p ++ k :: q) = wordWeight d (p ++ i :: j :: q) := by
          simp [hkWeight, add_assoc]
        have hmem : monomial v (p ++ k :: q) ∈ S := by
          change _ ∈ orderedSpan K v d (wordWeight d (p ++ i :: j :: q))
          rw [← hweight]
          exact hlower
        change monomial v p * (v k * monomial v q) ∈ S
        simpa only [monomial_append, monomial_cons] using hmem
      have hswapEq : v i * v j = v j * v i + f ⁅b i, b j⁆ := by
        rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
        change v i * v j = v j * v i + (v i * v j - v j * v i)
        abel
      have hdecomp : monomial v (p ++ i :: j :: q) =
          monomial v (p ++ j :: i :: q) + g ⁅b i, b j⁆ := by
        change monomial v (p ++ i :: j :: q) =
          monomial v (p ++ j :: i :: q) + monomial v p * (f ⁅b i, b j⁆ * monomial v q)
        simp only [monomial_append, monomial_cons]
        calc
          monomial v p * (v i * (v j * monomial v q)) =
              monomial v p * ((v j * v i + f ⁅b i, b j⁆) * monomial v q) := by
                rw [← mul_assoc (v i), hswapEq]
          _ = _ := by rw [add_mul, mul_add, mul_assoc (v j)]
      rw [hdecomp]
      exact S.add_mem hswap hcomm

/-- The unweighted spanning statement is the grading in which every basis vector has weight zero. -/
theorem monomial_mem_span_ordered (b : Basis ι K L) (f : L →ₗ⁅K⁆ A) (w : List ι) :
    monomial (fun i => f (b i)) w ∈
      Submodule.span K ((fun u => monomial (fun i => f (b i)) u) ''
        {u : List ι | u.SortedLE}) := by
  apply Submodule.span_mono _ (monomial_mem_orderedSpan b f (fun _ => 0) (by simp [BracketHomogeneous]) w)
  rintro _ ⟨u, rfl⟩
  exact ⟨u.val, u.property.1, rfl⟩

/-- Products of homogeneous Lie elements are spanned by ordered basis products of the same weight.
The hypothesis on `v` records its basis support in weight `e`. -/
theorem homogeneous_monomial_mem_orderedSpan (b : Basis ι K L) (f : L →ₗ⁅K⁆ A)
    (d : ι → ℕ) (hbr : BracketHomogeneous b d) (v : X → L) (e : X → ℕ)
    (hv : ∀ x i, b.repr (v x) i ≠ 0 → d i = e x) (w : List X) :
    monomial (fun x => f (v x)) w ∈
      orderedSpan K (fun i => f (b i)) d (wordWeight e w) := by
  let u : ι → A := fun i => f (b i)
  suffices aux : ∀ (w : List X) (p : List ι),
      monomial u p * monomial (fun x => f (v x)) w ∈
        orderedSpan K u d (wordWeight d p + wordWeight e w) by
    simpa using aux w []
  intro w
  induction w with
  | nil =>
    intro p
    simpa using monomial_mem_orderedSpan b f d hbr p
  | cons x w ih =>
    intro p
    let g : L →ₗ[K] A :=
      (LinearMap.mulLeft K (monomial u p)).comp
        ((LinearMap.mulRight K (monomial (fun x => f (v x)) w)).comp f.toLinearMap)
    change g (v x) ∈ _
    apply linearMap_apply_mem_of_basis_support b g
    intro i hi
    have hdi := hv x i (Finsupp.mem_support_iff.mp hi)
    simpa [g, hdi, add_assoc, mul_assoc, u] using ih (p ++ [i])

end Basis

section FreeAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable [Field K] [LinearOrder ι]

/-- The degree-`n` space of the free associative algebra on weighted generators. -/
def freeAlgebraWeightSpace (K : Type*) [Field K] (e : X → ℕ) (n : ℕ) :
    Submodule K (FreeAlgebra K X) :=
  Submodule.span K (Set.range fun w : {w : FreeMonoid X // wordWeight e w.toList = n} =>
    FreeAlgebra.basisFreeMonoid K X w.val)

private theorem freeAlgebra_basis_word (w : List X) :
    FreeAlgebra.basisFreeMonoid K X (FreeMonoid.ofList w) = monomial (FreeAlgebra.ι K) w := by
  let E : FreeAlgebra K X ≃ₐ[K] MonoidAlgebra K (FreeMonoid X) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
  change E.symm (MonoidAlgebra.of K (FreeMonoid X) (FreeMonoid.ofList w)) = _
  induction w with
  | nil => exact (E.symm.toAlgHom.toMonoidHom.comp (MonoidAlgebra.of K (FreeMonoid X))).map_one
  | cons x w ih =>
    rw [FreeMonoid.ofList_cons, map_mul, map_mul, ih, monomial_cons]
    congr 1
    have hx : E (FreeAlgebra.ι K x) = MonoidAlgebra.of K (FreeMonoid X) (FreeMonoid.of x) :=
      FreeAlgebra.lift_ι_apply _ _
    rw [← hx, E.symm_apply_apply]

/-- The weight space of the free associative algebra is contained in the span
of ordered products from a homogeneous basis of the free Lie algebra. -/
theorem freeAlgebraWeightSpace_le_orderedSpan
    (b : Basis ι K (FreeLieAlgebra K X)) (d : ι → ℕ) (hbr : BracketHomogeneous b d)
    (e : X → ℕ) (he : ∀ x i, b.repr (FreeLieAlgebra.of K x) i ≠ 0 → d i = e x)
    (n : ℕ) :
    freeAlgebraWeightSpace K e n ≤ orderedSpan K
      (fun i => FreeLieAlgebra.lift K (FreeAlgebra.ι K) (b i)) d n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  change FreeAlgebra.basisFreeMonoid K X w ∈ _
  rw [← FreeMonoid.ofList_toList w, freeAlgebra_basis_word]
  have h := homogeneous_monomial_mem_orderedSpan b
    (FreeLieAlgebra.lift K (FreeAlgebra.ι K)) d hbr (FreeLieAlgebra.of K) e he w.toList
  rw [show (fun x => FreeLieAlgebra.lift K (FreeAlgebra.ι K) (FreeLieAlgebra.of K x)) =
      FreeAlgebra.ι K from funext (FreeLieAlgebra.lift_of_apply (FreeAlgebra.ι K)), hw] at h
  exact h

/-- The Hilbert coefficient of the free associative algebra is bounded by the
number of ordered basis words of the same weight. -/
theorem finrank_freeAlgebraWeightSpace_le_card_orderedWords
    (b : Basis ι K (FreeLieAlgebra K X)) (d : ι → ℕ) (hbr : BracketHomogeneous b d)
    (e : X → ℕ) (he : ∀ x i, b.repr (FreeLieAlgebra.of K x) i ≠ 0 → d i = e x)
    (n : ℕ) [Fintype (OrderedWords d n)] :
    finrank K (freeAlgebraWeightSpace K e n) ≤ Fintype.card (OrderedWords d n) := by
  let j : FreeLieAlgebra K X →ₗ⁅K⁆ FreeAlgebra K X :=
    FreeLieAlgebra.lift K (FreeAlgebra.ι K)
  let v : OrderedWords d n → FreeAlgebra K X := fun w => monomial (fun i => j (b i)) w.val
  let : Module.Finite K (Submodule.span K (Set.range v)) :=
    Module.Finite.span_of_finite K (Set.finite_range v)
  exact (Submodule.finrank_mono
    (show freeAlgebraWeightSpace K e n ≤ Submodule.span K (Set.range v) from
      freeAlgebraWeightSpace_le_orderedSpan b d hbr e he n)).trans
        (finrank_range_le_card v)

end FreeAlgebra

section EulerProduct

private abbrev WeightCutoff (d : ι → ℕ) (n : ℕ) := {i : ι // d i ≤ n}

private theorem weight_le_wordWeight (d : ι → ℕ) {i : ι} {w : List ι} (hi : i ∈ w) :
    d i ≤ wordWeight d w := by
  induction w with
  | nil => simp at hi
  | cons a w ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp
    · simpa only [wordWeight_cons] using (ih hi).trans (Nat.le_add_left _ _)

private theorem length_le_wordWeight (d : ι → ℕ) (hd : ∀ i, 0 < d i) (w : List ι) :
    w.length ≤ wordWeight d w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [List.length_cons, wordWeight_cons, Nat.add_comm] using Nat.add_le_add ih (hd i)

private theorem sum_weighted_counts [DecidableEq ι] (d : ι → ℕ) (n : ℕ)
    [Fintype (WeightCutoff d n)] (w : List ι) (hw : ∀ i ∈ w, d i ≤ n) :
    ∑ i : WeightCutoff d n, d i.val * w.count i.val = wordWeight d w := by
  classical
  induction w with
  | nil => simp
  | cons a w ih =>
    let a' : WeightCutoff d n := ⟨a, hw a List.mem_cons_self⟩
    have hcount (i : WeightCutoff d n) :
        (a :: w).count i.val = w.count i.val + if i = a' then 1 else 0 := by
      have hsub : a = i.val ↔ i = a' :=
        ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩
      simp only [List.count_cons, beq_iff_eq, hsub]
    simp_rw [hcount, Nat.mul_add, Finset.sum_add_distrib, mul_ite, Nat.mul_one, Nat.mul_zero]
    rw [ih (fun i hi => hw i (List.mem_cons_of_mem a hi))]
    simp [a', add_comm]

private abbrev WeightedMultiplicities (d : ι → ℕ) (n : ℕ) [Fintype (WeightCutoff d n)] :=
  {a : WeightCutoff d n → Fin (n + 1) // ∑ i, d i.val * (a i : ℕ) = n}

private noncomputable def orderedWordsEmbedding [LinearOrder ι] (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (n : ℕ) [Fintype (WeightCutoff d n)] :
    OrderedWords d n ↪ WeightedMultiplicities d n := by
  classical
  let cutoff (w : OrderedWords d n) (i : ι) (hi : i ∈ w.val) : d i ≤ n :=
    w.property.2 ▸ weight_le_wordWeight d hi
  let counts (w : OrderedWords d n) (i : WeightCutoff d n) : Fin (n + 1) :=
    ⟨w.val.count i.val, by
      apply Nat.lt_succ_of_le
      exact List.count_le_length.trans ((length_le_wordWeight d hd w.val).trans_eq w.property.2)⟩
  refine ⟨fun w => ⟨counts w, (sum_weighted_counts d n w.val (cutoff w)).trans w.property.2⟩, ?_⟩
  intro w u heq
  apply Subtype.ext
  apply List.Perm.eq_of_sortedLE w.property.1 u.property.1
  apply List.perm_iff_count.mpr
  intro i
  by_cases hi : d i ≤ n
  · exact congrArg (fun a : WeightedMultiplicities d n => (a.val ⟨i, hi⟩ : ℕ)) heq
  · have absent (v : OrderedWords d n) : i ∉ v.val := fun h => hi (cutoff v i h)
    rw [List.count_eq_zero.mpr (absent w), List.count_eq_zero.mpr (absent u)]

/-- The Euler product through degree `n`, with the geometric sum for each
positive weight cut off after the `n`-th power. For a positive grading
`a 0 = 0`, so the weight-zero factor contributes `1`. -/
noncomputable def truncatedEulerProduct (a : ℕ → ℕ) (n : ℕ) : Polynomial ℕ :=
  ∏ m : Fin (n + 1), (∑ k : Fin (n + 1), (Polynomial.X : Polynomial ℕ) ^ (m.val * k.val)) ^ a m.val

private theorem coeff_truncatedEulerProduct (d : ι → ℕ) (n : ℕ) [Fintype (WeightCutoff d n)] :
    (truncatedEulerProduct (fun m => Nat.card {i : ι // d i = m}) n).coeff n =
      Nat.card (WeightedMultiplicities d n) := by
  classical
  let deg (i : WeightCutoff d n) : Fin (n + 1) := ⟨d i.val, Nat.lt_succ_of_le i.property⟩
  let factor (m : Fin (n + 1)) : Polynomial ℕ :=
    ∑ k : Fin (n + 1), (Polynomial.X : Polynomial ℕ) ^ (m.val * k.val)
  have hcard (m : Fin (n + 1)) :
      Fintype.card {i : WeightCutoff d n // deg i = m} = Nat.card {i : ι // d i = m.val} := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact
      { toFun := fun i => ⟨i.val.val, congrArg Fin.val i.property⟩
        invFun := fun i => ⟨⟨i.val, i.property.le.trans (Nat.le_of_lt_succ m.isLt)⟩,
          Fin.ext i.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hprod : truncatedEulerProduct (fun m => Nat.card {i : ι // d i = m}) n =
      ∏ i : WeightCutoff d n, factor (deg i) := by
    rw [← Fintype.prod_fiberwise' deg factor]
    simp only [Finset.prod_const, Finset.card_univ, hcard]
    rfl
  rw [hprod]
  change (∏ i : WeightCutoff d n,
    ∑ k : Fin (n + 1), (Polynomial.X : Polynomial ℕ) ^ (d i.val * k.val)).coeff n = _
  rw [Fintype.prod_sum]
  simp only [Finset.prod_pow_eq_pow_sum, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]

end EulerProduct

section HilbertBound

variable [Field K] [LinearOrder ι]

/-- The weight space spanned by the basis vectors of the indicated degree. -/
def basisWeightSpace {L : Type*} [AddCommGroup L] [Module K L] (b : Basis ι K L)
    (d : ι → ℕ) (n : ℕ) : Submodule K L :=
  Submodule.span K (Set.range fun i : {i : ι // d i = n} => b i.val)

omit [LinearOrder ι] in
private theorem finrank_basisWeightSpace {L : Type*} [AddCommGroup L] [Module K L]
    (b : Basis ι K L) (d : ι → ℕ) (n : ℕ) [Finite {i : ι // d i = n}] :
    finrank K (basisWeightSpace b d n) = Nat.card {i : ι // d i = n} := by
  let := Fintype.ofFinite {i : ι // d i = n}
  rw [Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (b.linearIndependent.comp Subtype.val Subtype.val_injective)

/-- The degree-`n` Hilbert coefficient for the free associative algebra is at most
the degree-`n` coefficient of the finite Euler product with the dimensions of the
Lie weight spaces as exponents. The finite cutoff suffices at degree `n` since
all basis weights are positive. -/
theorem finrank_freeAlgebraWeightSpace_le_eulerCoeff
    (b : Basis ι K (FreeLieAlgebra K X)) (d : ι → ℕ) (hbr : BracketHomogeneous b d)
    (e : X → ℕ) (he : ∀ x i, b.repr (FreeLieAlgebra.of K x) i ≠ 0 → d i = e x)
    (hd : ∀ i, 0 < d i) (n : ℕ) [Finite {i : ι // d i ≤ n}] :
    finrank K (freeAlgebraWeightSpace K e n) ≤
      (truncatedEulerProduct (fun m => finrank K (basisWeightSpace b d m)) n).coeff n := by
  classical
  let : Fintype (WeightCutoff d n) := Fintype.ofFinite _
  let inject := orderedWordsEmbedding d hd n
  let : Finite (OrderedWords d n) := Finite.of_injective inject inject.injective
  let := Fintype.ofFinite (OrderedWords d n)
  have hprod : truncatedEulerProduct (fun m => finrank K (basisWeightSpace b d m)) n =
      truncatedEulerProduct (fun m => Nat.card {i : ι // d i = m}) n := by
    unfold truncatedEulerProduct
    refine Finset.prod_congr rfl ?_
    intro m _
    let into (i : {i : ι // d i = m.val}) : WeightCutoff d n :=
      ⟨i.val, i.property.le.trans (Nat.le_of_lt_succ m.isLt)⟩
    let : Finite {i : ι // d i = m.val} :=
      Finite.of_injective into (fun _ _ h => Subtype.ext
        (congrArg (fun x : WeightCutoff d n => x.val) h))
    dsimp only
    rw [finrank_basisWeightSpace]
  rw [hprod, coeff_truncatedEulerProduct]
  refine (finrank_freeAlgebraWeightSpace_le_card_orderedWords b d hbr e he n).trans ?_
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective inject inject.injective

end HilbertBound

end D5.S3.VertexAlgebra.OrderedLieMonomials
