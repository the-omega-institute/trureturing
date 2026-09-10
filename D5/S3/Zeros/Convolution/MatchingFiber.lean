/- GID: D5/S3/Zeros/Convolution/MatchingFiber
   generality: I
   mirror-B: D5/B/S3/Zeros/Convolution/MatchingFiber
   mirror-E: none(waiver:symbolic-matching-identity)
   anchors: []
   utility: none
   digest: All-degree matching sums and symmetrization coefficient normalization. -/

import D5.S3.Zeros.Convolution.FiniteConvolutionCoefficients
import D5.S3.Zeros.Convolution.PerfectMatchingCount
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
`Matching` and its finite instance describe arbitrary finite index matchings.
`edgeSquare`, `matchingSum`, and `rootPolynomial` are symbolic algebraic definitions.
`MatchingIdentity` records the unproved all-degree target as a proposition.
`coeff_reflection` and `symmetrize_coefficient` normalize the existing definitions.
None is a bounded enumeration, checker, numerical reduction, or certified instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.MatchingFiber

open Polynomial
open scoped BigOperators
open D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeFour
open D5.S3.Zeros.Convolution.FiniteConvolutionCoefficients

/-- Unordered, loop-free, vertex-disjoint edges on root indices. -/
def Matching (n k : ℕ) :=
  { M : Finset (Sym2 (Fin n)) // M.card = k ∧
    (∀ e ∈ M, ¬ e.IsDiag) ∧
    (M : Set (Sym2 (Fin n))).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) }

noncomputable instance (n k : ℕ) : Fintype (Matching n k) := by
  classical
  unfold Matching
  exact Fintype.ofFinite _

/-- Symmetry makes this a well-defined square on unordered pairs. -/
def edgeSquare {n : ℕ} {R : Type*} [CommRing R] (r : Fin n → R) : Sym2 (Fin n) → R :=
  Sym2.lift ⟨fun i j => (r i - r j) ^ 2, by intro i j; ring⟩

def matchingSum {n : ℕ} {R : Type*} [CommRing R] (r : Fin n → R) (k : ℕ) : R :=
  ∑ M : Matching n k, ∏ e ∈ M.val, edgeSquare r e

def rootPolynomial {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (X - C (r i))

/-- The full target, recorded as a proposition and not asserted as a theorem. -/
def MatchingIdentity : Prop := ∀ (n k : ℕ), 2 * k ≤ n → ∀ (r : Fin n → ℝ),
  (-1 : ℝ) ^ k * (symmetrize n (rootPolynomial r)).coeff (n - 2 * k) =
    matchingSum r k / (n.descFactorial k : ℝ)

/-- Reflection multiplies the descending coefficient by its alternating sign. -/
theorem coeff_reflection (n j : ℕ) (hj : j ≤ n) (p : ℝ[X]) :
    (dilate n (-1) p).coeff (n - j) = (-1 : ℝ) ^ j * p.coeff (n - j) := by
  simp only [dilate, coeff_C_mul, comp_C_mul_X_coeff, inv_neg, inv_one]
  have hn : (-1 : ℝ) ^ n = (-1) ^ j * (-1) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hs : (-1 : ℝ) ^ (n - j) * (-1) ^ (n - j) = 1 := by rw [← mul_pow]; norm_num
  rw [hn]
  calc
    _ = (-1 : ℝ) ^ j * p.coeff (n - j) * ((-1) ^ (n - j) * (-1) ^ (n - j)) := by ring
    _ = _ := by rw [hs, mul_one]

/-- Corrected step (1), derived from the frozen definition at arbitrary degree. -/
theorem symmetrize_coefficient (n k : ℕ) (hk : 2 * k ≤ n) (p : ℝ[X]) :
    (-1 : ℝ) ^ k * (symmetrize n p).coeff (n - 2 * k) =
      (-1 : ℝ) ^ k * (n.descFactorial (2 * k) : ℝ) *
        ∑ i ∈ Finset.range (2 * k + 1),
          (-1 : ℝ) ^ i * elementaryCoeff n p i * elementaryCoeff n p (2 * k - i) /
            ((n.descFactorial i : ℝ) * (n.descFactorial (2 * k - i) : ℝ)) := by
  rw [symmetrize, coeff_additiveConvolution n p _ (2 * k) hk, mul_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_reflection n (2 * k - i) (by omega)]
  unfold elementaryCoeff
  have hs : (-1 : ℝ) ^ i * (-1) ^ i = 1 := by rw [← mul_pow]; norm_num
  congr 1
  calc
    _ = ((-1 : ℝ) ^ i * (-1) ^ i) *
        (p.coeff (n - i) * ((-1) ^ (2 * k - i) * p.coeff (n - (2 * k - i)))) := by
          rw [hs, one_mul]
    _ = _ := by ring

#print axioms coeff_reflection
#print axioms symmetrize_coefficient

/-- The exponent vector of a squarefree monomial on a set of indices. -/
def squarefreeExponent {n : ℕ} (A : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ x ∈ A, Finsupp.single x 1

/-- Indices in S occur twice; indices in T occur once. -/
def fiberExponent {n : ℕ} (S T : Finset (Fin n)) : Fin n →₀ ℕ :=
  squarefreeExponent S + squarefreeExponent S + squarefreeExponent T

private theorem squarefreeExponent_apply {n : ℕ} (A : Finset (Fin n)) (x : Fin n) :
    squarefreeExponent A x = if x ∈ A then 1 else 0 := by
  classical
  simp [squarefreeExponent, Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem fiber_pair_decomposition {n : ℕ} (S T A B : Finset (Fin n))
    (hST : Disjoint S T)
    (h : squarefreeExponent A + squarefreeExponent B = fiberExponent S T) :
    A = S ∪ (A ∩ T) ∧ B = S ∪ (T \ (A ∩ T)) := by
  have hx (x : Fin n) := congrArg (fun d : Fin n →₀ ℕ => d x) h
  simp only [fiberExponent, Finsupp.add_apply, squarefreeExponent_apply] at hx
  constructor <;> ext x
  all_goals
    have hp := hx x
    have hd : ¬ (x ∈ S ∧ x ∈ T) := fun h => Finset.disjoint_left.mp hST h.1 h.2
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
      by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp_all

private theorem split_pair_exponent {n : ℕ} (S T U : Finset (Fin n))
    (hST : Disjoint S T) (hUT : U ⊆ T) :
    squarefreeExponent (S ∪ U) + squarefreeExponent (S ∪ (T \ U)) =
      fiberExponent S T := by
  ext x
  have hd : ¬ (x ∈ S ∧ x ∈ T) := fun h => Finset.disjoint_left.mp hST h.1 h.2
  have hu : x ∈ U → x ∈ T := fun h => hUT h
  simp only [fiberExponent, Finsupp.add_apply, squarefreeExponent_apply]
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> by_cases hx : x ∈ U <;> simp_all

private theorem split_pair_inter {n : ℕ} (S T U : Finset (Fin n))
    (hST : Disjoint S T) (hUT : U ⊆ T) : (S ∪ U) ∩ T = U := by
  ext x
  have hd : x ∈ S → x ∉ T := fun h => Finset.disjoint_left.mp hST h
  have hu : x ∈ U → x ∈ T := fun h => hUT h
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

private theorem fiber_pair_cards {n : ℕ} (S T A B : Finset (Fin n))
    (hST : Disjoint S T)
    (h : squarefreeExponent A + squarefreeExponent B = fiberExponent S T) :
    A.card = S.card + (A ∩ T).card ∧
      B.card = S.card + (T.card - (A ∩ T).card) := by
  obtain ⟨hA, hB⟩ := fiber_pair_decomposition S T A B hST h
  constructor
  · conv_lhs => rw [hA]
    exact Finset.card_union_of_disjoint (hST.mono_right Finset.inter_subset_right)
  · rw [hB, Finset.card_union_of_disjoint (hST.mono_right Finset.sdiff_subset),
      Finset.card_sdiff_of_subset Finset.inter_subset_right]

/-- Ordered subset pairs contributing to a prescribed exponent vector. -/
def elementaryFiber (n i j : ℕ) (d : Fin n →₀ ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (Finset.univ.powersetCard i ×ˢ Finset.univ.powersetCard j).filter
    (fun p => squarefreeExponent p.1 + squarefreeExponent p.2 = d)

private theorem mem_elementaryFiber {n i j : ℕ} {d : Fin n →₀ ℕ}
    {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ elementaryFiber n i j d ↔
      (p.1.card = i ∧ p.2.card = j) ∧
        squarefreeExponent p.1 + squarefreeExponent p.2 = d := by
  simp [elementaryFiber, Finset.mem_powersetCard]

/-- The squarefree monomial formula identifies coefficients with subset-pair fibers. -/
theorem coeff_esymm_mul_eq_card (n i j : ℕ) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d
      (MvPolynomial.esymm (Fin n) ℚ i * MvPolynomial.esymm (Fin n) ℚ j) =
        ((elementaryFiber n i j d).card : ℚ) := by
  classical
  rw [MvPolynomial.esymm_eq_sum_monomial, MvPolynomial.esymm_eq_sum_monomial,
    Finset.sum_mul_sum, ← Finset.sum_product']
  simp only [MvPolynomial.coeff_sum, MvPolynomial.monomial_mul, one_mul,
    MvPolynomial.coeff_monomial]
  exact Finset.sum_boole _ _

/-- A fiber is freely chosen by the subset of singly occurring indices in A. -/
theorem card_elementaryFiber (n : ℕ) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (ell : ℕ) (hell : ell ≤ T.card) :
    (elementaryFiber n (S.card + ell) (S.card + (T.card - ell))
      (fiberExponent S T)).card = T.card.choose ell := by
  classical
  rw [← Finset.card_powersetCard]
  symm
  apply Finset.card_bij (fun U _ => (S ∪ U, S ∪ (T \ U)))
  · intro U hU
    obtain ⟨hUT, hcard⟩ := Finset.mem_powersetCard.mp hU
    apply mem_elementaryFiber.mpr
    refine ⟨⟨?_, ?_⟩, split_pair_exponent S T U hST hUT⟩
    · rw [Finset.card_union_of_disjoint (hST.mono_right hUT), hcard]
    · rw [Finset.card_union_of_disjoint (hST.mono_right Finset.sdiff_subset),
        Finset.card_sdiff_of_subset hUT, hcard]
  · intro U hU V hV heq
    have h := congrArg (fun p : Finset (Fin n) × Finset (Fin n) => p.1 ∩ T) heq
    simpa only [split_pair_inter S T U hST (Finset.mem_powersetCard.mp hU).1,
      split_pair_inter S T V hST (Finset.mem_powersetCard.mp hV).1] using h
  · intro p hp
    obtain ⟨⟨hA, hB⟩, heq⟩ := mem_elementaryFiber.mp hp
    have hcards := fiber_pair_cards S T p.1 p.2 hST heq
    obtain ⟨hleft, hright⟩ := fiber_pair_decomposition S T p.1 p.2 hST heq
    refine ⟨p.1 ∩ T, Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, ?_⟩,
      Prod.ext hleft.symm hright.symm⟩
    omega

/-- Complete coefficient formula, including impossible degree and index cases. -/
theorem coeff_esymm_mul_fiber (n i j : ℕ) (S T : Finset (Fin n))
    (hST : Disjoint S T) :
    MvPolynomial.coeff (fiberExponent S T)
      (MvPolynomial.esymm (Fin n) ℚ i * MvPolynomial.esymm (Fin n) ℚ j) =
      if S.card ≤ i ∧ S.card ≤ j ∧ i + j = 2 * S.card + T.card
      then (T.card.choose (i - S.card) : ℚ) else 0 := by
  classical
  rw [coeff_esymm_mul_eq_card]
  split_ifs with h
  · have he : i - S.card ≤ T.card := by omega
    have hi : i = S.card + (i - S.card) := by omega
    have hj : j = S.card + (T.card - (i - S.card)) := by omega
    conv_lhs => rw [hi, hj]
    rw [card_elementaryFiber n S T hST _ he]
  · have hempty : elementaryFiber n i j (fiberExponent S T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨⟨hA, hB⟩, heq⟩ := mem_elementaryFiber.mp hp
      have hcards := fiber_pair_cards S T p.1 p.2 hST heq
      have hle := Finset.card_le_card (Finset.inter_subset_right (s₁ := p.1) (s₂ := T))
      exact h (by omega)
    rw [hempty, Finset.card_empty, Nat.cast_zero]

#print axioms coeff_esymm_mul_eq_card
#print axioms card_elementaryFiber
#print axioms coeff_esymm_mul_fiber

/-- None selects the cross term; a vertex selects its square term. -/
abbrev EdgeChoice {n : ℕ} (e : Sym2 (Fin n)) := Option {x : Fin n // x ∈ e.toFinset}

def edgeChoiceExponent {n : ℕ} (e : Sym2 (Fin n)) : EdgeChoice e → Fin n →₀ ℕ
  | none => squarefreeExponent e.toFinset
  | some x => Finsupp.single x.val 2

def edgeChoiceWeight {n : ℕ} (e : Sym2 (Fin n)) : EdgeChoice e → ℚ
  | none => -2
  | some _ => 1

/-- The local expansion has just three terms, independently of matching size. -/
theorem edgeSquare_eq_choice_sum {n : ℕ} (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    edgeSquare (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ) e =
      ∑ c : EdgeChoice e,
        MvPolynomial.monomial (edgeChoiceExponent e c) (edgeChoiceWeight e c) := by
  classical
  change _ = ∑ c : Option {x : Fin n // x ∈ e.toFinset}, _
  rw [Fintype.sum_option]
  simp only [edgeChoiceExponent, edgeChoiceWeight]
  change _ = MvPolynomial.monomial (squarefreeExponent e.toFinset) (-2) +
    ∑ x : e.toFinset, MvPolynomial.monomial (Finsupp.single (x : Fin n) 2) (1 : ℚ)
  rw [Finset.sum_coe_sort e.toFinset
    (fun x : Fin n => MvPolynomial.monomial (Finsupp.single x 2) (1 : ℚ))]
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := by simpa using he
    simp only [edgeSquare, Sym2.lift_mk, Sym2.toFinset_mk_eq, squarefreeExponent,
      Finset.sum_pair hxy]
    rw [← MvPolynomial.X_pow_eq_monomial, ← MvPolynomial.X_pow_eq_monomial]
    have hm : (MvPolynomial.monomial (Finsupp.single x 1 + Finsupp.single y 1) (-2) :
        MvPolynomial (Fin n) ℚ) = -2 * MvPolynomial.X x * MvPolynomial.X y := by
      rw [show (-2 : MvPolynomial (Fin n) ℚ) = MvPolynomial.C (-2) by
        rw [map_neg, map_ofNat]]
      simp only [MvPolynomial.X, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul]
      norm_num
    rw [hm]
    ring

/-- One local monomial choice on each edge of a matching. -/
abbrev MatchingDecoration {n k : ℕ} (M : Matching n k) := ∀ e : M.val, EdgeChoice e.val

def decorationExponent {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M) : Fin n →₀ ℕ :=
  ∑ e : M.val, edgeChoiceExponent e.val (c e)

def decorationWeight {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M) : ℚ :=
  ∏ e : M.val, edgeChoiceWeight e.val (c e)

/-- Mathlib's inductive distributivity theorem expands the finite product symbolically. -/
theorem matching_product_eq_decoration_sum {n k : ℕ} (M : Matching n k) :
    (∏ e ∈ M.val, edgeSquare (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ) e) =
      ∑ c : MatchingDecoration M,
        MvPolynomial.monomial (decorationExponent M c) (decorationWeight M c) := by
  classical
  calc
    _ = ∏ e : M.val, edgeSquare (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ)
        e.val := (Finset.prod_coe_sort _ _).symm
    _ = ∏ e : M.val, ∑ c : EdgeChoice e.val,
        MvPolynomial.monomial (edgeChoiceExponent e.val c) (edgeChoiceWeight e.val c) := by
      apply Finset.prod_congr rfl
      intro e _
      exact edgeSquare_eq_choice_sum e.val (M.prop.2.1 e.val e.prop)
    _ = ∑ c : MatchingDecoration M, ∏ e : M.val,
        MvPolynomial.monomial (edgeChoiceExponent e.val (c e))
          (edgeChoiceWeight e.val (c e)) := Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact (MvPolynomial.monomial_sum_prod Finset.univ
        (fun e : M.val => edgeChoiceExponent e.val (c e))
        (fun e : M.val => edgeChoiceWeight e.val (c e))).symm

/-- The matching coefficient is the exact weighted sum over its monomial fiber. -/
theorem coeff_matchingSum_eq_decoration_fiber (n k : ℕ) (d : Fin n →₀ ℕ) :
    MvPolynomial.coeff d
      (matchingSum (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ) k) =
      ∑ M : Matching n k, ∑ c : MatchingDecoration M,
        if decorationExponent M c = d then decorationWeight M c else 0 := by
  classical
  simp only [matchingSum, matching_product_eq_decoration_sum, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]

#print axioms edgeSquare_eq_choice_sum
#print axioms matching_product_eq_decoration_sum
#print axioms coeff_matchingSum_eq_decoration_fiber

private theorem edgeChoiceExponent_zero_of_not_mem {n : ℕ} (e : Sym2 (Fin n))
    (c : EdgeChoice e) (x : Fin n) (hx : x ∉ e.toFinset) :
    edgeChoiceExponent e c x = 0 := by
  cases c with
  | none => simp [edgeChoiceExponent, squarefreeExponent_apply, hx]
  | some y =>
    have hy : y.val ≠ x := fun h => hx (h ▸ y.prop)
    simp [edgeChoiceExponent, hy]

/-- Disjoint edges make the global exponent local at each incident vertex. -/
theorem decorationExponent_apply_of_mem {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (e : M.val) (x : Fin n) (hx : x ∈ e.val.toFinset) :
    decorationExponent M c x = edgeChoiceExponent e.val (c e) x := by
  classical
  simp only [decorationExponent, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_single e
  · intro f _ hfe
    apply edgeChoiceExponent_zero_of_not_mem
    have hval : f.val ≠ e.val := fun h => hfe (Subtype.ext h)
    exact fun hf => Finset.disjoint_left.mp
      (M.prop.2.2 f.prop e.prop hval) hf hx
  · simp

private theorem exists_edge_of_decorationExponent_ne_zero {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (x : Fin n) (hx : decorationExponent M c x ≠ 0) :
    ∃ e : M.val, x ∈ e.val.toFinset := by
  classical
  by_contra h
  apply hx
  simp only [decorationExponent, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro e _
  exact edgeChoiceExponent_zero_of_not_mem e.val (c e) x (fun he => h ⟨e, he⟩)

private theorem fiberExponent_eq_two_iff {n : ℕ} (S T : Finset (Fin n))
    (hST : Disjoint S T) (x : Fin n) : fiberExponent S T x = 2 ↔ x ∈ S := by
  have hd : ¬ (x ∈ S ∧ x ∈ T) := fun h => Finset.disjoint_left.mp hST h.1 h.2
  simp only [fiberExponent, Finsupp.add_apply, squarefreeExponent_apply]
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp_all

/-- Edges on which the square, rather than cross, monomial was selected. -/
abbrev SquareChoices {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M) :=
  {e : M.val // (c e).isSome}

def chosenSquareVertex {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (q : SquareChoices M c) : Fin n := ((c q.val).get q.prop).val

private theorem chosenSquareVertex_mem {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (q : SquareChoices M c) :
    chosenSquareVertex M c q ∈ q.val.val.toFinset := ((c q.val).get q.prop).prop

private theorem chosenSquareVertex_exponent {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (q : SquareChoices M c) :
    decorationExponent M c (chosenSquareVertex M c q) = 2 := by
  rw [decorationExponent_apply_of_mem M c q.val _ (chosenSquareVertex_mem M c q)]
  unfold chosenSquareVertex
  have hs (o : EdgeChoice q.val.val) (ho : o.isSome) :
      edgeChoiceExponent q.val.val o (o.get ho).val = 2 := by
    cases o with
    | none => simp at ho
    | some x => simp [edgeChoiceExponent]
  exact hs (c q.val) q.prop

/-- Each squared variable determines exactly one square choice in its matching. -/
theorem chosenSquareVertex_injective {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) : Function.Injective (chosenSquareVertex M c) := by
  intro q r h
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  have hd := M.prop.2.2 q.val.prop r.val.prop hne
  exact Finset.disjoint_left.mp hd (chosenSquareVertex_mem M c q)
    (h ▸ chosenSquareVertex_mem M c r)

/-- The square choices in a prescribed fiber are in bijection with S. -/
theorem card_squareChoices_of_fiber {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) :
    Fintype.card (SquareChoices M c) = S.card := by
  classical
  let f : SquareChoices M c → S := fun q => ⟨chosenSquareVertex M c q,
    (fiberExponent_eq_two_iff S T hST _).mp
      (hc ▸ chosenSquareVertex_exponent M c q)⟩
  rw [← Fintype.card_coe S]
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro q r h
    exact chosenSquareVertex_injective M c (congrArg Subtype.val h)
  · intro x
    have hx : decorationExponent M c x.val = 2 := by
      rw [hc]
      exact (fiberExponent_eq_two_iff S T hST _).mpr x.prop
    obtain ⟨e, he⟩ := exists_edge_of_decorationExponent_ne_zero M c x.val (by omega)
    rw [decorationExponent_apply_of_mem M c e x.val he] at hx
    cases hce : c e with
    | none =>
      simp [hce, edgeChoiceExponent, squarefreeExponent_apply, he] at hx
    | some y =>
      have hy : y.val = x.val := by
        simpa [hce, edgeChoiceExponent, Finsupp.single_apply] using hx
      refine ⟨⟨e, by simp [hce]⟩, Subtype.ext ?_⟩
      change chosenSquareVertex M c _ = x.val
      simpa [chosenSquareVertex, hce] using hy

#print axioms decorationExponent_apply_of_mem
#print axioms chosenSquareVertex_injective
#print axioms card_squareChoices_of_fiber

/-- Only cross choices contribute a non-unit weight. -/
theorem decorationWeight_eq_pow {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) :
    decorationWeight M c = (-2 : ℚ) ^ (k - Fintype.card (SquareChoices M c)) := by
  classical
  have hw (e : M.val) : edgeChoiceWeight e.val (c e) =
      if (c e).isSome then 1 else -2 := by
    cases c e <;> rfl
  simp only [decorationWeight, hw, Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const]
  rw [← Fintype.card_subtype, Fintype.card_subtype_compl, Fintype.card_coe, M.prop.1]

/-- All decorated matchings in a fiber carry the same signed weight. -/
theorem decorationWeight_of_fiber {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) :
    decorationWeight M c = (-2 : ℚ) ^ (k - S.card) := by
  rw [decorationWeight_eq_pow, card_squareChoices_of_fiber M c S T hST hc]

/-- Decorated matchings whose selected monomials have the prescribed exponent. -/
abbrev MatchingMonomialFiber {n : ℕ} (k : ℕ) (S T : Finset (Fin n)) :=
  {p : (Σ M : Matching n k, MatchingDecoration M) //
    decorationExponent p.1 p.2 = fiberExponent S T}

/-- The remaining counting problem is an unweighted fiber cardinality. -/
theorem coeff_matchingSum_eq_card_fiber (n k : ℕ) (S T : Finset (Fin n))
    (hST : Disjoint S T) :
    MvPolynomial.coeff (fiberExponent S T)
      (matchingSum (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ) k) =
      (-2 : ℚ) ^ (k - S.card) * Fintype.card (MatchingMonomialFiber k S T) := by
  classical
  have hcard : (Fintype.card (MatchingMonomialFiber k S T) : ℚ) =
      ∑ M : Matching n k, ∑ c : MatchingDecoration M,
        if decorationExponent M c = fiberExponent S T then 1 else 0 := by
    rw [Fintype.card_subtype, ← Finset.sum_boole, Fintype.sum_sigma]
  rw [coeff_matchingSum_eq_decoration_fiber, hcard, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hc
  · simpa only [mul_one] using decorationWeight_of_fiber M c S T hST hc
  · simp

#print axioms decorationWeight_eq_pow
#print axioms decorationWeight_of_fiber
#print axioms coeff_matchingSum_eq_card_fiber

/-- The unused endpoint of a square choice. -/
def chosenSquarePartner {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (q : SquareChoices M c) : Fin n :=
  Sym2.Mem.other (Sym2.mem_toFinset.mp (chosenSquareVertex_mem M c q))

private theorem chosenSquarePartner_mem {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (q : SquareChoices M c) :
    chosenSquarePartner M c q ∈ q.val.val.toFinset :=
  Sym2.mem_toFinset.mpr (Sym2.other_mem _)

private theorem chosenSquarePartner_ne {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (q : SquareChoices M c) :
    chosenSquarePartner M c q ≠ chosenSquareVertex M c q :=
  Sym2.other_ne (M.prop.2.1 q.val.val q.val.prop) _

private theorem chosenSquarePartner_exponent {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (q : SquareChoices M c) :
    decorationExponent M c (chosenSquarePartner M c q) = 0 := by
  rw [decorationExponent_apply_of_mem M c q.val _ (chosenSquarePartner_mem M c q)]
  have hs (o : EdgeChoice q.val.val) (ho : o.isSome) (y : Fin n)
      (hy : y ≠ (o.get ho).val) : edgeChoiceExponent q.val.val o y = 0 := by
    cases o with
    | none => simp at ho
    | some x =>
      change y ≠ x.val at hy
      simp [edgeChoiceExponent, hy.symm]
  exact hs (c q.val) q.prop _ (chosenSquarePartner_ne M c q)

/-- Wasted partners are outside the monomial support. -/
theorem chosenSquarePartner_not_mem {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n))
    (hc : decorationExponent M c = fiberExponent S T) (q : SquareChoices M c) :
    chosenSquarePartner M c q ∉ S ∪ T := by
  have hz := chosenSquarePartner_exponent M c q
  rw [hc] at hz
  simp only [fiberExponent, Finsupp.add_apply, squarefreeExponent_apply] at hz
  by_cases hs : chosenSquarePartner M c q ∈ S <;>
    by_cases ht : chosenSquarePartner M c q ∈ T <;> simp_all

/-- Disjointness of the original matching makes all wasted partners distinct. -/
theorem chosenSquarePartner_injective {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) : Function.Injective (chosenSquarePartner M c) := by
  intro q r h
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  have hd := M.prop.2.2 q.val.prop r.val.prop hne
  exact Finset.disjoint_left.mp hd (chosenSquarePartner_mem M c q)
    (h ▸ chosenSquarePartner_mem M c r)

/-- Reuse the proved bijection to index square choices by their squared vertices. -/
def squareChoiceEquiv {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) : SquareChoices M c ≃ S := by
  classical
  let f : SquareChoices M c → S := fun q => ⟨chosenSquareVertex M c q,
    (fiberExponent_eq_two_iff S T hST _).mp
      (hc ▸ chosenSquareVertex_exponent M c q)⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨fun q r h => chosenSquareVertex_injective M c (congrArg Subtype.val h), ?_⟩
  rw [card_squareChoices_of_fiber M c S T hST hc, Fintype.card_coe]

/-- The square-edge leg of the proposed fiber decomposition. -/
def squarePartnerEmbedding {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) :
    S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n)) := by
  classical
  let g : SquareChoices M c ↪ ↥((S ∪ T)ᶜ : Finset (Fin n)) :=
    ⟨fun q => ⟨chosenSquarePartner M c q,
      Finset.mem_compl.mpr (chosenSquarePartner_not_mem M c S T hc q)⟩,
      fun q r h => chosenSquarePartner_injective M c (congrArg Subtype.val h)⟩
  exact (squareChoiceEquiv M c S T hST hc).symm.toEmbedding.trans g

/-- Mathlib counts ordered partner assignments as a descending factorial. -/
theorem card_partner_embeddings (n : ℕ) (S T : Finset (Fin n)) (hST : Disjoint S T) :
    Fintype.card (S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) =
      (n - S.card - T.card).descFactorial S.card := by
  classical
  rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Finset.card_union_of_disjoint hST, Fintype.card_fin]
  congr 1
  omega

#print axioms chosenSquarePartner_not_mem
#print axioms chosenSquarePartner_injective
#print axioms card_partner_embeddings
#print axioms squareChoiceEquiv
#print axioms squarePartnerEmbedding
#print axioms squarefreeExponent_apply
#print axioms fiber_pair_decomposition
#print axioms split_pair_exponent
#print axioms split_pair_inter
#print axioms fiber_pair_cards
#print axioms mem_elementaryFiber
#print axioms edgeChoiceExponent_zero_of_not_mem
#print axioms exists_edge_of_decorationExponent_ne_zero
#print axioms fiberExponent_eq_two_iff
#print axioms chosenSquareVertex_mem
#print axioms chosenSquareVertex_exponent
#print axioms chosenSquarePartner_mem
#print axioms chosenSquarePartner_ne
#print axioms chosenSquarePartner_exponent

private theorem fiberExponent_eq_one_iff {n : ℕ} (S T : Finset (Fin n))
    (hST : Disjoint S T) (x : Fin n) : fiberExponent S T x = 1 ↔ x ∈ T := by
  have hd : ¬ (x ∈ S ∧ x ∈ T) := fun h => Finset.disjoint_left.mp hST h.1 h.2
  simp only [fiberExponent, Finsupp.add_apply, squarefreeExponent_apply]
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp_all

/-- Two matching edges incident to the same vertex are identical. -/
theorem matching_edge_eq_of_mem {n k : ℕ} (M : Matching n k)
    {e f : Sym2 (Fin n)} (he : e ∈ M.val) (hf : f ∈ M.val)
    {x : Fin n} (hx : x ∈ e.toFinset) (hy : x ∈ f.toFinset) : e = f := by
  by_contra hne
  exact Finset.disjoint_left.mp (M.prop.2.2 he hf hne) hx hy

private theorem exists_cross_partner {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (t : T) :
    ∃ u : T, s(t.val, u.val) ∈ M.val := by
  have ht : decorationExponent M c t.val = 1 := by
    rw [hc]; exact (fiberExponent_eq_one_iff S T hST _).mpr t.prop
  obtain ⟨e, he⟩ := exists_edge_of_decorationExponent_ne_zero M c t.val (by omega)
  have hnone : c e = none := by
    have hl := decorationExponent_apply_of_mem M c e t.val he
    rw [ht] at hl
    cases hce : c e with
    | none => rfl
    | some x =>
      simp only [hce, edgeChoiceExponent, Finsupp.single_apply] at hl
      split_ifs at hl <;> omega
  let u := Sym2.Mem.other (Sym2.mem_toFinset.mp he)
  have hu : u ∈ e.val.toFinset := Sym2.mem_toFinset.mpr (Sym2.other_mem _)
  have hut : u ∈ T := by
    apply (fiberExponent_eq_one_iff S T hST u).mp
    rw [← hc, decorationExponent_apply_of_mem M c e u hu, hnone]
    simp [edgeChoiceExponent, squarefreeExponent_apply, hu]
  refine ⟨⟨u, hut⟩, ?_⟩
  rw [show s(t.val, u) = e.val from Sym2.other_spec _]
  exact e.prop

/-- The other endpoint of the cross edge incident to a linear variable. -/
def crossPartner {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (t : T) : T :=
  (exists_cross_partner M c S T hST hc t).choose

theorem crossPartner_mem {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (t : T) :
    s(t.val, (crossPartner M c S T hST hc t).val) ∈ M.val :=
  (exists_cross_partner M c S T hST hc t).choose_spec

/-- Incidence determines the cross partner uniquely. -/
theorem crossPartner_eq_iff {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (t u : T) :
    crossPartner M c S T hST hc t = u ↔ s(t.val, u.val) ∈ M.val := by
  constructor
  · intro h; rw [← h]; exact crossPartner_mem M c S T hST hc t
  · intro hu
    apply Subtype.ext
    apply Sym2.congr_right.mp
    exact matching_edge_eq_of_mem M (crossPartner_mem M c S T hST hc t) hu
      (x := t.val) (by simp) (by simp)

theorem crossPartner_involutive {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) :
    Function.Involutive (crossPartner M c S T hST hc) := by
  intro t
  apply (crossPartner_eq_iff M c S T hST hc _ _).mpr
  rw [Sym2.eq_swap]
  exact crossPartner_mem M c S T hST hc t

theorem crossPartner_ne {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (t : T) :
    crossPartner M c S T hST hc t ≠ t := by
  intro h
  have he := crossPartner_mem M c S T hST hc t
  rw [h] at he
  exact M.prop.2.1 _ he (by simp)

/-- The cross-edge factor extracted from a decorated matching fiber. -/
def crossPartnerInvolution {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) :
    PerfectMatchingCount.FixedPointFreeInvolution T :=
  ⟨(crossPartner_involutive M c S T hST hc).toPerm _,
    crossPartner_involutive M c S T hST hc, crossPartner_ne M c S T hST hc⟩

/-- Every extracted square partner is joined to its squared vertex. -/
theorem squarePartnerEmbedding_mem {n k : ℕ} (M : Matching n k)
    (c : MatchingDecoration M) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (s : S) :
    s(s.val, (squarePartnerEmbedding M c S T hST hc s).val) ∈ M.val := by
  let q := (squareChoiceEquiv M c S T hST hc).symm s
  have hv : chosenSquareVertex M c q = s.val :=
    congrArg Subtype.val ((squareChoiceEquiv M c S T hST hc).apply_symm_apply s)
  change s(s.val, chosenSquarePartner M c q) ∈ M.val
  rw [← hv, show s(chosenSquareVertex M c q, chosenSquarePartner M c q) =
    q.val.val from Sym2.other_spec _]
  exact q.val.prop

/-- The two extracted factors account for every edge of the original matching. -/
theorem matching_edge_cases {n k : ℕ} (M : Matching n k) (c : MatchingDecoration M)
    (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hc : decorationExponent M c = fiberExponent S T) (e : M.val) :
    (∃ s : S, e.val = s(s.val, (squarePartnerEmbedding M c S T hST hc s).val)) ∨
    (∃ t : T, e.val = s(t.val, (crossPartner M c S T hST hc t).val)) := by
  classical
  cases hce : c e with
  | some x =>
    let q : SquareChoices M c := ⟨e, by simp [hce]⟩
    refine Or.inl ⟨squareChoiceEquiv M c S T hST hc q, ?_⟩
    change e.val = s(chosenSquareVertex M c q,
      chosenSquarePartner M c ((squareChoiceEquiv M c S T hST hc).symm
        (squareChoiceEquiv M c S T hST hc q)))
    rw [Equiv.symm_apply_apply]
    exact (Sym2.other_spec _).symm
  | none =>
    obtain ⟨x, hx⟩ : ∃ x, x ∈ e.val.toFinset :=
      e.val.inductionOn fun x y => ⟨x, by simp⟩
    have ht : x ∈ T := by
      apply (fiberExponent_eq_one_iff S T hST x).mp
      rw [← hc, decorationExponent_apply_of_mem M c e x hx, hce]
      simp [edgeChoiceExponent, squarefreeExponent_apply, hx]
    refine Or.inr ⟨⟨x, ht⟩, ?_⟩
    exact matching_edge_eq_of_mem M e.prop (crossPartner_mem M c S T hST hc ⟨x, ht⟩)
      (x := x) hx (by simp)

/-- Distinct local choices cannot cancel because matching edges are disjoint. -/
theorem decorationExponent_injective {n k : ℕ} (M : Matching n k) :
    Function.Injective (decorationExponent M) := by
  intro c d h
  funext e
  have he (x : Fin n) (hx : x ∈ e.val.toFinset) :
      edgeChoiceExponent e.val (c e) x = edgeChoiceExponent e.val (d e) x := by
    rw [← decorationExponent_apply_of_mem M c e x hx,
      ← decorationExponent_apply_of_mem M d e x hx, h]
  cases hce : c e with
  | none =>
    cases hde : d e with
    | none => rfl
    | some y =>
      have hy := he y.val y.prop
      simp [hce, hde, edgeChoiceExponent, squarefreeExponent_apply, y.prop] at hy
  | some x =>
    cases hde : d e with
    | none =>
      have hx := he x.val x.prop
      simp [hce, hde, edgeChoiceExponent, squarefreeExponent_apply, x.prop] at hx
    | some y =>
      apply congrArg some
      apply Subtype.ext
      by_contra hne
      have hx := he x.val x.prop
      simp [hce, hde, edgeChoiceExponent, Finsupp.single_apply,
        Ne.symm hne] at hx

#print axioms matching_edge_eq_of_mem
#print axioms crossPartner_mem
#print axioms crossPartner_eq_iff
#print axioms crossPartner_involutive
#print axioms crossPartner_ne
#print axioms crossPartnerInvolution
#print axioms exists_cross_partner
#print axioms fiberExponent_eq_one_iff
#print axioms squarePartnerEmbedding_mem
#print axioms matching_edge_cases
#print axioms decorationExponent_injective

end D5.S3.Zeros.Convolution.MatchingFiber
