/- GID: D5/S3/Zeros/Convolution/MatchingPolynomial
   generality: I
   mirror-B: D5/B/S3/Zeros/Convolution/MatchingPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Assemble matching coefficients into the elementary-symmetric identity. -/

import D5.S3.Zeros.Convolution.MatchingEquiv
import D5.S3.Zeros.Convolution.AlternatingFactorialSum
import Mathlib.RingTheory.Polynomial.Vieta

/-!
All exponent and coefficient statements are symbolic at arbitrary degrees.
No bounded enumeration, checker, numerical reduction, or certified instance
is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.MatchingPolynomial

open MatchingFiber MatchingEquiv AlternatingFactorialSum MvPolynomial
open FiniteFreeCommutatorDegreeFour
open scoped BigOperators

variable {n k : ℕ}

private def GoodExponent (k : ℕ) (d : Fin n →₀ ℕ) : Prop :=
  (∀ x, d x ≤ 2) ∧ ∑ x, d x = 2 * k

private theorem squarefree_apply (A : Finset (Fin n)) (x : Fin n) :
    squarefreeExponent A x = if x ∈ A then 1 else 0 := by
  classical
  simp [squarefreeExponent, Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem sum_squarefree (A : Finset (Fin n)) :
    ∑ x, squarefreeExponent A x = A.card := by
  classical
  simp only [squarefreeExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

private theorem goodExponent_fiber (d : Fin n →₀ ℕ) (hd : GoodExponent k d) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S.card ≤ k ∧
      T.card = 2 * (k - S.card) ∧ d = fiberExponent S T := by
  classical
  let S := Finset.univ.filter fun x => d x = 2
  let T := Finset.univ.filter fun x => d x = 1
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hs ht
    have hs' : d x = 2 := (Finset.mem_filter.mp hs).2
    have ht' : d x = 1 := (Finset.mem_filter.mp ht).2
    omega
  have he : d = fiberExponent S T := by
    ext x
    have hx := hd.1 x
    simp only [fiberExponent, Finsupp.add_apply, squarefree_apply, S, T,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h2 : d x = 2 <;> by_cases h1 : d x = 1 <;> simp_all <;> omega
  have hs : 2 * S.card + T.card = 2 * k := by
    rw [← sum_squarefree S, ← sum_squarefree T]
    have hsum := hd.2
    rw [he] at hsum
    simpa only [fiberExponent, Finsupp.add_apply, Finset.sum_add_distrib,
      two_mul] using hsum
  exact ⟨S, T, hST, by omega, by omega, he⟩

private theorem edge_exponent_le_two (e : Sym2 (Fin n)) (c : EdgeChoice e)
    (x : Fin n) : edgeChoiceExponent e c x ≤ 2 := by
  classical
  cases c with
  | none => simp only [edgeChoiceExponent, squarefree_apply]; split_ifs <;> omega
  | some y => simp only [edgeChoiceExponent, Finsupp.single_apply]; split_ifs <;> omega

private theorem decoration_good (M : Matching n k) (c : MatchingDecoration M) :
    GoodExponent k (decorationExponent M c) := by
  classical
  constructor
  · intro x
    by_cases h : ∃ e : M.val, x ∈ e.val.toFinset
    · obtain ⟨e, he⟩ := h
      rw [decorationExponent_apply_of_mem M c e x he]
      exact edge_exponent_le_two e.val (c e) x
    · have hz : decorationExponent M c x = 0 := by
        simp only [decorationExponent, Finsupp.finsetSum_apply]
        apply Finset.sum_eq_zero
        intro e _
        have hx : x ∉ e.val.toFinset := fun hx => h ⟨e, hx⟩
        cases c e with
        | none => simp [edgeChoiceExponent, squarefree_apply, hx]
        | some y =>
          have hy : y.val ≠ x := fun hy => hx (hy ▸ y.prop)
          simp [edgeChoiceExponent, hy]
      omega
  · have he (e : M.val) : ∑ x, edgeChoiceExponent e.val (c e) x = 2 := by
      cases c e with
      | none =>
        rw [edgeChoiceExponent, sum_squarefree]
        exact Sym2.card_toFinset_of_not_isDiag e.val (M.prop.2.1 _ e.prop)
      | some y => simp [edgeChoiceExponent, Finsupp.single_apply]
    simp only [decorationExponent, Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_coe, M.prop.1,
      smul_eq_mul, Nat.mul_comm]

private theorem pair_good (A B : Finset (Fin n)) (hAB : A.card + B.card = 2 * k) :
    GoodExponent k (squarefreeExponent A + squarefreeExponent B) := by
  classical
  constructor
  · intro x
    simp only [Finsupp.add_apply, squarefree_apply]
    split_ifs <;> omega
  · simpa only [Finsupp.add_apply, Finset.sum_add_distrib, sum_squarefree] using hAB

private theorem coeff_matchingSum_zero (d : Fin n →₀ ℕ) (hd : ¬ GoodExponent k d) :
    coeff d (matchingSum (X : Fin n → MvPolynomial (Fin n) ℚ) k) = 0 := by
  classical
  rw [coeff_matchingSum_eq_decoration_fiber]
  apply Finset.sum_eq_zero
  intro M _
  apply Finset.sum_eq_zero
  intro c _
  apply if_neg
  intro he
  exact hd (he ▸ decoration_good M c)

private theorem coeff_esymm_mul_zero (i j : ℕ) (hij : i + j = 2 * k)
    (d : Fin n →₀ ℕ) (hd : ¬ GoodExponent k d) :
    coeff d (esymm (Fin n) ℚ i * esymm (Fin n) ℚ j) = 0 := by
  classical
  rw [coeff_esymm_mul_eq_card]
  have he : elementaryFiber n i j d = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp' : (p.1.card = i ∧ p.2.card = j) ∧
        squarefreeExponent p.1 + squarefreeExponent p.2 = d := by
      simpa [elementaryFiber, Finset.mem_powersetCard] using hp
    exact hd (hp'.2 ▸ pair_good p.1 p.2 (by rw [hp'.1.1, hp'.1.2, hij]))
  rw [he, Finset.card_empty, Nat.cast_zero]

/-- The numerator in the elementary-symmetric formula (star). -/
def matchingNumerator (n k : ℕ) : MvPolynomial (Fin n) ℚ :=
  ∑ i ∈ Finset.range (2 * k + 1),
    C ((-1 : ℚ) ^ (k + i) * ((n - i).factorial : ℚ) *
      ((n - 2 * k + i).factorial : ℚ)) *
        (esymm (Fin n) ℚ i * esymm (Fin n) ℚ (2 * k - i))

private theorem shifted_factorial_sum (n k a : ℕ) (hk : 2 * k ≤ n) (ha : a ≤ k) :
    (∑ i ∈ Finset.range (2 * k + 1),
      (-1 : ℚ) ^ (k + i) * ((n - i).factorial : ℚ) *
        ((n - 2 * k + i).factorial : ℚ) *
          (if a ≤ i ∧ a ≤ 2 * k - i then ((2 * (k - a)).choose (i - a) : ℚ) else 0)) =
      (-1 : ℚ) ^ (k - a) *
        (((2 * (k - a)).factorial : ℚ) / ((k - a).factorial : ℚ) *
          ((n - 2 * k + a).factorial : ℚ) * ((n - k).factorial : ℚ)) := by
  classical
  let f (i : ℕ) : ℚ := (-1 : ℚ) ^ (k + i) * ((n - i).factorial : ℚ) *
    ((n - 2 * k + i).factorial : ℚ) *
      (if a ≤ i ∧ a ≤ 2 * k - i then ((2 * (k - a)).choose (i - a) : ℚ) else 0)
  have hsub : (Finset.range (2 * (k - a) + 1)).image (fun ell => a + ell) ⊆
      Finset.range (2 * k + 1) := by
    intro i hi
    obtain ⟨ell, he, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_range] at he ⊢
    omega
  have hz (i : ℕ) (hi : i ∈ Finset.range (2 * k + 1))
      (hnot : i ∉ (Finset.range (2 * (k - a) + 1)).image (fun ell => a + ell)) :
      f i = 0 := by
    have hc : ¬ (a ≤ i ∧ a ≤ 2 * k - i) := by
      intro hc
      apply hnot
      refine Finset.mem_image.mpr ⟨i - a, ?_, by omega⟩
      simp only [Finset.mem_range] at hi ⊢
      omega
    simp only [f, if_neg hc, mul_zero]
  have hs : (∑ i ∈ Finset.range (2 * k + 1), f i) =
      ∑ ell ∈ Finset.range (2 * (k - a) + 1), f (a + ell) := by
    calc
      _ = ∑ i ∈ (Finset.range (2 * (k - a) + 1)).image (fun ell => a + ell), f i :=
        (Finset.sum_subset hsub hz).symm
      _ = _ := Finset.sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)
  change (∑ i ∈ Finset.range (2 * k + 1), f i) = _
  rw [hs]
  calc
    _ = (-1 : ℚ) ^ (k - a) *
        ∑ ell ∈ Finset.range (2 * (k - a) + 1), (-1 : ℚ) ^ ell *
          ((2 * (k - a)).choose ell : ℚ) *
          ((n - 2 * k + a + ell).factorial : ℚ) *
          ((n - 2 * k + a + 2 * (k - a) - ell).factorial : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell he
      have he' : ell ≤ 2 * (k - a) := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using he
      have hc : a ≤ a + ell ∧ a ≤ 2 * k - (a + ell) := by omega
      have hi : a + ell - a = ell := by omega
      have hn : n - (a + ell) = n - 2 * k + a + 2 * (k - a) - ell := by omega
      have hj : n - 2 * k + (a + ell) = n - 2 * k + a + ell := by omega
      have hp : k + (a + ell) = (k - a) + ell + 2 * a := by omega
      have hsign : (-1 : ℚ) ^ (2 * a) = 1 := by simp [pow_mul]
      dsimp only [f]
      rw [if_pos hc, hi, hn, hj, hp, pow_add, pow_add, hsign, mul_one]
      ring
    _ = _ := by
      rw [alternating_factorial_sum]
      rw [show n - 2 * k + a + (k - a) = n - k by omega]

private theorem coeff_matchingNumerator_fiber (n k : ℕ) (hk : 2 * k ≤ n)
    (S T : Finset (Fin n)) (hST : Disjoint S T) (hS : S.card ≤ k)
    (hT : T.card = 2 * (k - S.card)) :
    coeff (fiberExponent S T) (matchingNumerator n k) =
      (-1 : ℚ) ^ (k - S.card) *
        (((2 * (k - S.card)).factorial : ℚ) / ((k - S.card).factorial : ℚ) *
          ((n - 2 * k + S.card).factorial : ℚ) * ((n - k).factorial : ℚ)) := by
  classical
  rw [matchingNumerator]
  simp only [coeff_sum, coeff_C_mul]
  calc
    _ = ∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℚ) ^ (k + i) * ((n - i).factorial : ℚ) *
          ((n - 2 * k + i).factorial : ℚ) *
          (if S.card ≤ i ∧ S.card ≤ 2 * k - i
            then ((2 * (k - S.card)).choose (i - S.card) : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ 2 * k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      rw [coeff_esymm_mul_fiber n i (2 * k - i) S T hST]
      simp only [show i + (2 * k - i) = 2 * S.card + T.card by omega,
        and_true, hT]
    _ = _ := shifted_factorial_sum n k S.card hk hS

/-- Formula (star), with the nonzero scalar denominator kept on the left. -/
theorem matchingSum_esymm_mul (n k : ℕ) (hk : 2 * k ≤ n) :
    C (((n - 2 * k).factorial : ℚ) * ((n - k).factorial : ℚ)) *
      matchingSum (X : Fin n → MvPolynomial (Fin n) ℚ) k = matchingNumerator n k := by
  classical
  ext d
  rw [coeff_C_mul]
  by_cases hd : GoodExponent k d
  · obtain ⟨S, T, hST, hS, hT, rfl⟩ := goodExponent_fiber d hd
    rw [coeff_matchingSum_fiber n k S T hST hk hS hT,
      coeff_matchingNumerator_fiber n k hk S T hST hS hT]
    have hb : ((n - 2 * k).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - 2 * k)
    have hh : ((k - S.card).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (k - S.card)
    field_simp
  · rw [coeff_matchingSum_zero d hd, mul_zero, matchingNumerator]
    simp only [coeff_sum, coeff_C_mul]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_esymm_mul_zero i (2 * k - i) (by
      simp only [Finset.mem_range] at hi
      omega) d hd, mul_zero]

/-- Formula (star) as a rational scalar multiple of its explicit numerator. -/
theorem matchingSum_esymm (n k : ℕ) (hk : 2 * k ≤ n) :
    matchingSum (X : Fin n → MvPolynomial (Fin n) ℚ) k =
      C (1 / (((n - 2 * k).factorial : ℚ) * ((n - k).factorial : ℚ))) *
        matchingNumerator n k := by
  have hb : ((n - 2 * k).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2 * k)
  have hh : ((n - k).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  rw [← matchingSum_esymm_mul n k hk, ← mul_assoc, ← map_mul,
    one_div_mul_cancel (mul_ne_zero hb hh), map_one, one_mul]

private theorem aeval_matchingSum (r : Fin n → ℝ) (k : ℕ) :
    aeval r (matchingSum (X : Fin n → MvPolynomial (Fin n) ℚ) k) =
      matchingSum r k := by
  classical
  have he (e : Sym2 (Fin n)) :
      aeval r (edgeSquare (X : Fin n → MvPolynomial (Fin n) ℚ) e) = edgeSquare r e := by
    induction e using Sym2.ind with
    | _ i j => simp [edgeSquare]
  simp only [matchingSum, map_sum, map_prod, he]

private theorem elementaryCoeff_root (r : Fin n → ℝ) (i : ℕ) (hi : i ≤ n) :
    elementaryCoeff n (rootPolynomial r) i =
      aeval r (esymm (Fin n) ℚ i) := by
  classical
  rw [aeval_esymm_eq_multiset_esymm]
  have hp : rootPolynomial r =
      ((Finset.univ.val.map r).map fun t => Polynomial.X - Polynomial.C t).prod := by
    simp only [rootPolynomial, Multiset.map_map, Finset.prod]
    rfl
  have hc : (Finset.univ.val.map r).card = n := by simp
  rw [elementaryCoeff, hp, Multiset.prod_X_sub_C_coeff _ (by rw [hc]; omega),
    hc, Nat.sub_sub_self hi, ← mul_assoc, ← mul_pow]
  norm_num

private theorem real_descFactorial (n i : ℕ) (hi : i ≤ n) :
    (n.descFactorial i : ℝ) = (n.factorial : ℝ) / ((n - i).factorial : ℝ) := by
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero (n - i))).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.factorial_mul_descFactorial hi)

private theorem real_matchingSum_mul (n k : ℕ) (hk : 2 * k ≤ n) (r : Fin n → ℝ) :
    (((n - 2 * k).factorial : ℝ) * ((n - k).factorial : ℝ)) * matchingSum r k =
      ∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℝ) ^ (k + i) * ((n - i).factorial : ℝ) *
          ((n - 2 * k + i).factorial : ℝ) *
          (elementaryCoeff n (rootPolynomial r) i *
            elementaryCoeff n (rootPolynomial r) (2 * k - i)) := by
  classical
  have h := congrArg (fun P : MvPolynomial (Fin n) ℚ => aeval r P)
    (matchingSum_esymm_mul n k hk)
  simp only [map_mul, aeval_matchingSum, matchingNumerator, map_sum,
    map_pow, map_neg, map_one, map_natCast] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 2 * k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  rw [elementaryCoeff_root r i (by omega), elementaryCoeff_root r (2 * k - i) (by omega)]

private theorem symmetrize_factorial (n k : ℕ) (hk : 2 * k ≤ n) (p : Polynomial ℝ) :
    (-1 : ℝ) ^ k * (symmetrize n p).coeff (n - 2 * k) =
      (∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℝ) ^ (k + i) * ((n - i).factorial : ℝ) *
          ((n - 2 * k + i).factorial : ℝ) *
          (elementaryCoeff n p i * elementaryCoeff n p (2 * k - i))) /
        (((n - 2 * k).factorial : ℝ) * (n.factorial : ℝ)) := by
  classical
  rw [symmetrize_coefficient n k hk, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 2 * k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  rw [real_descFactorial n (2 * k) hk, real_descFactorial n i (by omega),
    real_descFactorial n (2 * k - i) (by omega),
    show n - (2 * k - i) = n - 2 * k + i by omega, pow_add]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hb : ((n - 2 * k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2 * k)
  have hi0 : ((n - i).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hj0 : ((n - 2 * k + i).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2 * k + i)
  field_simp

/-- The all-degree matching identity follows from (star), Vieta, and symmetrization. -/
theorem matching_identity : MatchingIdentity := by
  intro n k hk r
  rw [symmetrize_factorial n k hk, real_descFactorial n k (by omega)]
  have h := real_matchingSum_mul n k hk r
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hb : ((n - 2 * k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2 * k)
  have hh : ((n - k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  field_simp
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h.symm

#print axioms squarefree_apply
#print axioms sum_squarefree
#print axioms goodExponent_fiber
#print axioms edge_exponent_le_two
#print axioms decoration_good
#print axioms pair_good
#print axioms coeff_matchingSum_zero
#print axioms coeff_esymm_mul_zero
#print axioms shifted_factorial_sum
#print axioms coeff_matchingNumerator_fiber
#print axioms matchingSum_esymm_mul
#print axioms matchingSum_esymm
#print axioms aeval_matchingSum
#print axioms elementaryCoeff_root
#print axioms real_descFactorial
#print axioms real_matchingSum_mul
#print axioms symmetrize_factorial
#print axioms matching_identity

end D5.S3.Zeros.Convolution.MatchingPolynomial
