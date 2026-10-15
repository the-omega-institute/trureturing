/- GID: D5/S3/ArithSums/HannaLaurentRowSums
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentRowSums
   mirror-E: none(waiver:symbolic-laurent-coefficient-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.LaurentSeries,mathlib/module/Mathlib.RingTheory.HahnSeries.Summable]
   utility: none
   digest: Formal bilateral Laurent coefficients and the A391810 zero-row-sum assertion. -/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

set_option maxRecDepth 2048
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.HannaLaurentRowSums

open scoped BigOperators
open HahnSeries
noncomputable section

/-- The Laurent monomial with coefficient one. -/
def z (k : ℤ) : LaurentSeries ℚ := single k 1

/-- The literal summand, with integer powers interpreted in the Laurent field. -/
def summand (n : ℕ) (k : ℤ) : LaurentSeries ℚ :=
  z k * (1 - z k) ^ ((n : ℤ) + k)

private theorem z_ne_zero (k : ℤ) : z k ≠ 0 := single_ne_zero (by norm_num)

private theorem order_inv (f : LaurentSeries ℚ) (hf : f ≠ 0) :
    f⁻¹.order = -f.order := by
  have h := order_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, order_one] at h
  omega

private theorem order_zpow (f : LaurentSeries ℚ) (hf : f ≠ 0) (a : ℤ) :
    (f ^ a).order = a * f.order := by
  cases a with
  | ofNat a => simp [zpow_natCast, order_pow, nsmul_eq_mul]
  | negSucc a =>
    rw [zpow_negSucc, order_inv _ (pow_ne_zero _ hf), order_pow]
    simp [Int.negSucc_eq]
    ring

private theorem binomial_order (k : ℤ) (hk : k ≠ 0) :
    (1 - z k).order = min 0 k := by
  have htop : (1 - z k).orderTop = (min 0 k : ℤ) := by
    rcases lt_or_gt_of_ne hk with h | h
    · rw [sub_eq_add_neg, orderTop_add_eq_right]
      · simp [z, orderTop_neg, orderTop_single, min_eq_right h.le]
      · simp only [orderTop_one, orderTop_neg, z, orderTop_single (by norm_num : (1 : ℚ) ≠ 0)]
        exact_mod_cast h
    · rw [orderTop_sub]
      · simp [min_eq_left h.le]
      · simp only [orderTop_one, z, orderTop_single (by norm_num : (1 : ℚ) ≠ 0)]
        exact_mod_cast h
  have hne : 1 - z k ≠ 0 := by
    intro he
    rw [he, orderTop_zero] at htop
    exact WithTop.top_ne_coe htop
  exact WithTop.coe_inj.mp ((order_eq_orderTop_of_ne_zero hne).trans htop)

private theorem binomial_ne_zero (k : ℤ) (hk : k ≠ 0) : 1 - z k ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LaurentSeries ℚ => f.coeff k) h
  simp [z, hk, coeff_one, coeff_single] at hc

/-- The exact order of every nonzero-index rational summand. -/
theorem summand_order (n : ℕ) (k : ℤ) (hk : k ≠ 0) :
    (summand n k).order = k + ((n : ℤ) + k) * min 0 k := by
  rw [summand, order_mul (z_ne_zero k) (zpow_ne_zero _ (binomial_ne_zero k hk)),
    order_zpow _ (binomial_ne_zero k hk), binomial_order k hk]
  simp [z, order_single]

private theorem summand_zero (n : ℕ) (hn : 0 < n) : summand n 0 = 0 := by
  simp [summand, z, zpow_natCast, hn.ne']

/-- The bilateral support has a uniform lower bound. -/
theorem summand_lower_bound (n : ℕ) (hn : 0 < n) (k d : ℤ)
    (hd : (summand n k).coeff d ≠ 0) : -((n : ℤ) + 1)^2 ≤ d := by
  have hk : k ≠ 0 := by intro h; subst k; simp [summand_zero n hn] at hd
  have ho := order_le_of_coeff_ne_zero hd
  rw [summand_order n k hk] at ho
  rcases lt_or_gt_of_ne hk with hk | hk
  · rw [min_eq_right hk.le] at ho
    nlinarith [sq_nonneg (k + (n : ℤ) + 1), sq_nonneg k]
  · rw [min_eq_left hk.le] at ho
    nlinarith [sq_nonneg ((n : ℤ) + 1)]

/-- Only finitely many outer indices contribute to any fixed coefficient. -/
theorem coefficient_finite (n : ℕ) (hn : 0 < n) (d : ℤ) :
    {k : ℤ | (summand n k).coeff d ≠ 0}.Finite := by
  apply (Set.finite_Icc (-((n : ℤ) + d.natAbs + 2)) (d.natAbs + 1)).subset
  intro k hd
  have hk : k ≠ 0 := by intro h; subst k; simp [summand_zero n hn] at hd
  have ho := order_le_of_coeff_ne_zero hd
  rw [summand_order n k hk] at ho
  have habs : d ≤ (d.natAbs : ℤ) := Int.le_natAbs
  have habs0 : (0 : ℤ) ≤ d.natAbs := by positivity
  constructor
  · by_contra hh
    have hb : k < -((n : ℤ) + d.natAbs + 2) := by omega
    rw [min_eq_right (by omega)] at ho
    nlinarith
  · rcases le_or_gt k 0 with h | h
    · omega
    · rw [min_eq_left h.le] at ho
      omega

/-- The original doubly infinite family is formally summable at zero. -/
def family (n : ℕ) (hn : 0 < n) : SummableFamily ℤ ℚ ℤ where
  toFun := summand n
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.wellFoundedOn_lt
    refine ⟨-((n : ℤ) + 1)^2, ?_⟩
    intro d hd
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hd
    exact summand_lower_bound n hn k d hk
  finite_co_support' := coefficient_finite n hn

/-- The formal Laurent series in the published definition. -/
def series (n : ℕ) (hn : 0 < n) : LaurentSeries ℚ := (family n hn).hsum

/-- The finite negative-power polynomial, written in the inverse variable. -/
def rowPolynomial (n : ℕ) : Polynomial ℤ :=
  -1 + ∑ j ∈ Finset.range n,
    Polynomial.X ^ (j + 1) * (1 - Polynomial.X ^ (j + 1)) ^ (n - (j + 1))

private theorem z_mul (a b : ℤ) : z a * z b = z (a + b) := by
  simp [z, single_mul_single]

private theorem negative_binomial (j : ℕ) :
    1 - z (-(j : ℤ)) = -z (-(j : ℤ)) * (1 - z j) := by
  have h : z (-(j : ℤ)) * z j = 1 := by rw [z_mul]; simp [z]
  calc
    1 - z (-(j : ℤ)) = z (-(j : ℤ)) * z j - z (-(j : ℤ)) := by rw [h]
    _ = _ := by ring

private theorem negative_boundary (n : ℕ) :
    summand n (-((n : ℤ) + 1)) = -(1 - z ((n : ℤ) + 1))⁻¹ := by
  rw [summand, show (n : ℤ) + (-((n : ℤ) + 1)) = -1 by ring]
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
    negative_binomial, zpow_neg_one, mul_inv_rev, inv_neg]
  have hz := z_ne_zero (-((n + 1 : ℕ) : ℤ))
  field_simp

private theorem inverse_constant (j : ℤ) (hj : 0 < j) :
    ((1 - z j)⁻¹).coeff 0 = 1 := by
  have hn := binomial_ne_zero j hj.ne'
  have ho : (1 - z j).order = 0 := by rw [binomial_order j hj.ne', min_eq_left hj.le]
  have h := coeff_mul_order_add_order (1 - z j) (1 - z j)⁻¹
  have hi : ((1 - z j)⁻¹).order = 0 := by rw [order_inv _ hn, ho, neg_zero]
  rw [mul_inv_cancel₀ hn, ho, hi] at h
  rw [leadingCoeff_eq, leadingCoeff_eq, ho, hi] at h
  simpa [z, hj.ne', Ne.symm hj.ne', coeff_one, coeff_single] using h.symm

private theorem boundary_coeff (n : ℕ) (m : ℕ) :
    (summand n (-((n : ℤ) + 1))).coeff (-(m : ℤ)) =
      if m = 0 then -1 else 0 := by
  rw [negative_boundary, coeff_neg]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, neg_zero, if_pos rfl]
    rw [inverse_constant ((n : ℤ) + 1) (by omega)]
    simp
  · rw [coeff_eq_zero_of_lt_order, neg_zero, if_neg hm]
    rw [order_inv _ (binomial_ne_zero _ (by omega)), binomial_order _ (by omega),
      min_eq_left (by omega), neg_zero]
    omega

private theorem negative_finite_term (n j : ℕ) (hj : j < n) :
    summand n (-((j + 1 : ℕ) : ℤ)) =
      (Polynomial.X ^ (j + 1) * (1 - Polynomial.X ^ (j + 1)) ^ (n - (j + 1)) :
        Polynomial ℤ).eval₂ (Int.castRingHom (LaurentSeries ℚ)) (z (-1)) := by
  have hz : z (-1) ^ (j + 1) = z (-((j + 1 : ℕ) : ℤ)) := by
    simp [z, single_pow, nsmul_eq_mul]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, hz]
  rw [summand, show (n : ℤ) + (-((j + 1 : ℕ) : ℤ)) = ((n - (j + 1) : ℕ) : ℤ) by omega,
    zpow_natCast]

private theorem coeff_polynomial (p : Polynomial ℤ) (m : ℕ) :
    (p.eval₂ (Int.castRingHom (LaurentSeries ℚ)) (z (-1))).coeff (-(m : ℤ)) =
      (p.coeff m : ℚ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, coeff_add, hp, hq]
  | monomial j a =>
    simp [Polynomial.eval₂_monomial, z, single_pow, nsmul_eq_mul,
      ← single_zero_intCast, single_mul_single, coeff_single, Polynomial.coeff_monomial,
      eq_comm]

/-- Every nonpositive coefficient of the original bilateral sum is the integer
coefficient of the finite inverse-variable polynomial. -/
theorem series_coefficient (n : ℕ) (hn : 0 < n) (m : ℕ) :
    (series n hn).coeff (-(m : ℤ)) = ((rowPolynomial n).coeff m : ℚ) := by
  classical
  let t := (Finset.range (n + 1)).image (fun j : ℕ => -((j + 1 : ℕ) : ℤ))
  have hs : {k : ℤ | (summand n k).coeff (-(m : ℤ)) ≠ 0} ⊆ t := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; subst k; simp [summand_zero n hn] at hk
    have ho := order_le_of_coeff_ne_zero hk
    rw [summand_order n k hk0] at ho
    have hkneg : k < 0 := by
      by_contra hh
      rw [min_eq_left (by omega)] at ho
      omega
    have hkb : -((n : ℤ) + 1) ≤ k := by
      rw [min_eq_right hkneg.le] at ho
      nlinarith
    refine Finset.mem_image.mpr ⟨(-k - 1).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  change (family n hn).hsum.coeff _ = _
  rw [SummableFamily.coeff_hsum_eq_sum_of_subset hs]
  change (∑ k ∈ t, (summand n k).coeff (-(m : ℤ))) = _
  rw [Finset.sum_image]
  · rw [Finset.sum_range_succ]
    rw [show -((n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) by omega, boundary_coeff]
    have ht : ∀ j ∈ Finset.range n,
        (summand n (-((j + 1 : ℕ) : ℤ))).coeff (-(m : ℤ)) =
          ((Polynomial.X ^ (j + 1) * (1 - Polynomial.X ^ (j + 1)) ^ (n - (j + 1)) :
            Polynomial ℤ).coeff m : ℚ) := by
      intro j hj
      rw [negative_finite_term n j (Finset.mem_range.mp hj), coeff_polynomial]
    rw [Finset.sum_congr rfl ht]
    simp [rowPolynomial, Polynomial.coeff_sum, Polynomial.coeff_neg,
      Polynomial.coeff_one, add_comm]
    split_ifs <;> norm_num
  · intro a ha b hb h
    simp only [neg_inj, Int.natCast_inj, Nat.add_right_cancel_iff] at h
    exact h


/-- The inclusive bound in the published row definition. -/
def rowBound (n : ℕ) : ℕ := ((n + 1) / 2)^2

private def binomialTerm (n j r : ℕ) : Polynomial ℤ :=
  Polynomial.C ((-1 : ℤ)^r * (Nat.choose (n - (j + 1)) r : ℤ)) *
    Polynomial.X ^ ((j + 1) * (r + 1))

private def lowerPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range n, ∑ r ∈ Finset.range (n - (j + 1)), binomialTerm n j r

private def topTerm (n j : ℕ) : Polynomial ℤ :=
  Polynomial.C ((-1 : ℤ)^(n - (j + 1))) *
    Polynomial.X ^ ((j + 1) * (n - j))

private theorem polynomial_expansion (n : ℕ) :
    rowPolynomial n = -1 + lowerPolynomial n + ∑ j ∈ Finset.range n, topTerm n j := by
  unfold rowPolynomial lowerPolynomial
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have he : (Polynomial.X ^ (j + 1) *
      (1 - Polynomial.X ^ (j + 1)) ^ (n - (j + 1)) : Polynomial ℤ) =
        ∑ r ∈ Finset.range (n - (j + 1) + 1), binomialTerm n j r := by
    rw [sub_eq_add_neg, add_comm (1 : Polynomial ℤ), add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [neg_pow]
    simp only [one_pow, mul_one]
    rw [binomialTerm, Polynomial.C_mul, Polynomial.C_pow]
    simp only [map_neg, map_one, map_intCast, map_natCast]
    rw [← pow_mul]
    rw [show (j + 1) * (r + 1) = (j + 1) + (j + 1) * r by ring, pow_add]
    ring
  rw [he, Finset.sum_range_succ]
  congr 1
  simp only [binomialTerm, Nat.choose_self, Int.natCast_one, mul_one, topTerm]
  rw [show n - (j + 1) + 1 = n - j by omega]

private theorem product_bound (a b h : ℕ) (hab : a + b ≤ 2 * h) : a * b ≤ h^2 := by
  nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]

private theorem lower_degree (n : ℕ) : (lowerPolynomial n).natDegree ≤ rowBound n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  have he : (j + 1) * (r + 1) ≤ rowBound n := by
    apply product_bound
    have hjn := Finset.mem_range.mp hj
    have hrn := Finset.mem_range.mp hr
    omega
  unfold binomialTerm
  calc
    _ ≤ (Polynomial.C ((-1 : ℤ)^r * (Nat.choose (n - (j + 1)) r : ℤ))).natDegree +
        (Polynomial.X ^ ((j + 1) * (r + 1)) : Polynomial ℤ).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ rowBound n := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]; exact he

private theorem top_cancel (h : ℕ) :
    (∑ j ∈ Finset.range (2 * h), topTerm (2 * h) j) = 0 := by
  classical
  apply Finset.sum_involution (fun j _ => 2 * h - 1 - j)
  · intro j hj
    have hjn := Finset.mem_range.mp hj
    have ht : topTerm (2 * h) (2 * h - 1 - j) = -topTerm (2 * h) j := by
      have he : 2 * h - (2 * h - 1 - j + 1) = j := by omega
      have hd : (2 * h - 1 - j + 1) * (2 * h - (2 * h - 1 - j)) =
          (j + 1) * (2 * h - j) := by
        rw [show 2 * h - 1 - j + 1 = 2 * h - j by omega,
          show 2 * h - (2 * h - 1 - j) = j + 1 by omega]
        ring
      have hs : (-1 : ℤ)^j = -(-1 : ℤ)^(2 * h - (j + 1)) := by
        rw [neg_one_pow_eq_pow_mod_two j,
          neg_one_pow_eq_pow_mod_two (2 * h - (j + 1))]
        have hm : j % 2 < 2 := Nat.mod_lt _ (by decide)
        rcases Nat.mod_two_eq_zero_or_one j with hm | hm
        · rw [hm, show (2 * h - (j + 1)) % 2 = 1 by omega]
          norm_num
        · rw [hm, show (2 * h - (j + 1)) % 2 = 0 by omega]
          norm_num
      simp only [topTerm, he, hd, hs, Polynomial.C_neg, neg_mul]
    rw [ht, add_neg_cancel]
  · intro j hj _
    have hjn := Finset.mem_range.mp hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at *
    omega
  · intro j hj
    simp only [Finset.mem_range] at *
    omega

/-- All powers in the finite row polynomial satisfy the exact published bound. -/
theorem row_degree (n : ℕ) : (rowPolynomial n).natDegree ≤ rowBound n := by
  rw [polynomial_expansion]
  have hl := lower_degree n
  have hc : (-1 : Polynomial ℤ).natDegree ≤ rowBound n := by simp [rowBound]
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨h, rfl⟩ := hn
    rw [show h + h = 2 * h by omega, top_cancel, add_zero]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp [rowBound]) (lower_degree _))
  · obtain ⟨h, rfl⟩ := hn
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le hc hl)
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      have hjn := Finset.mem_range.mp hj
      have he : (j + 1) * (2 * h + 1 - j) ≤ rowBound (2 * h + 1) := by
        unfold rowBound
        rw [show (2 * h + 1 + 1) / 2 = h + 1 by omega]
        apply product_bound
        omega
      unfold topTerm
      calc
        _ ≤ (Polynomial.C ((-1 : ℤ)^(2 * h + 1 - (j + 1)))).natDegree +
            (Polynomial.X ^ ((j + 1) * (2 * h + 1 - j)) : Polynomial ℤ).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ rowBound (2 * h + 1) := by
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
          exact he

private theorem polynomial_at_one (n : ℕ) (hn : 0 < n) :
    (rowPolynomial n).eval 1 = 0 := by
  simp only [rowPolynomial, Polynomial.eval_add, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow, one_mul, sub_self]
  rw [Finset.sum_eq_single (n - 1)]
  · simp [show n - (n - 1 + 1) = 0 by omega]
  · intro j hj hjne
    have hjn := Finset.mem_range.mp hj
    have hp : n - (j + 1) ≠ 0 := by omega
    simp [hp]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

/-- Integer entries of the full row, including its constant coefficient. -/
def rowEntry (n m : ℕ) : ℤ := (rowPolynomial n).coeff m

/-- The original row sum is zero for every positive row index. -/
private theorem integer_row_sum (n : ℕ) (hn : 0 < n) :
    ∑ m ∈ Finset.range (rowBound n + 1), rowEntry n m = 0 := by
  have he := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (row_degree n)) (1 : ℤ)
  simpa [rowEntry, one_pow] using he.symm.trans (polynomial_at_one n hn)

/-- The full integer row sum, its original Laurent-series counterpart, and the
vanishing of every nonpositive coefficient outside the published row. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.range (rowBound n + 1), rowEntry n m = 0) ∧
    (∑ m ∈ Finset.range (rowBound n + 1), (series n hn).coeff (-(m : ℤ)) = 0) ∧
    (∀ m : ℕ, rowBound n < m → (series n hn).coeff (-(m : ℤ)) = 0) := by
  refine ⟨integer_row_sum n hn, ?_, ?_⟩
  · simp_rw [series_coefficient]
    rw [← Int.cast_sum]
    exact_mod_cast integer_row_sum n hn
  · intro m hm
    rw [series_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (row_degree n) hm), Int.cast_zero]

#print axioms row_degree
#print axioms result

#print axioms series_coefficient
#print axioms summand_order
#print axioms summand_lower_bound
#print axioms coefficient_finite

end
end D5.S3.ArithSums.HannaLaurentRowSums
