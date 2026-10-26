/- GID: D5/S3/Zeros/LeeYang/TreePairPolynomial
   generality: G
   mirror-B: D5/B/S3/Zeros/LeeYang/TreePairPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive allocation sums have exact degree and endpoint multiplicity. -/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Homogenize

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Polynomial

namespace FiolArbitraryTreePair

def vertexFactor (d r : ℕ) : ℝ[X] := 1 + C ((-1 : ℝ) ^ d) * X ^ (d + r)

def allocationPolynomial {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) : ℝ[X] :=
  ∑ a, C (w a) * ∏ v, vertexFactor (d v) (r a v)

theorem vertexFactor_zero (d r : ℕ) (hd : 0 < d) :
    (vertexFactor d r).coeff 0 = 1 := by
  have hm : d + r ≠ 0 := by omega
  rw [vertexFactor, coeff_add, coeff_C_mul_X_pow]
  simp only [coeff_one]
  simp [hm, Ne.symm hm, Nat.ne_of_gt hd]

theorem vertexFactor_degree (d r : ℕ) (hd : 0 < d) :
    (vertexFactor d r).natDegree = d + r := by
  unfold vertexFactor
  rw [natDegree_one_add, natDegree_C_mul_X_pow _ _ (pow_ne_zero _ (by norm_num))]

theorem vertexFactor_ne_zero (d r : ℕ) (hd : 0 < d) : vertexFactor d r ≠ 0 := by
  intro h
  have := vertexFactor_zero d r hd
  rw [h] at this
  norm_num at this

theorem vertexFactor_leadingCoeff (d r : ℕ) (hd : 0 < d) :
    (vertexFactor d r).leadingCoeff = (-1 : ℝ) ^ d := by
  rw [← coeff_natDegree, vertexFactor_degree d r hd]
  have hm : d + r ≠ 0 := by omega
  rw [vertexFactor, coeff_add, coeff_C_mul_X_pow]
  simp only [coeff_one]
  simp [hm, Ne.symm hm, Nat.ne_of_gt hd]

theorem allocation_constant {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (hd : ∀ v, 0 < d v) :
    (allocationPolynomial d r w).coeff 0 = ∑ a, w a := by
  classical
  simp [allocationPolynomial, coeff_zero_prod, vertexFactor_zero, hd]

theorem allocation_degree_and_leading {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a)
    (hmass : ∀ a, (∑ v, (d v + r a v)) = N) (hparity : Even (∑ v, d v)) :
    (allocationPolynomial d r w).natDegree = N ∧
      (allocationPolynomial d r w).leadingCoeff = ∑ a, w a ∧
      allocationPolynomial d r w ≠ 0 := by
  classical
  have hterm (a : A) : (C (w a) * ∏ v, vertexFactor (d v) (r a v)).natDegree = N := by
    rw [natDegree_C_mul (ne_of_gt (hw a)), natDegree_prod]
    · simpa only [vertexFactor_degree, hd] using hmass a
    · intro v _
      exact vertexFactor_ne_zero _ _ (hd v)
  have hlead (a : A) : (C (w a) * ∏ v, vertexFactor (d v) (r a v)).leadingCoeff = w a := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_prod]
    simp_rw [vertexFactor_leadingCoeff _ _ (hd _)]
    rw [Finset.prod_pow_eq_pow_sum]
    simp [hparity.neg_one_pow]
  have hcoeff : (allocationPolynomial d r w).coeff N = ∑ a, w a := by
    unfold allocationPolynomial
    rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hterm a, coeff_natDegree, hlead]
  have hpos : 0 < ∑ a, w a := Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  have hle : (allocationPolynomial d r w).natDegree ≤ N := by
    apply natDegree_sum_le_of_forall_le
    intro a _
    exact le_of_eq (hterm a)
  have hge : N ≤ (allocationPolynomial d r w).natDegree :=
    le_natDegree_of_ne_zero (by rw [hcoeff]; exact ne_of_gt hpos)
  have hdeg := le_antisymm hle hge
  refine ⟨hdeg, ?_, ?_⟩
  · rw [← coeff_natDegree, hdeg, hcoeff]
  · intro h
    rw [h, coeff_zero] at hcoeff
    linarith

def quotientVertexFactor (d r : ℕ) : ℝ[X] :=
  if Odd d then ∑ i ∈ Finset.range (d + r), X ^ i else vertexFactor d r

def oddCount {V : Type*} [Fintype V] (d : V → ℕ) : ℕ :=
  (Finset.univ.filter fun v => Odd (d v)).card

def allocationQuotient {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) : ℝ[X] :=
  ∑ a, C (w a) * ∏ v, quotientVertexFactor (d v) (r a v)

theorem vertex_factor_at_one (d r : ℕ) :
    vertexFactor d r = (if Odd d then 1 - X else 1) * quotientVertexFactor d r := by
  classical
  by_cases h : Odd d
  · simp only [quotientVertexFactor, if_pos h, vertexFactor, h.neg_one_pow, C_neg, C_1,
      neg_one_mul]
    have he := geom_sum_mul_neg (X : ℝ[X]) (d + r)
    simpa [mul_comm, sub_eq_add_neg] using he.symm
  · simp [quotientVertexFactor, h]

theorem allocation_factor_at_one {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) :
    allocationPolynomial d r w = (1 - X) ^ oddCount d * allocationQuotient d r w := by
  classical
  unfold allocationPolynomial allocationQuotient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [vertex_factor_at_one, Finset.prod_mul_distrib]
  have he : (∏ v, if Odd (d v) then (1 - X : ℝ[X]) else 1) = (1 - X) ^ oddCount d := by
    simp [oddCount, Finset.prod_ite, Finset.prod_const]
  rw [he]
  ring

theorem allocation_quotient_at_one_pos {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a) :
    0 < (allocationQuotient d r w).eval 1 := by
  classical
  unfold allocationQuotient
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod]
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro a _
  apply mul_pos (hw a)
  apply Finset.prod_pos
  intro v _
  unfold quotientVertexFactor
  split_ifs with h
  · simp only [eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (show 0 < d v + r a v by have := hd v; omega)
  · have he : Even (d v) := Nat.not_odd_iff_even.mp h
    norm_num [vertexFactor, he.neg_one_pow]

theorem allocation_multiplicity_one {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a) :
    (allocationPolynomial d r w).rootMultiplicity 1 = oddCount d := by
  have hQ : allocationQuotient d r w ≠ 0 := by
    intro h
    have := allocation_quotient_at_one_pos d r w hd hw
    rw [h, eval_zero] at this
    linarith
  have hroot : (allocationQuotient d r w).rootMultiplicity 1 = 0 := by
    apply rootMultiplicity_eq_zero
    exact ne_of_gt (allocation_quotient_at_one_pos d r w hd hw)
  rw [allocation_factor_at_one]
  have hf : (1 - X : ℝ[X]) = C (-1) * (X - C 1) := by simp
  rw [hf, mul_pow]
  have hne : C (-1 : ℝ) ^ oddCount d * allocationQuotient d r w ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by simp)) hQ
  have he : C (-1 : ℝ) ^ oddCount d * (X - C 1) ^ oddCount d *
      allocationQuotient d r w =
      (C (-1) ^ oddCount d * allocationQuotient d r w) * (X - C 1) ^ oddCount d := by ring
  rw [he, rootMultiplicity_mul_X_sub_C_pow hne]
  have hc : (C (-1 : ℝ) ^ oddCount d).rootMultiplicity 1 = 0 := by
    apply rootMultiplicity_eq_zero
    simp [Polynomial.IsRoot]
  rw [rootMultiplicity_mul hne, hc, hroot]
  simp

def complexEval (p : ℝ[X]) (x : ℂ) : ℂ := p.eval₂ (algebraMap ℝ ℂ) x

theorem vertexFactor_eval (d r : ℕ) (x : ℂ) :
    complexEval (vertexFactor d r) x = 1 + (-1 : ℂ) ^ d * x ^ (d + r) := by
  simp [complexEval, vertexFactor]

theorem vertexFactor_reciprocal (d r : ℕ) (x : ℂ) (hx : x ≠ 0) :
    x ^ (d + r) * complexEval (vertexFactor d r) x⁻¹ =
      (-1 : ℂ) ^ d * complexEval (vertexFactor d r) x := by
  rw [vertexFactor_eval, vertexFactor_eval]
  have hs : ((-1 : ℂ) ^ d) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [inv_pow]
  calc
    x ^ (d + r) * (1 + (-1 : ℂ) ^ d * (x ^ (d + r))⁻¹) =
        x ^ (d + r) + (-1 : ℂ) ^ d := by field_simp
    _ = (-1 : ℂ) ^ d * (1 + (-1 : ℂ) ^ d * x ^ (d + r)) := by
      linear_combination -(x ^ (d + r)) * hs

theorem allocation_reciprocal {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hmass : ∀ a, (∑ v, (d v + r a v)) = N) (hparity : Even (∑ v, d v))
    (x : ℂ) (hx : x ≠ 0) :
    x ^ N * complexEval (allocationPolynomial d r w) x⁻¹ =
      complexEval (allocationPolynomial d r w) x := by
  classical
  simp only [allocationPolynomial, complexEval, eval₂_finsetSum, eval₂_mul, eval₂_C,
    eval₂_finsetProd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he := congrArg (fun q : V → ℂ => ∏ v, q v)
    (funext fun v => vertexFactor_reciprocal (d v) (r a v) x hx)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hmass a,
    hparity.neg_one_pow, one_mul, complexEval] at he
  rw [mul_left_comm, he]

theorem allocation_roots_on_circle {V A : Type*} [Fintype V] [Fintype A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hmass : ∀ a, (∑ v, (d v + r a v)) = N) (hparity : Even (∑ v, d v))
    (hdisk : ∀ x : ℂ, ‖x‖ < 1 → complexEval (allocationPolynomial d r w) x ≠ 0)
    (x : ℂ) (hx : complexEval (allocationPolynomial d r w) x = 0) : ‖x‖ = 1 := by
  have hn : ¬ ‖x‖ < 1 := by intro h; exact hdisk x h hx
  have hpos : 0 < ‖x‖ := by linarith
  by_contra hne
  have hgt : 1 < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
  have hi : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hgt
  have hrec := allocation_reciprocal d r w N hmass hparity x
    (norm_pos_iff.mp hpos)
  rw [hx] at hrec
  exact hdisk x⁻¹ hi ((mul_eq_zero.mp hrec).resolve_left
    (pow_ne_zero _ (norm_pos_iff.mp hpos)))

theorem vertexFactor_eval_neg_one (d r : ℕ) :
    (vertexFactor d r).eval (-1) = 1 + (-1 : ℝ) ^ r := by
  simp only [vertexFactor, eval_add, eval_one, eval_mul, eval_C, eval_pow, eval_X, pow_add]
  have hs : (-1 : ℝ) ^ d * (-1 : ℝ) ^ d = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [← mul_assoc, hs, one_mul]

end FiolArbitraryTreePair

open scoped BigOperators
open Polynomial

namespace FiolArbitraryTreePair

theorem homogenize_axis_scaled {R : Type*} [CommSemiring R]
    (p : R[X]) (N : ℕ) (x : R) :
    MvPolynomial.eval ![x,0] (p.homogenize N) = p.coeff N * x ^ N := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simpa [add_mul] using congrArg₂ (fun a b : R => a + b) ihp ihq
  | monomial k c =>
    rcases le_or_gt k N with hk | hk
    · rw [homogenize_monomial hk]
      by_cases h : k = N
      · subst k
        simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]
      · have hn : N - k ≠ 0 := by omega
        simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two,
          hn, coeff_monomial, h, Ne.symm h]
    · rw [homogenize_monomial_of_lt hk]
      simp [coeff_monomial, Nat.ne_of_gt hk, Ne.symm (Nat.ne_of_gt hk)]

theorem homogenize_axis {R : Type*} [CommSemiring R] (p : R[X]) (N : ℕ) :
    MvPolynomial.eval ![(1 : R),0] (p.homogenize N) = p.coeff N := by
  simpa using homogenize_axis_scaled p N 1

theorem complexEval_real (p : ℝ[X]) (x : ℝ) :
    complexEval p (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [complexEval] using congrArg₂ (fun a b : ℂ => a + b) hp hq
  | monomial k c => simp [complexEval]

theorem homogenize_complex_eval (p : ℝ[X]) (N : ℕ) (hN : p.natDegree ≤ N)
    (x : Fin 2 → ℂ) (hx : x 1 ≠ 0) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) x (p.homogenize N) =
      complexEval p (x 0 / x 1) * x 1 ^ N := by
  rw [MvPolynomial.eval₂_eq_eval_map, ← homogenize_map]
  rw [eval_homogenize ((natDegree_map_le).trans hN) x hx]
  simp only [Polynomial.eval_map,complexEval]

theorem homogenize_complex_infinity (p : ℝ[X]) (N : ℕ) (x : ℂ) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) ![x,0] (p.homogenize N) =
      (p.coeff N : ℂ) * x ^ N := by
  rw [MvPolynomial.eval₂_eq_eval_map, ← homogenize_map, homogenize_axis_scaled]
  simp

theorem allocation_quotient_degree {V A : Type*} [Fintype V] [Fintype A] [Nonempty A]
    (d : V → ℕ) (r : A → V → ℕ) (w : A → ℝ) (N : ℕ)
    (hd : ∀ v, 0 < d v) (hw : ∀ a, 0 < w a)
    (hdegree : (allocationPolynomial d r w).natDegree = N) :
    (allocationQuotient d r w).natDegree = N - oddCount d := by
  have hQ : allocationQuotient d r w ≠ 0 := by
    intro h
    have := allocation_quotient_at_one_pos d r w hd hw
    rw [h, eval_zero] at this
    linarith
  have hf : (1 - X : ℝ[X]) = C (-1) * (X - C 1) := by simp
  have hfne : (1 - X : ℝ[X]) ≠ 0 := by rw [hf]; exact mul_ne_zero (by simp) (X_sub_C_ne_zero 1)
  have hdeg : (1 - X : ℝ[X]).natDegree = 1 := by
    rw [hf, natDegree_C_mul (by norm_num), natDegree_X_sub_C]
  have he := congrArg Polynomial.natDegree (allocation_factor_at_one d r w)
  rw [hdegree, natDegree_mul (pow_ne_zero _ hfne) hQ] at he
  simp only [natDegree_pow, hdeg, mul_one, one_mul] at he
  omega

end FiolArbitraryTreePair
