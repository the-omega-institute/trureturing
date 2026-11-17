/- GID: D5/S1/Recurrence/RowlandSistosBarronRankSequences
   generality: I
   mirror-B: D5/B/S1/Recurrence/RowlandSistosBarronRankSequences
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Parameter-dependent coefficient cancellation gives infinitely many rank sequences. -/

/-
Public theorem: D5.S1.Recurrence.RowlandSistosBarronRankSequences.result
proof_shape: content (finite parameter fibres and coefficient positivity and cancellation inductions).
escape_witness: none; no escape-witness basis is claimed.
admission_basis: open-problem-resolution (#19942; Refuted).
Direct frozen dependencies: none (all imported declarations are pinned Mathlib).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20338
The parameter polynomial is Mathlib Polynomial.trinomial; its coefficients are used directly.
The rational tail-recurrence, minimum rank and positive-exponent indexing agree with #19942.
Every private lemma is a consumed helper; their classifications and consumers follow.
charPoly_natDegree: proof_shape: bind-only; consumers: exponential_lower; direct frozen dependencies: none; escape_witness: none.
exponential_lower: proof_shape: bind-only; consumers: exponential_rank; direct frozen dependencies: none; escape_witness: none.
polynomial_recurrence: proof_shape: bind-only; consumers: exponential_upper; direct frozen dependencies: none; escape_witness: none.
exponential_upper: proof_shape: bind-only; consumers: exponential_rank, exponential_upper_fintype; direct frozen dependencies: none; escape_witness: none.
exponential_rank: proof_shape: bind-only; consumers: exponential_rank_fintype; direct frozen dependencies: none; escape_witness: none.
exponential_rank_fintype: proof_shape: bind-only; consumers: polynomial_support_rank; direct frozen dependencies: none; escape_witness: none.
exponential_upper_fintype: proof_shape: bind-only; consumers: polynomial_support_rank; direct frozen dependencies: none; escape_witness: none.
polynomial_support_rank: proof_shape: bind-only; consumers: family_power_rank; direct frozen dependencies: none; escape_witness: none.
eval_A: proof_shape: bind-only; consumers: A_ne_zero, finite_bad_parameter; direct frozen dependencies: none; escape_witness: none.
trinomial_coeff_rec: proof_shape: bind-only; consumers: trinomial_pos; direct frozen dependencies: none; escape_witness: none.
trinomial_nonneg: proof_shape: bind-only; consumers: trinomial_pos; direct frozen dependencies: none; escape_witness: none.
trinomial_pos: proof_shape: content; consumers: A_ne_zero; direct frozen dependencies: none; escape_witness: none.
A_ne_zero: proof_shape: content; consumers: finite_bad_parameter; direct frozen dependencies: none; escape_witness: none.
F_power_coeff_rec: proof_shape: bind-only; consumers: trinomial_coeff_rec, low_coeffs; direct frozen dependencies: none; escape_witness: none.
low_coeffs: proof_shape: content; consumers: cancellation; direct frozen dependencies: none; escape_witness: none.
cancellation: proof_shape: content; consumers: power_cancellation_rank; direct frozen dependencies: none; escape_witness: none.
finite_bad_parameter: proof_shape: content; consumers: finite_rank_sequence_fibre; direct frozen dependencies: none; escape_witness: none.
family_closed: proof_shape: bind-only; consumers: family_power_closed; direct frozen dependencies: none; escape_witness: none.
family_power_closed: proof_shape: bind-only; consumers: family_power_rank; direct frozen dependencies: none; escape_witness: none.
family_power_rank: proof_shape: bind-only; consumers: family_rank_three, power_full_rank, power_cancellation_rank; direct frozen dependencies: none; escape_witness: none.
support_F: proof_shape: bind-only; consumers: family_rank_three; direct frozen dependencies: none; escape_witness: none.
family_rank_three: proof_shape: bind-only; consumers: result; direct frozen dependencies: none; escape_witness: none.
power_degree_bound: proof_shape: bind-only; consumers: power_full_rank, power_cancellation_rank; direct frozen dependencies: none; escape_witness: none.
power_full_rank: proof_shape: bind-only; consumers: finite_rank_sequence_fibre; direct frozen dependencies: none; escape_witness: none.
power_cancellation_rank: proof_shape: content; consumers: finite_rank_sequence_fibre; direct frozen dependencies: none; escape_witness: none.
finite_rank_sequence_fibre: proof_shape: content; consumers: result; direct frozen dependencies: none; escape_witness: none.
All declarations treat symbolic unbounded parameters, exponents and sequence indices; utility kind=none.
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.UnitTrinomial
import Mathlib.Algebra.LinearRecurrence

namespace D5.S1.Recurrence.RowlandSistosBarronRankSequences

/-- `s` satisfies, for every sufficiently large `n`, a recurrence of size `r` with constant rational coefficients
and `c₀ ≠ 0`: some `E : LinearRecurrence ℚ` of order `r` with `E.coeffs 0 ≠ 0` solves a tail of `s`. -/
def HasRecurrence (s : ℕ → ℤ) (r : ℕ) : Prop :=
  ∃ E : LinearRecurrence ℚ, E.order = r ∧ (∀ h : 0 < E.order, E.coeffs ⟨0, h⟩ ≠ 0) ∧
    ∃ N : ℕ, E.IsSolution fun n => (s (n + N) : ℚ)

/-- `s` is constant-recursive. -/
def IsConstantRecursive (s : ℕ → ℤ) : Prop :=
  ∃ r, HasRecurrence s r

/-- The rank of `s`: the size of its minimal recurrence. -/
noncomputable def rank (s : ℕ → ℤ) : ℕ :=
  sInf {r | HasRecurrence s r}

/-- The rank sequence `(rank s(n)^M)_{M≥1}` of `s`. -/
noncomputable def rankSequence (s : ℕ → ℤ) : ℕ+ → ℕ :=
  fun M => rank fun n => s n ^ (M : ℕ)

/-- The conjecture of Section 1: for each `r ≥ 1`, only finitely many rank sequences arise from constant-recursive
integer sequences of rank `r`. -/
def claim : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    {R : ℕ+ → ℕ | ∃ s : ℕ → ℤ, IsConstantRecursive s ∧ rank s = r ∧ R = rankSequence s}.Finite

end D5.S1.Recurrence.RowlandSistosBarronRankSequences

open Finset Polynomial
namespace D5.S1.Recurrence.RowlandSistosBarronRankSequences

private lemma charPoly_natDegree (E : LinearRecurrence ℚ) : E.charPoly.natDegree = E.order := by
  exact Polynomial.natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order

private lemma exponential_lower {h : ℕ} (v c : Fin h → ℚ)
    (hv : Function.Injective v) (hv0 : ∀ i, v i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (s : ℕ → ℤ) (hs : ∀ n, (s n : ℚ) = ∑ i, c i * v i ^ n)
    {d : ℕ} (hd : HasRecurrence s d) : h ≤ d := by
  rcases hd with ⟨E, rfl, _, N, hE⟩
  have heval : ∀ x : ℚ, E.charPoly.eval x = x ^ E.order - ∑ k : Fin E.order, E.coeffs k * x ^ (k : ℕ) := by
    intro x
    rw [LinearRecurrence.charPoly, eval_sub, eval_monomial, eval_finsetSum]
    simp only [one_mul, eval_monomial]
  have hz : (fun i => c i * v i ^ N * E.charPoly.eval (v i)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hv
    intro k
    have hh := hE (k : ℕ)
    simp only [hs] at hh
    simp_rw [pow_add] at hh
    simp_rw [heval, mul_sub, mul_sum, sub_mul, sum_mul]
    rw [sum_sub_distrib]
    have hswap : (∑ i : Fin h, ∑ j : Fin E.order,
      c i * v i ^ N * (E.coeffs j * v i ^ (j : ℕ)) * v i ^ (k : ℕ)) =
      ∑ j : Fin E.order, E.coeffs j * ∑ i : Fin h,
        c i * (v i ^ (k : ℕ) * v i ^ (j : ℕ) * v i ^ N) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [hswap]
    have hleft : (∑ i : Fin h, c i * v i ^ N * v i ^ E.order * v i ^ (k : ℕ)) =
      ∑ i : Fin h, c i * (v i ^ (k : ℕ) * v i ^ E.order * v i ^ N) := by
      apply sum_congr rfl
      intro i _
      ring
    rw [hleft, sub_eq_zero]
    exact hh
  have hroots : ∀ i, E.charPoly.IsRoot (v i) := by
    intro i
    have hz' := congrFun hz i
    change c i * v i ^ N * E.charPoly.eval (v i) = 0 at hz'
    exact (mul_eq_zero.mp hz').resolve_left (mul_ne_zero (hc i) (pow_ne_zero _ (hv0 i)))
  have hcard := Polynomial.card_le_degree_of_subset_roots (p := E.charPoly)
    (Z := univ.image v) (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots E.charPoly_monic.ne_zero).mpr (hroots i))
  simpa [card_image_of_injective _ hv, charPoly_natDegree] using hcard


private lemma polynomial_recurrence (P : ℚ[X]) (hP : P.Monic) :
    ∃ E : LinearRecurrence ℚ, E.order = P.natDegree ∧ E.charPoly = P := by
  let E : LinearRecurrence ℚ := ⟨P.natDegree, fun i => - P.coeff i⟩
  refine ⟨E, rfl, ?_⟩
  dsimp [LinearRecurrence.charPoly, E]
  simp only [monomial_neg, sum_neg_distrib, sub_neg_eq_add]
  rw [← C_mul_X_pow_eq_monomial, C_1, one_mul]
  conv_rhs => rw [hP.as_sum]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  rw [← C_mul_X_pow_eq_monomial]

private lemma exponential_upper {h : ℕ} (v c : Fin h → ℚ)
    (hv0 : ∀ i, v i ≠ 0)
    (s : ℕ → ℤ) (hs : ∀ n, (s n : ℚ) = ∑ i, c i * v i ^ n) :
    HasRecurrence s h := by
  classical
  let P : ℚ[X] := ∏ i, (X - C (v i))
  have hmon : P.Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hdeg : P.natDegree = h := by
    simpa only [P, Finset.card_univ, Fintype.card_fin] using
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card (Finset.univ : Finset (Fin h)) v
  obtain ⟨E, horder, hchar⟩ := polynomial_recurrence P hmon
  have hc0 : P.coeff 0 ≠ 0 := by
    dsimp [P]
    rw [coeff_zero_prod]
    apply prod_ne_zero_iff.mpr
    intro i _
    simpa using hv0 i
  refine ⟨E, horder.trans hdeg, ?_, 0, ?_⟩
  · intro hpos hzero
    have hcoeff := congrArg (fun p : ℚ[X] => p.coeff 0) hchar
    simp [LinearRecurrence.charPoly, coeff_monomial, ne_of_gt hpos, hzero,
      show (∑ i : Fin E.order, (monomial (i : ℕ) (E.coeffs i) : ℚ[X])).coeff 0 =
        E.coeffs ⟨0, hpos⟩ by
          simp only [finsetSum_coeff, coeff_monomial]
          rw [sum_eq_single ⟨0, hpos⟩]
          · simp
          · intro b _ hb; split_ifs with h
            · exact (hb (Fin.ext h)).elim
            · rfl
          · simp] at hcoeff
    exact hc0 hcoeff.symm
  · have hgeom : ∀ i, E.IsSolution (fun n => v i ^ n) := by
      intro i
      rw [E.geom_sol_iff_root_charPoly, hchar]
      change P.eval (v i) = 0
      dsimp [P]
      rw [eval_prod]
      apply prod_eq_zero (mem_univ i)
      simp
    have hsum : E.IsSolution (fun n => ∑ i, c i * v i ^ n) := by
      have ht : (∑ i, c i • (fun n => v i ^ n)) ∈ E.solSpace := by
        exact Submodule.sum_smul_mem E.solSpace c (fun i _ => hgeom i)
      change E.IsSolution (∑ i, c i • (fun n => v i ^ n)) at ht
      have heq : (∑ i, c i • (fun n => v i ^ n)) = (fun n => ∑ i, c i * v i ^ n) := by
        exact Finset.sum_fn Finset.univ (fun i => c i • (fun n : ℕ => v i ^ n))
      rwa [heq] at ht
    simpa only [Nat.add_zero, hs] using hsum

private lemma exponential_rank {h : ℕ} (v c : Fin h → ℚ)
    (hv : Function.Injective v) (hv0 : ∀ i, v i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (s : ℕ → ℤ) (hs : ∀ n, (s n : ℚ) = ∑ i, c i * v i ^ n) : rank s = h := by
  apply le_antisymm
  · exact Nat.sInf_le (exponential_upper v c hv0 s hs)
  · apply le_csInf ⟨h, exponential_upper v c hv0 s hs⟩
    intro d hd
    exact exponential_lower v c hv hv0 hc s hs hd


private lemma exponential_rank_fintype {ι : Type*} [Fintype ι] (v c : ι → ℚ)
    (hv : Function.Injective v) (hv0 : ∀ i, v i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (s : ℕ → ℤ) (hs : ∀ n, (s n : ℚ) = ∑ i, c i * v i ^ n) :
    rank s = Fintype.card ι := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply exponential_rank (fun i => v (e i)) (fun i => c (e i))
    (hv.comp e.injective) (fun i => hv0 (e i)) (fun i => hc (e i)) s
  intro n
  rw [hs]
  exact (e.sum_comp (fun i => c i * v i ^ n)).symm

private lemma exponential_upper_fintype {ι : Type*} [Fintype ι] (v c : ι → ℚ)
    (hv0 : ∀ i, v i ≠ 0)
    (s : ℕ → ℤ) (hs : ∀ n, (s n : ℚ) = ∑ i, c i * v i ^ n) :
    HasRecurrence s (Fintype.card ι) := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply exponential_upper (fun i => v (e i)) (fun i => c (e i))
    (fun i => hv0 (e i)) s
  intro n
  rw [hs]
  exact (e.sum_comp (fun i => c i * v i ^ n)).symm

private lemma polynomial_support_rank (P : ℚ[X]) (M : ℕ) (s : ℕ → ℤ)
    (hs : ∀ n, (s n : ℚ) = (-1 : ℚ) ^ M * (2 : ℚ) ^ (M * n) * P.eval ((2 : ℚ)^n)) :
    rank s = P.support.card ∧ HasRecurrence s P.support.card := by
  classical
  let v : P.support → ℚ := fun j => (2 : ℚ) ^ (M + (j : ℕ))
  let c : P.support → ℚ := fun j => (-1 : ℚ) ^ M * P.coeff j
  have hv0 : ∀ j, v j ≠ 0 := fun j => pow_ne_zero _ (by norm_num)
  have hc : ∀ j, c j ≠ 0 := by
    intro j
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mem_support_iff.mp j.property)
  have hv : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    have he : M + (i : ℕ) = M + (j : ℕ) :=
      (pow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)) hij
    omega
  have heq : ∀ n, (s n : ℚ) = ∑ j : P.support, c j * v j ^ n := by
    intro n
    rw [hs, P.eval_eq_sum, Polynomial.sum]
    dsimp only [v, c]
    rw [← Finset.sum_coe_sort P.support (fun j : ℕ => P.coeff j * ((2 : ℚ) ^ n) ^ j), mul_sum]
    apply sum_congr rfl
    intro j hj
    simp only [← pow_mul, pow_add]
    rw [mul_comm n (j : ℕ)]
    ring
  constructor
  · simpa using exponential_rank_fintype v c hv hv0 hc s heq
  · simpa using exponential_upper_fintype v c hv0 s heq

end D5.S1.Recurrence.RowlandSistosBarronRankSequences


open Finset Polynomial
namespace D5.S1.Recurrence.RowlandSistosBarronRankSequences.RSBPoly
noncomputable section

private def B : (ℚ[X])[X] := 1 + X - C (X : ℚ[X]) * X ^ 2

private lemma eval_A (p : ℚ) (M j : ℕ) : (((B ^ M).coeff j)).eval p = ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff j := by
  rw [← coe_evalRingHom, ← coeff_map]
  simp [B, Polynomial.trinomial, sub_eq_add_neg]

private lemma F_power_coeff_rec (p : ℚ) (M j : ℕ) :
    ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ (M + 1)).coeff j = ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff j +
      (if 1 ≤ j then ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff (j - 1) else 0) -
      p * (if 2 ≤ j then ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff (j - 2) else 0) := by
  have he : (Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ (M + 1) = (Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M + (Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M * X - C p * ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M * X ^ 2) := by
    rw [pow_succ, Polynomial.trinomial]
    simp only [pow_zero, pow_one, C_1, one_mul, C_neg]
    ring
  rw [he, coeff_sub, coeff_add, coeff_C_mul]
  have hX (Q : ℚ[X]) : (Q * X).coeff j = if 1 ≤ j then Q.coeff (j - 1) else 0 := by
    rw [← pow_one (X : ℚ[X]), coeff_mul_X_pow']
  rw [hX, coeff_mul_X_pow']


private lemma trinomial_coeff_rec (M j : ℕ) :
    ((1 + X + X ^ 2 : ℚ[X]) ^ (M + 1)).coeff j =
      ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff j +
      (if 1 ≤ j then ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff (j - 1) else 0) +
      (if 2 ≤ j then ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff (j - 2) else 0) := by
  simpa only [Polynomial.trinomial, pow_zero, pow_one, C_1, neg_neg, one_mul,
    neg_one_mul, sub_neg_eq_add] using F_power_coeff_rec (-1) M j


private lemma trinomial_nonneg (M j : ℕ) : 0 ≤ ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff j := by
  have heq : (1 + X + X ^ 2 : ℚ[X]) ^ M =
      (((1 + X + X ^ 2 : ℕ[X]) ^ M).map (Nat.castRingHom ℚ)) := by
    simp
  rw [heq, coeff_map]
  exact Nat.cast_nonneg _

private lemma trinomial_pos (M j : ℕ) (hj : j ≤ 2 * M) :
    0 < ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff j := by
  induction M generalizing j with
  | zero =>
    have : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp
  | succ M ih =>
    rw [trinomial_coeff_rec]
    have hn0 := trinomial_nonneg M j
    have hn1 : 0 ≤ (if 1 ≤ j then ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff (j - 1) else 0) := by
      exact ite_nonneg (trinomial_nonneg M (j - 1)) le_rfl
    have hn2 : 0 ≤ (if 2 ≤ j then ((1 + X + X ^ 2 : ℚ[X]) ^ M).coeff (j - 2) else 0) := by
      exact ite_nonneg (trinomial_nonneg M (j - 2)) le_rfl
    by_cases h : j ≤ 2 * M
    · have hpos := ih j h
      linarith
    · by_cases h2 : j = 2 * M + 1
      · have hj1 : 1 ≤ j := h2 ▸ Nat.le_add_left 1 (2 * M)
        have hprev : j - 1 ≤ 2 * M := Nat.sub_le_of_le_add h2.le
        rw [ite_eq_left hj1]
        have hpos := ih _ hprev
        linarith
      · have hj2 : 2 ≤ j := by omega
        have hprev : j - 2 ≤ 2 * M := Nat.sub_le_of_le_add hj
        rw [ite_eq_left hj2, ite_eq_left (by omega : 1 ≤ j)]
        have hpos := ih _ hprev
        have hn1 := trinomial_nonneg M (j - 1)
        linarith

private lemma A_ne_zero (M j : ℕ) (hj : j ≤ 2 * M) : ((B ^ M).coeff j) ≠ 0 := by
  intro hz
  have he := eval_A (-1) M j
  rw [hz] at he
  have hp := trinomial_pos M j hj
  have hF : (Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(-1 : ℚ))) = (1 + X + X ^ 2 : ℚ[X]) := by simp [Polynomial.trinomial]
  rw [hF] at he
  simp only [eval_zero] at he
  linarith



private lemma low_coeffs (p : ℚ) (M : ℕ) :
    ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff 0 = 1 ∧ ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff 1 = (M : ℚ) ∧
      ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).coeff 2 = (M : ℚ) * ((M : ℚ) - 1) / 2 - p * M := by
  induction M with
  | zero => simp [coeff_one]
  | succ M ih =>
    simp only [F_power_coeff_rec, ih.1, ih.2.1, ih.2.2]
    norm_num
    ring

private lemma cancellation (p : ℕ) : ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ (2 * p + 1)).coeff 2 = 0 := by
  rw [(low_coeffs (p : ℚ) (2 * p + 1)).2.2]
  push_cast
  ring

private lemma finite_bad_parameter (M : ℕ) :
    {p : ℕ | ∃ j ≤ 2 * M, ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).coeff j = 0}.Finite := by
  classical
  have hfinite : ∀ j ∈ range (2 * M + 1),
      {p : ℕ | ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).coeff j = 0}.Finite := by
    intro j hj
    have hh := Polynomial.finite_setOfPred_isRoot (A_ne_zero M j (by have := mem_range.mp hj; omega))
    have hinj : Function.Injective (fun p : ℕ => (p : ℚ)) := Nat.cast_injective
    have hf := hh.preimage hinj.injOn
    simpa only [Set.preimage_ofPred_eq, Polynomial.IsRoot.def, eval_A] using hf
  have hf := (range (2 * M + 1)).finite_toSet.biUnion hfinite
  apply hf.subset
  intro p hp
  obtain ⟨j, hj, hz⟩ := hp
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨j, Finset.mem_range.mpr (by omega), hz⟩

end
end D5.S1.Recurrence.RowlandSistosBarronRankSequences.RSBPoly

namespace D5.S1.Recurrence.RowlandSistosBarronRankSequences
open RSBPoly

private def family (p n : ℕ) : ℤ := (p : ℤ) * 8 ^ n - 4 ^ n - 2 ^ n

private lemma family_closed (p n : ℕ) : (family p n : ℚ) =
    (-1 : ℚ) * (2 : ℚ) ^ n * ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ)))).eval ((2 : ℚ) ^ n) := by
  have h8 : (8 : ℚ) ^ n = ((2 : ℚ) ^ n) ^ 3 := by
    rw [← pow_mul, mul_comm n 3, pow_mul]
    norm_num
  have h4 : (4 : ℚ) ^ n = ((2 : ℚ) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  simp only [family, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_pow,
    Int.cast_ofNat, Polynomial.trinomial, eval_add, eval_X, eval_mul, eval_C, eval_pow]
  rw [h8, h4]
  ring

private lemma family_power_closed (p M n : ℕ) : ((family p n ^ M : ℤ) : ℚ) =
    (-1 : ℚ) ^ M * (2 : ℚ) ^ (M * n) * ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).eval ((2 : ℚ) ^ n) := by
  rw [Int.cast_pow, family_closed]
  simp only [mul_pow, eval_pow, ← pow_mul]
  rw [mul_comm n M]

private lemma family_power_rank (p M : ℕ) :
    rank (fun n => family p n ^ M) = ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).support.card ∧
    HasRecurrence (fun n => family p n ^ M) ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).support.card := by
  exact polynomial_support_rank _ _ _ (family_power_closed p M)

private lemma support_F (p : ℕ) (hp : 0 < p) : ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ)))).support = {0, 1, 2} := by
  exact Polynomial.trinomial_support (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (neg_ne_zero.mpr (by exact_mod_cast hp.ne'))

private lemma family_rank_three (p : ℕ) (hp : 3 ≤ p) : rank (family p) = 3 ∧ IsConstantRecursive (family p) := by
  have h := family_power_rank p 1
  simp only [pow_one] at h
  rw [support_F p (by omega)] at h
  norm_num at h
  exact ⟨h.1, ⟨3, h.2⟩⟩

private lemma power_degree_bound (p : ℚ) (M : ℕ) : ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).natDegree ≤ 2 * M := by
  calc
    ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p)) ^ M).natDegree ≤ M * ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-p))).natDegree := natDegree_pow_le
    _ ≤ M * 2 := by
      apply Nat.mul_le_mul_left
      simp only [Polynomial.trinomial, pow_zero, pow_one, C_1, one_mul, C_neg, neg_mul, ← sub_eq_add_neg]
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · apply (natDegree_add_le _ _).trans
        exact max_le (by simp) (by simp)
      · apply (natDegree_C_mul_le _ _).trans
        simp
    _ = 2 * M := Nat.mul_comm _ _

private lemma power_full_rank (p M : ℕ)
    (hnz : ∀ j ≤ 2 * M, ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).coeff j ≠ 0) :
    rank (fun n => family p n ^ M) = 2 * M + 1 := by
  rw [(family_power_rank p M).1]
  have hsupp : ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ M).support = range (2 * M + 1) := by
    ext j
    simp only [mem_support_iff, mem_range]
    constructor
    · intro hj
      have := le_natDegree_of_ne_zero hj
      have := power_degree_bound (p : ℚ) M
      omega
    · intro hj
      exact hnz j (by omega)
  rw [hsupp, card_range]

end D5.S1.Recurrence.RowlandSistosBarronRankSequences

namespace D5.S1.Recurrence.RowlandSistosBarronRankSequences
open RSBPoly

private lemma power_cancellation_rank (p : ℕ) :
    rank (fun n => family p n ^ (2 * p + 1)) ≤ 2 * (2 * p + 1) := by
  classical
  rw [(family_power_rank p (2 * p + 1)).1]
  have hsupp : ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(p : ℚ))) ^ (2 * p + 1)).support ⊆ (range (2 * (2 * p + 1) + 1)).erase 2 := by
    intro j hj
    simp only [mem_erase, mem_range]
    constructor
    · intro he
      subst j
      exact (mem_support_iff.mp hj) (cancellation p)
    · have h1 := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
      have h2 := power_degree_bound (p : ℚ) (2 * p + 1)
      omega
  have hc := card_le_card hsupp
  have htwo : 2 ∈ range (2 * (2 * p + 1) + 1) := by simp only [mem_range]; omega
  rw [card_erase_of_mem htwo, card_range] at hc
  omega

private lemma finite_rank_sequence_fibre (R : ℕ+ → ℕ) :
    {q : ℕ | 3 ≤ q ∧ rankSequence (family q) = R}.Finite := by
  classical
  by_cases hx : ∃ p : ℕ, 3 ≤ p ∧ rankSequence (family p) = R
  · obtain ⟨p, hp, hpR⟩ := hx
    apply (finite_bad_parameter (2 * p + 1)).subset
    intro q hq
    change ∃ j ≤ 2 * (2 * p + 1), ((Polynomial.trinomial 0 1 2 (1 : ℚ) 1 (-(q : ℚ))) ^ (2 * p + 1)).coeff j = 0
    by_contra hh
    push Not at hh
    have hfull := power_full_rank q (2 * p + 1) hh
    have hcancel := power_cancellation_rank p
    have heq := congrFun (hq.2.trans hpR.symm) (⟨2 * p + 1, by omega⟩ : ℕ+)
    change rank (fun n => family q n ^ (2 * p + 1)) =
      rank (fun n => family p n ^ (2 * p + 1)) at heq
    omega
  · apply Set.finite_empty.subset
    intro p hp
    exact (hx ⟨p, hp⟩).elim

theorem result : ¬ D5.S1.Recurrence.RowlandSistosBarronRankSequences.claim := by
  classical
  intro hclaim
  let S := {R : ℕ+ → ℕ | ∃ s : ℕ → ℤ, IsConstantRecursive s ∧ rank s = 3 ∧ R = rankSequence s}
  have hS : S.Finite := hclaim 3 (by omega)
  have hf : (⋃ R ∈ S, {q : ℕ | 3 ≤ q ∧ rankSequence (family q) = R}).Finite :=
    hS.biUnion (fun R _ => finite_rank_sequence_fibre R)
  have hdomain : {p : ℕ | p.Prime ∧ 3 ≤ p}.Finite := by
    apply hf.subset
    intro p hp
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨rankSequence (family p), ?_, hp.2, rfl⟩
    obtain ⟨hrank, hrec⟩ := family_rank_three p hp.2
    exact ⟨family p, hrec, hrank, rfl⟩
  obtain ⟨B, hB⟩ := hdomain.bddAbove
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max (B + 1) 3)
  have hp3 : 3 ≤ p := le_trans (le_max_right _ _) hp
  have hpB : B + 1 ≤ p := le_trans (le_max_left _ _) hp
  have hle : p ≤ B := hB ⟨hprime, hp3⟩
  omega

end D5.S1.Recurrence.RowlandSistosBarronRankSequences
