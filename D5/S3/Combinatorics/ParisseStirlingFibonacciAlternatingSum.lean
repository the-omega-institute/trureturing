/- GID: D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The alternating Stirling weighted sum of even index terms of a Fibonacci recurrence equals the signed weighted sum of the preceding Stirling row. -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ParisseStirlingFibonacciAlternatingSum

open Finset Polynomial

/-
proof_shape: result: content
escape_witness: the active path carries several intermediate facts, none of them an
  instantiation, projection or normalisation of a pinned upstream statement:
  (i) the functional equation `X * (Q n).comp (-1 - X) = C ((-1) ^ n) * ((1 + X) * Q n)`
      satisfied by the row polynomials of the Stirling numbers of the second kind, proved
      by induction from the differential recurrence;
  (ii) `∑ i ∈ range (m + 1), (m.choose i) * u (i + c) = u (2 * m + c)`, the doubling of the
      index of an arbitrary Fibonacci recurrence under the binomial transform;
  (iii) the transport rules `L u c (X * p) = L u (c + 1) p` and
      `L u c ((1 + X) * p) = L u (c + 2) p` for the pairing with such a sequence, and the
      evaluation `L u 1 ((1 + X) ^ m) = u (2 * m + 1)`;
  (iv) the factorisation `Q l = X * P` for `1 ≤ l` and the cancellation of `X` that turns
      the functional equation into an identity between the composite and `(1 + X) * P`;
  (v) the coefficient reindexing that rewrites the alternating even-index sum as
      `∑ k, (Q l).coeff k * (-1) ^ k * u (2 * k + 1)`, in which the boundary term drops out
      because `Q l` has no constant term.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- The row polynomial of the Stirling numbers of the second kind, `Q n = ∑ m, m! S(n, m) Xᵐ`,
presented through the differential recurrence it satisfies. -/
noncomputable def Q : ℕ → Polynomial ℤ
  | 0 => 1
  | (n + 1) => X * (1 + X) * derivative (Q n) + X * Q n

/-- The pairing of a polynomial with a sequence `u`, shifted by `c`:
`L u c p = ∑ k, p.coeff k * u (k + c)`. -/
noncomputable def L (u : ℕ → ℤ) (c : ℕ) (p : Polynomial ℤ) : ℤ :=
  ∑ k ∈ p.support, p.coeff k * u (k + c)

/-- The Lucas numbers `2, 1, 3, 4, 7, 11, …`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

/-- Conjectures 1 and 2 of Parisse, *Integers* 24 (2024), Article A70. For every `ℓ` the
alternating sum of the Stirling numbers of the second kind of row `ℓ + 1`, weighted by the
factorials and by the even-index Fibonacci numbers, equals `(-1) ^ ℓ` times the plain weighted
sum of row `ℓ`; and the same identity holds with the Lucas numbers in place of the Fibonacci
numbers. Here `S` is `Nat.stirlingSecond` and `F` is `Nat.fib`, so that `F 1 = F 2 = 1`. -/
def claim : Prop :=
  (∀ l : ℕ,
      ∑ m ∈ range (l + 1),
          (-1 : ℤ) ^ m * ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
            * (Nat.fib (2 * m + 2) : ℤ)
        = (-1 : ℤ) ^ l * ∑ m ∈ range (l + 1),
            ((Nat.factorial m * Nat.stirlingSecond l m : ℕ) : ℤ) * (Nat.fib (m + 2) : ℤ))
    ∧ (∀ l : ℕ,
      ∑ m ∈ range (l + 1),
          (-1 : ℤ) ^ m * ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
            * lucas (2 * m + 2)
        = (-1 : ℤ) ^ l * ∑ m ∈ range (l + 1),
            ((Nat.factorial m * Nat.stirlingSecond l m : ℕ) : ℤ) * lucas (m + 2))

/-- Conjectures 1 and 2 of Parisse hold. -/
theorem result : claim := by
  have hQsucc : ∀ n : ℕ, Q (n + 1) = X * (1 + X) * derivative (Q n) + X * Q n :=
    fun _ => rfl
  have hsplit : ∀ p : Polynomial ℤ, X * (1 + X) * p = X * p + X * (X * p) := by
    intro p
    ring
  have hQcoeff : ∀ n m : ℕ,
      (Q n).coeff m = (Nat.factorial m * Nat.stirlingSecond n m : ℕ) := by
    intro n m
    induction n generalizing m with
    | zero =>
      rcases m with _ | m
      · simp [Q]
      · simp [Q, coeff_one, Nat.stirlingSecond_zero_succ]
    | succ p ih =>
      rw [hQsucc, hsplit]
      rcases m with _ | m
      · simp [mul_coeff_zero]
      · rcases m with _ | m
        · simp only [coeff_add, coeff_X_mul, coeff_derivative, ih, mul_coeff_zero, coeff_X_zero,
            zero_mul, Nat.stirlingSecond_succ_succ]
          norm_num [Nat.factorial]
        · simp only [coeff_add, coeff_X_mul, coeff_derivative, ih,
            Nat.stirlingSecond_succ_succ]
          have hf : ((m + 1 + 1).factorial : ℤ)
              = ((m + 1 + 1 : ℕ) : ℤ) * ((m + 1).factorial : ℤ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
          push_cast
          push_cast at hf
          rw [hf]
          ring
  have hQone : Q 1 = X := by
    simp [Q]
  have hQfe : ∀ n : ℕ, 1 ≤ n →
      X * (Q n).comp (-1 - X) = C ((-1 : ℤ) ^ n) * ((1 + X) * Q n) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ p ih =>
      intro _
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        rw [hQone, X_comp]
        simp
        ring
      · have IH := ih hp
        have hcomp : (Q (p + 1)).comp (-1 - X)
            = -(X * (1 + X)) * derivative ((Q p).comp (-1 - X))
              - (1 + X) * ((Q p).comp (-1 - X)) := by
          rw [hQsucc]
          simp only [add_comp, mul_comp, X_comp, one_comp, derivative_comp,
            derivative_sub, derivative_one, derivative_X, derivative_neg]
          ring
        have hder := congrArg derivative IH
        simp only [derivative_mul, derivative_X, derivative_add, derivative_one,
          derivative_C, one_mul, zero_mul, zero_add] at hder
        have hsign : (C ((-1 : ℤ) ^ (p + 1)) : Polynomial ℤ) = -C ((-1 : ℤ) ^ p) := by
          rw [pow_succ]
          simp
        rw [hcomp, hQsucc, hsign]
        linear_combination (-(X * (1 + X)) : Polynomial ℤ) * hder
  have hshift : ∀ l m : ℕ,
      ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
        = (Q l).coeff (m + 1) + (Q l).coeff m := by
    intro l m
    rw [hQcoeff, hQcoeff, Nat.stirlingSecond_succ_succ]
    have hf : ((m + 1).factorial : ℤ) = ((m + 1 : ℕ) : ℤ) * (m.factorial : ℤ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    push_cast
    push_cast at hf
    rw [hf]
    ring
  have hQdeg : ∀ n : ℕ, (Q n).natDegree ≤ n := by
    intro n
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hQcoeff, Nat.stirlingSecond_eq_zero_of_lt hN]
    simp
  have hQne : ∀ l : ℕ, Q l ≠ 0 := by
    intro l h
    have hz := hQcoeff l l
    rw [h, Polynomial.coeff_zero, Nat.stirlingSecond_self, mul_one] at hz
    exact Nat.factorial_ne_zero l (by exact_mod_cast hz.symm)
  have hQzero : ∀ l : ℕ, 1 ≤ l → (Q l).coeff 0 = 0 := by
    intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    rw [hQcoeff]
    simp
  have hQfactor : ∀ l : ℕ, 1 ≤ l → ∃ P : Polynomial ℤ, Q l = X * P := by
    intro l hl
    exact Polynomial.X_dvd_iff.mpr (hQzero l hl)
  have hdegpow : ∀ m : ℕ, ((1 + X : Polynomial ℤ) ^ m).natDegree < m + 1 := by
    intro m
    have h1 : (1 + X : Polynomial ℤ).natDegree ≤ 1 := by
      simpa using Polynomial.natDegree_add_le (1 : Polynomial ℤ) X
    calc ((1 + X : Polynomial ℤ) ^ m).natDegree ≤ m * (1 + X : Polynomial ℤ).natDegree :=
          Polynomial.natDegree_pow_le
      _ ≤ m * 1 := Nat.mul_le_mul_left m h1
      _ < m + 1 := by omega
  have hcompsum : ∀ (r : Polynomial ℤ) (f : ℕ → Polynomial ℤ) (N : ℕ),
      (∑ i ∈ range N, f i).comp r = ∑ i ∈ range N, (f i).comp r := by
    intro r f N
    induction N with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, add_comp, ih]
  have hnegpow : ∀ k : ℕ,
      (-1 - X : Polynomial ℤ) ^ k = C ((-1 : ℤ) ^ k) * (1 + X) ^ k := by
    intro k
    have hC : (C ((-1 : ℤ) ^ k) : Polynomial ℤ) = (-1 : Polynomial ℤ) ^ k := by
      rw [map_pow]
      simp
    rw [hC, show (-1 - X : Polynomial ℤ) = -(1 + X) from by ring, neg_pow]
  have general : ∀ u : ℕ → ℤ, (∀ n : ℕ, u (n + 2) = u n + u (n + 1)) → ∀ l : ℕ,
      ∑ m ∈ range (l + 1),
          (-1 : ℤ) ^ m * ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
            * u (2 * m + 2)
        = (-1 : ℤ) ^ l * ∑ m ∈ range (l + 1),
            ((Nat.factorial m * Nat.stirlingSecond l m : ℕ) : ℤ) * u (m + 2) := by
    intro u hu
    have hLrange : ∀ (c N : ℕ) (p : Polynomial ℤ), p.natDegree < N →
        L u c p = ∑ k ∈ range N, p.coeff k * u (k + c) := by
      intro c N p h
      rw [L]
      refine Finset.sum_subset ?_ ?_
      · intro k hk
        exact Finset.mem_range.mpr (lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
          (Polynomial.mem_support_iff.mp hk)) h)
      · intro k _ hk
        rw [Polynomial.notMem_support_iff.mp hk, zero_mul]
    have hLXmul : ∀ (c N : ℕ) (p : Polynomial ℤ), p.natDegree < N →
        L u c (X * p) = L u (c + 1) p := by
      intro c N p h
      have h1 : (X * p).natDegree < N + 1 := by
        rcases eq_or_ne p 0 with rfl | hp
        · simp
        · rw [Polynomial.natDegree_X_mul hp]; omega
      rw [hLrange c (N + 1) _ h1, hLrange (c + 1) N p h, Finset.sum_range_succ']
      simp only [Polynomial.coeff_X_mul, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
        zero_mul, add_zero]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [show k + 1 + c = k + (c + 1) from by omega]
    have hLadd : ∀ (c N : ℕ) (p q : Polynomial ℤ), p.natDegree < N → q.natDegree < N →
        L u c (p + q) = L u c p + L u c q := by
      intro c N p q hp hq
      have hpq : (p + q).natDegree < N :=
        lt_of_le_of_lt (Polynomial.natDegree_add_le p q) (max_lt hp hq)
      rw [hLrange c N _ hpq, hLrange c N p hp, hLrange c N q hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Polynomial.coeff_add]
      ring
    have hLCmul : ∀ (c N : ℕ) (a : ℤ) (p : Polynomial ℤ), p.natDegree < N →
        L u c (C a * p) = a * L u c p := by
      intro c N a p h
      have h2 : (C a * p).natDegree < N := by
        refine lt_of_le_of_lt ?_ h
        simpa using Polynomial.natDegree_mul_le (p := (C a : Polynomial ℤ)) (q := p)
      rw [hLrange c N _ h2, hLrange c N p h, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Polynomial.coeff_C_mul]
      ring
    have hushift : ∀ k c : ℕ, u (k + c) + u (k + (c + 1)) = u (k + (c + 2)) := by
      intro k c
      rw [show k + (c + 2) = k + c + 2 from by omega, hu,
        show k + (c + 1) = k + c + 1 from by omega]
    have hLshift2 : ∀ (c N : ℕ) (p : Polynomial ℤ), p.natDegree < N →
        L u c ((1 + X) * p) = L u (c + 2) p := by
      intro c N p h
      have hXp : (X * p).natDegree < N + 1 := by
        rcases eq_or_ne p 0 with rfl | hp0
        · simp
        · rw [Polynomial.natDegree_X_mul hp0]; omega
      have hpN : p.natDegree < N + 1 := by omega
      have e : (1 + X) * p = p + X * p := by ring
      rw [e, hLadd c (N + 1) p (X * p) hpN hXp, hLXmul c N p h,
        hLrange c N p h, hLrange (c + 1) N p h, hLrange (c + 2) N p h, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [← hushift k c]
      ring
    have hbinom : ∀ m c : ℕ,
        ∑ i ∈ range (m + 1), ((m.choose i : ℕ) : ℤ) * u (i + c) = u (2 * m + c) := by
      intro m
      induction m with
      | zero => intro c; simp
      | succ p ih =>
        intro c
        rw [Finset.sum_range_succ']
        have e2 : ∑ i ∈ range (p + 1), (((p + 1).choose (i + 1) : ℕ) : ℤ) * u (i + 1 + c)
            = (∑ i ∈ range (p + 1), ((p.choose i : ℕ) : ℤ) * u (i + (c + 1)))
              + ∑ i ∈ range (p + 1), ((p.choose (i + 1) : ℕ) : ℤ) * u (i + 1 + c) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Nat.choose_succ_succ p i, show i + (c + 1) = i + 1 + c from by omega]
          push_cast
          ring
        have e3 : (∑ i ∈ range (p + 1), ((p.choose (i + 1) : ℕ) : ℤ) * u (i + 1 + c))
            + ((p.choose 0 : ℕ) : ℤ) * u (0 + c) = u (2 * p + c) := by
          rw [← Finset.sum_range_succ' (fun i => ((p.choose i : ℕ) : ℤ) * u (i + c)) (p + 1),
            Finset.sum_range_succ, Nat.choose_succ_self]
          simp only [Nat.cast_zero, zero_mul, add_zero]
          exact ih c
        rw [e2]
        have e4 := ih (c + 1)
        have e5 : u (2 * p + (c + 1)) = u (2 * p + c + 1) := by
          rw [show 2 * p + (c + 1) = 2 * p + c + 1 from by ring]
        have e6 : u (2 * (p + 1) + c) = u (2 * p + c + 2) := by
          rw [show 2 * (p + 1) + c = 2 * p + c + 2 from by ring]
        have e7 := hu (2 * p + c)
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at e3 ⊢
        linarith
    have hLpow : ∀ m : ℕ,
        L u 1 ((1 + X : Polynomial ℤ) ^ m) = u (2 * m + 1) := by
      intro m
      rw [hLrange 1 (m + 1) _ (hdegpow m), ← hbinom m 1]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Polynomial.coeff_one_add_X_pow]
    have hLzero : ∀ c : ℕ, L u c 0 = 0 := by
      intro c
      simp [L]
    have hLadd2 : ∀ (c : ℕ) (p q : Polynomial ℤ), L u c (p + q) = L u c p + L u c q := by
      intro c p q
      exact hLadd c (max p.natDegree q.natDegree + 1) p q
        (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _))
    have hLsum : ∀ (c : ℕ) (f : ℕ → Polynomial ℤ) (N : ℕ),
        L u c (∑ i ∈ range N, f i) = ∑ i ∈ range N, L u c (f i) := by
      intro c f N
      induction N with
      | zero => simp [hLzero]
      | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, hLadd2, ih]
    have hLcomp : ∀ (N : ℕ) (p : Polynomial ℤ), p.natDegree < N →
        L u 1 (p.comp (-1 - X))
          = ∑ k ∈ range N, p.coeff k * (-1 : ℤ) ^ k * u (2 * k + 1) := by
      intro N p h
      conv_lhs => rw [Polynomial.as_sum_range' p N h]
      rw [hcompsum, hLsum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Polynomial.monomial_comp, hnegpow, ← mul_assoc, ← Polynomial.C_mul,
        hLCmul 1 (k + 1) _ _ (hdegpow k), hLpow]
    have hAeq : ∀ l : ℕ, 1 ≤ l →
        ∑ m ∈ range (l + 1),
            (-1 : ℤ) ^ m * ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
              * u (2 * m + 2)
          = ∑ k ∈ range (l + 1), (Q l).coeff k * (-1 : ℤ) ^ k * u (2 * k + 1) := by
      intro l hl
      have hc : (Q l).coeff (l + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hQdeg l; omega)
      set g : ℕ → ℤ := fun j => (-1 : ℤ) ^ j * (Q l).coeff j * u (2 * j) with hg
      have h3 : g 0 = 0 := by simp [hg, hQzero l hl]
      have h4 : g (l + 1) = 0 := by simp [hg, hc]
      have hsplitg : ∑ i ∈ range (l + 1), g (i + 1) = ∑ j ∈ range (l + 1), g j := by
        have h1 : ∑ j ∈ range (l + 1 + 1), g j = (∑ i ∈ range (l + 1), g (i + 1)) + g 0 :=
          Finset.sum_range_succ' g (l + 1)
        have h2 : ∑ j ∈ range (l + 1 + 1), g j = (∑ j ∈ range (l + 1), g j) + g (l + 1) :=
          Finset.sum_range_succ g (l + 1)
        rw [h3] at h1
        rw [h4] at h2
        linarith
      have hA : ∑ m ∈ range (l + 1),
          (-1 : ℤ) ^ m * ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
            * u (2 * m + 2)
          = ∑ m ∈ range (l + 1),
            ((-1 : ℤ) ^ m * (Q l).coeff (m + 1) * u (2 * m + 2)
              + (-1 : ℤ) ^ m * (Q l).coeff m * u (2 * m + 2)) := by
        refine Finset.sum_congr rfl ?_
        intro m _
        rw [hshift]
        ring
      have hfirst : (∑ m ∈ range (l + 1),
          (-1 : ℤ) ^ m * (Q l).coeff (m + 1) * u (2 * m + 2))
          + ∑ i ∈ range (l + 1), g (i + 1) = 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero ?_
        intro i _
        simp only [hg]
        rw [show 2 * (i + 1) = 2 * i + 2 from by ring, pow_succ]
        ring
      have hsecond : (∑ m ∈ range (l + 1),
          (-1 : ℤ) ^ m * (Q l).coeff m * u (2 * m + 2))
          = (∑ m ∈ range (l + 1), g m)
            + ∑ k ∈ range (l + 1), (Q l).coeff k * (-1 : ℤ) ^ k * u (2 * k + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro m _
        simp only [hg]
        rw [hu (2 * m)]
        ring
      rw [hA, Finset.sum_add_distrib]
      linarith
    have hBeq : ∀ l : ℕ,
        ∑ m ∈ range (l + 1),
            ((Nat.factorial m * Nat.stirlingSecond l m : ℕ) : ℤ) * u (m + 2)
          = L u 2 (Q l) := by
      intro l
      rw [hLrange 2 (l + 1) (Q l) (Nat.lt_succ_of_le (hQdeg l))]
      exact Finset.sum_congr rfl (fun m _ => by rw [hQcoeff])
    intro l
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · norm_num [Nat.stirlingSecond_self]
    · obtain ⟨P, hP⟩ := hQfactor l hl
      have hP0 : P ≠ 0 := by
        intro h
        exact hQne l (by rw [hP, h, mul_zero])
      have hPd : P.natDegree + 1 ≤ l := by
        have h1 : (X * P).natDegree = P.natDegree + 1 := Polynomial.natDegree_X_mul hP0
        rw [← hP] at h1
        have h2 := hQdeg l
        omega
      have hPdeg : P.natDegree < l + 1 := by omega
      have hQdl : (Q l).natDegree < l + 1 := Nat.lt_succ_of_le (hQdeg l)
      have hXPdeg : ((1 + X : Polynomial ℤ) * P).natDegree < l + 1 := by
        have h1 : (1 + X : Polynomial ℤ).natDegree ≤ 1 := by
          simpa using Polynomial.natDegree_add_le (1 : Polynomial ℤ) X
        have h2 := Polynomial.natDegree_mul_le (p := (1 + X : Polynomial ℤ)) (q := P)
        omega
      have hcancel : (Q l).comp (-1 - X) = C ((-1 : ℤ) ^ l) * ((1 + X) * P) := by
        refine mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℤ)) ?_
        rw [hQfe l hl, hP]
        ring
      calc ∑ m ∈ range (l + 1),
            (-1 : ℤ) ^ m * ((Nat.factorial m * Nat.stirlingSecond (l + 1) (m + 1) : ℕ) : ℤ)
              * u (2 * m + 2)
          = ∑ k ∈ range (l + 1),
              (Q l).coeff k * (-1 : ℤ) ^ k * u (2 * k + 1) := hAeq l hl
        _ = L u 1 ((Q l).comp (-1 - X)) := (hLcomp (l + 1) (Q l) hQdl).symm
        _ = L u 1 (C ((-1 : ℤ) ^ l) * ((1 + X) * P)) := by rw [hcancel]
        _ = (-1 : ℤ) ^ l * L u 1 ((1 + X) * P) := hLCmul 1 (l + 1) _ _ hXPdeg
        _ = (-1 : ℤ) ^ l * L u 3 P := by rw [hLshift2 1 (l + 1) P hPdeg]
        _ = (-1 : ℤ) ^ l * L u 2 (X * P) := by rw [hLXmul 2 (l + 1) P hPdeg]
        _ = (-1 : ℤ) ^ l * L u 2 (Q l) := by rw [← hP]
        _ = (-1 : ℤ) ^ l * ∑ m ∈ range (l + 1),
              ((Nat.factorial m * Nat.stirlingSecond l m : ℕ) : ℤ) * u (m + 2) := by
            rw [hBeq]
  refine ⟨fun l => ?_, fun l => ?_⟩
  · exact general (fun n => (Nat.fib n : ℤ)) (fun n => by rw [Nat.fib_add_two]; push_cast; ring) l
  · exact general lucas (fun n => by simp [lucas]) l

end D5.S3.Combinatorics.ParisseStirlingFibonacciAlternatingSum
