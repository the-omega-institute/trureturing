/- GID: D5/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/QStirling/SaganSwansonBottomHeavy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All four unshifted q-Stirling coefficient families are bottom heavy. -/

/-
result:
  proof_shape: content (same-module expansion includes interval-layer inductions)
  escape_witness: none
  admission_basis: open-problem-resolution (#21443; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22255
Direct frozen dependencies:
  D5/S0/Certificates/Polynomials/QProductNecessityRefutation.qInteger
  statement_id: sha256:1f34579ee25223e26a60c00621daa9d6549df95a00359f2c551a918df36f1577
The q-integer is reused at its owner. SB and cB denote the source's S_B and c_B;
only their identifier spelling changes. Each recurrence has the source's body.

Private theorem classification (dependency above, after same-module expansion):
  q_zero: proof_shape: bind-only; consumer: cone_mul; escape_witness: none
  q_one: proof_shape: bind-only; consumers: q_succ, q_head, interval_mul, cone_one; escape_witness: none
  q_succ: proof_shape: bind-only; consumer: q_peel; escape_witness: none
  q_add: proof_shape: bind-only; consumers: q_succ, q_head, q_peel; escape_witness: none
  q_head: proof_shape: bind-only; consumer: q_peel; escape_witness: none
  q_peel: proof_shape: bind-only; consumer: interval_mul; escape_witness: none
  q_coeff: proof_shape: bind-only; consumers: centered_support, centered_symm,
    centered_rise, cone_mul; escape_witness: none
  centered_support: proof_shape: content; consumers: centered_symm, centered_ambient; escape_witness: none
  centered_symm: proof_shape: content; consumers: centered_ambient, cone_ambient; escape_witness: none
  centered_rise: proof_shape: content; consumer: centered_ambient; escape_witness: none
  interval_mul: proof_shape: content; consumer: centered_mul_interval; escape_witness: none
  centered_mul_interval: proof_shape: content; consumer: cone_mul; escape_witness: none
  centered_ambient: proof_shape: content; consumer: cone_ambient; escape_witness: none
  cone_one: proof_shape: bind-only; consumer: families_cone; escape_witness: none
  cone_mul: proof_shape: content; consumer: families_cone; escape_witness: none
  cone_ambient: proof_shape: content; consumer: result; escape_witness: none
  families_cone: proof_shape: content; consumer: result; escape_witness: none
-/

import Mathlib.Algebra.Polynomial.Degree.Operations
import D5.S0.Certificates.Polynomials.QProductNecessityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QStirling.SaganSwansonBottomHeavy

open Polynomial
open D5.S0.Certificates.Polynomials.QProductNecessityRefutation (qInteger)

/-! The unshifted polynomials of arXiv:2205.14078v1, equations (2), (5), (8), (9).
The existing D5 owner supplies [a]_q = sum_{j<a} X^j, including [0]_q = 0.
The negative-k branch is explicitly zero, as follows from the common initial
condition and the source recurrences. Thus Int.toNat is used only for a
nonnegative bracket argument. No polynomial value is assigned to a negative
q-integer, for which the source uses a Laurent expression. -/

/-- S[0,k] = delta_{0,k}; S[n+1,k] = S[n,k-1] + [k] S[n,k]. -/
noncomputable def S : ℕ → ℤ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => if k < 0 then 0 else S n (k - 1) + qInteger k.toNat * S n k

/-- c[0,k] = delta_{0,k}; c[n+1,k] = c[n,k-1] + [n] c[n,k]. -/
noncomputable def c : ℕ → ℤ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => c n (k - 1) + qInteger n * c n k

/-- SB[0,k] = delta_{0,k}; SB[n+1,k] = SB[n,k-1] + [2k+1] SB[n,k]. -/
noncomputable def SB : ℕ → ℤ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
      if k < 0 then 0 else SB n (k - 1) + qInteger (2 * k + 1).toNat * SB n k

/-- cB[0,k] = delta_{0,k}; cB[n+1,k] = cB[n,k-1] + [2n+1] cB[n,k]. -/
noncomputable def cB : ℕ → ℤ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => cB n (k - 1) + qInteger (2 * n + 1) * cB n k

/-- Conjecture 7.6: compare coefficients at reflected exponents about the actual
polynomial degree, for all four families, every n >= 0 and every integer k.
For the zero polynomial natDegree is 0 and the strict comparison is vacuous. -/
def claim : Prop :=
  ∀ (n : ℕ) (k : ℤ) (p : ℕ[X]),
    (p = S n k ∨ p = c n k ∨ p = SB n k ∨ p = cB n k) →
      ∀ (r : ℕ), 2 * r < p.natDegree → p.coeff (p.natDegree - r) ≤ p.coeff r

end D5.S3.Combinatorics.QStirling.SaganSwansonBottomHeavy

namespace D5.S3.Combinatorics.QStirling.SaganSwansonBottomHeavy
open Polynomial
open D5.S0.Certificates.Polynomials.QProductNecessityRefutation (qInteger)

private theorem q_zero : qInteger 0 = 0 := by
  exact toFinsupp_eq_zero.mp rfl

private theorem q_one : qInteger 1 = 1 := by
  exact Eq.symm (ext (congrFun rfl))

private theorem q_add (a b : ℕ) : qInteger (a + b) = qInteger a + X ^ a * qInteger b := by
  simp [qInteger, Finset.sum_range_add, pow_add, Finset.mul_sum]

private theorem q_succ (a : ℕ) : qInteger (a + 1) = qInteger a + X ^ a := by
  simpa only [q_one, mul_one] using q_add a 1

private theorem q_head (a : ℕ) : qInteger (a + 1) = 1 + X * qInteger a := by
  simpa [q_one, Nat.add_comm] using q_add 1 a

private theorem q_peel (a b : ℕ) :
    qInteger (a + 1) * qInteger (b + 1) =
      qInteger (a + b + 1) + X * (qInteger a * qInteger b) := by
  have h := q_add (a + 1) b
  rw [show a + 1 + b = a + b + 1 by omega] at h
  rw [h, q_head b, q_succ a]
  ring

private theorem q_coeff (a k : ℕ) : (qInteger a).coeff k = if k < a then 1 else 0 := by
  simp [qInteger, coeff_X_pow, Finset.mem_range]

private inductive Centered : ℕ → ℕ[X] → Prop
  | interval (d : ℕ) : Centered d (qInteger (d + 1))
  | add {d : ℕ} {p q : ℕ[X]} : Centered d p → Centered d q → Centered d (p + q)
  | shift {d : ℕ} {p : ℕ[X]} : Centered d p → Centered (d + 2) (X * p)

private theorem centered_support {d : ℕ} {p : ℕ[X]} (h : Centered d p) :
    ∀ i : ℕ, d < i → p.coeff i = 0 := by
  induction h with
  | interval d =>
      intro i hi
      simp [q_coeff, show ¬ i < d + 1 by omega]
  | add hp hq ihp ihq =>
      intro i hi
      simp [coeff_add, ihp i hi, ihq i hi]
  | @shift d p hp ih =>
      intro i hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      simpa only [coeff_X_mul] using ih j (by omega)

private theorem centered_symm {d : ℕ} {p : ℕ[X]} (h : Centered d p) :
    ∀ i j : ℕ, i + j = d → p.coeff i = p.coeff j := by
  induction h with
  | interval d =>
      intro i j hij
      simp [q_coeff, show i < d + 1 by omega, show j < d + 1 by omega]
  | add hp hq ihp ihq =>
      intro i j hij
      simp only [coeff_add, ihp i j hij, ihq i j hij]
  | @shift d p hp ih =>
      intro i j hij
      cases i with
      | zero =>
          have hj : j = (d + 1) + 1 := by omega
          simp [hj, coeff_X_mul, centered_support hp (d + 1) (by omega)]
      | succ i =>
          cases j with
          | zero =>
              have hi : i = d + 1 := by exact Nat.add_right_cancel hij
              simp [hi, coeff_X_mul, centered_support hp (d + 1) (by omega)]
          | succ j =>
              simpa only [coeff_X_mul] using ih i j (by omega)

private theorem centered_rise {d : ℕ} {p : ℕ[X]} (h : Centered d p) :
    ∀ i j : ℕ, i ≤ j → i + j ≤ d → p.coeff i ≤ p.coeff j := by
  induction h with
  | interval d =>
      intro i j hij hd
      simp [q_coeff, show i < d + 1 by omega, show j < d + 1 by omega]
  | add hp hq ihp ihq =>
      intro i j hij hd
      simpa only [coeff_add] using Nat.add_le_add (ihp i j hij hd) (ihq i j hij hd)
  | @shift d p hp ih =>
      intro i j hij hd
      cases i with
      | zero => simp
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simpa only [coeff_X_mul] using ih i j (by omega) (by omega)

private theorem interval_mul (a b : ℕ) :
    Centered (a + b) (qInteger (a + 1) * qInteger (b + 1)) := by
  induction a generalizing b with
  | zero => simpa [q_one] using Centered.interval b
  | succ a ih =>
      cases b with
      | zero => simpa [q_one] using Centered.interval (a + 1)
      | succ b =>
          rw [q_peel]
          have h1 := Centered.interval ((a + 1) + (b + 1))
          have h2 := Centered.shift (ih b)
          have he : a + b + 2 = (a + 1) + (b + 1) := by
            exact Eq.symm (Nat.add_right_comm a 1 (b + 1))
          rw [he] at h2
          exact Centered.add h1 h2

private theorem centered_mul_interval {d : ℕ} {p : ℕ[X]} (h : Centered d p) (a : ℕ) :
    Centered (d + a) (p * qInteger (a + 1)) := by
  induction h with
  | interval d => exact interval_mul d a
  | add hp hq ihp ihq =>
      simpa only [add_mul] using Centered.add ihp ihq
  | @shift d p hp ih =>
      have hs := Centered.shift ih
      have he : d + a + 2 = d + 2 + a := by exact Nat.add_right_comm d a 2
      rw [he] at hs
      simpa only [mul_assoc] using hs

private theorem centered_ambient {d : ℕ} {p : ℕ[X]} (h : Centered d p)
    (D r : ℕ) (hd : d ≤ D) (hr : 2 * r < D) : p.coeff (D - r) ≤ p.coeff r := by
  by_cases hs : d < D - r
  · rw [centered_support h (D - r) hs]
    exact Nat.zero_le _
  · have ht : d - (D - r) ≤ r := by omega
    have htr : d - (D - r) + r ≤ d := by omega
    have he := centered_symm h (D - r) (d - (D - r)) (by omega)
    rw [he]
    exact centered_rise h _ _ ht htr

private inductive Cone : ℕ[X] → Prop
  | zero : Cone 0
  | atom {d : ℕ} {p : ℕ[X]} : Centered d p → 0 < p.coeff 0 → Cone p
  | add {p q : ℕ[X]} : Cone p → Cone q → Cone (p + q)

private theorem cone_one : Cone 1 := by
  apply Cone.atom (d := 0)
  · simpa [q_one] using Centered.interval 0
  · simp

private theorem cone_mul (a : ℕ) {p : ℕ[X]} (h : Cone p) : Cone (qInteger a * p) := by
  cases a with
  | zero => simpa [q_zero] using Cone.zero
  | succ a =>
      induction h with
      | zero => simpa using Cone.zero
      | @atom d p hp hc =>
          rw [mul_comm]
          apply Cone.atom (centered_mul_interval hp a)
          simpa [mul_coeff_zero, q_coeff] using hc
      | add hp hq ihp ihq =>
          simpa only [mul_add] using Cone.add ihp ihq

private theorem cone_ambient {p : ℕ[X]} (h : Cone p) :
    ∀ D r : ℕ, (∀ i : ℕ, D < i → p.coeff i = 0) →
      2 * r < D → p.coeff (D - r) ≤ p.coeff r := by
  induction h with
  | zero => simp
  | @atom d p hp hc =>
      intro D r hb hr
      have hd : d ≤ D := by
        by_contra hn
        have hz := hb d (by omega)
        have he := centered_symm hp d 0 (by omega)
        omega
      exact centered_ambient hp D r hd hr
  | @add p q hp hq ihp ihq =>
      intro D r hb hr
      have hbp : ∀ i : ℕ, D < i → p.coeff i = 0 := by
        exact fun i hi => Nat.eq_zero_of_add_eq_zero_right (hb i hi)
      have hbq : ∀ i : ℕ, D < i → q.coeff i = 0 := by
        exact fun i hi => Nat.eq_zero_of_add_eq_zero_left (hb i hi)
      simpa only [coeff_add] using Nat.add_le_add (ihp D r hbp hr) (ihq D r hbq hr)

private theorem families_cone (n : ℕ) (k : ℤ) :
    Cone (S n k) ∧ Cone (c n k) ∧ Cone (SB n k) ∧ Cone (cB n k) := by
  induction n generalizing k with
  | zero =>
      by_cases hk : k = 0
      · simp only [S, c, SB, cB, hk, ite_true]
        exact ⟨cone_one, cone_one, cone_one, cone_one⟩
      · simp only [S, c, SB, cB, hk, ite_false]
        exact ⟨Cone.zero, Cone.zero, Cone.zero, Cone.zero⟩
  | succ n ih =>
      have h0 := ih k
      have h1 := ih (k - 1)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [S]
        split_ifs
        · exact Cone.zero
        · exact Cone.add h1.1 (cone_mul _ h0.1)
      · rw [c]
        exact Cone.add h1.2.1 (cone_mul _ h0.2.1)
      · rw [SB]
        split_ifs
        · exact Cone.zero
        · exact Cone.add h1.2.2.1 (cone_mul _ h0.2.2.1)
      · rw [cB]
        exact Cone.add h1.2.2.2 (cone_mul _ h0.2.2.2)

theorem result : D5.S3.Combinatorics.QStirling.SaganSwansonBottomHeavy.claim := by
  intro n k p hp r hr
  have hc : Cone p := by
    rcases hp with h | h | h | h
    · rw [h]; exact (families_cone n k).1
    · rw [h]; exact (families_cone n k).2.1
    · rw [h]; exact (families_cone n k).2.2.1
    · rw [h]; exact (families_cone n k).2.2.2
  exact cone_ambient hc p.natDegree r
    (fun i hi => coeff_eq_zero_of_natDegree_lt hi) hr


end D5.S3.Combinatorics.QStirling.SaganSwansonBottomHeavy
