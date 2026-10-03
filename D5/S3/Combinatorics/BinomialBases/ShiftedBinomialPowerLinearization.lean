/- GID: D5/S3/Combinatorics/BinomialBases/ShiftedBinomialPowerLinearization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/ShiftedBinomialPowerLinearization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral linearization of shifted binomial powers with a fixed recursion. -/

/-
result:
  proof_shape: content
  escape_witness: integral_inverse; basis_product
  admission_basis: open-problem-resolution (#12307; Proved)
Direct frozen dependencies: none (Mathlib only).
Private content theorems:
  integral_inverse: content; strong induction constructs and verifies the integral inverse.
  basis_product: content; the live integral inverse constructs integer structure constants.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Nat.Choose.Vandermonde

open Finset Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.BinomialBases.ShiftedBinomialPowerLinearization

/-- Natural arguments cover exactly the source's n = 0, 1, 2, ... . -/
def B (d j n : ℕ) : ℤ := (n + d * j).choose j

/-- Integral unitriangular inverse, recursively in its row index. -/
private def W (d t j : ℕ) : ℤ :=
  if j = t then 1 else
    - ∑ v : Fin t, ((d * t).choose (t - v) : ℤ) * W d v j
termination_by t
decreasing_by exact v.isLt

private theorem integral_inverse (d : ℕ) :
    (∀ t j, t < j → W d t j = 0) ∧
    (∀ t n, (n.choose t : ℤ) =
      ∑ j ∈ range (t + 1), W d t j * B d j n) := by
  have upper : ∀ t j, t < j → W d t j = 0 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro j hj
      rw [W, if_neg (by omega)]
      apply neg_eq_zero.mpr
      apply sum_eq_zero
      intro v hv
      rw [ih v v.isLt j (by omega), mul_zero]
  refine ⟨upper, ?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro n
    have vand (t n : ℕ) : B d t n =
        ∑ v ∈ range (t + 1), ((d * t).choose (t - v) : ℤ) * (n.choose v : ℤ) := by
      have hv := Nat.add_choose_eq n (d * t) t
      rw [sum_antidiagonal_eq_sum_range_succ_mk] at hv
      have hv' : (n + d * t).choose t =
          ∑ v ∈ range (t + 1), (d * t).choose (t - v) * n.choose v :=
        hv.trans (by apply sum_congr rfl; intro v hv; exact Nat.mul_comm _ _)
      dsimp only [B]
      exact_mod_cast hv'
    have wdiag : W d t t = 1 := by rw [W, if_pos rfl]
    have wlow (j : ℕ) (hj : j < t) : W d t j =
        - ∑ v ∈ range t, ((d * t).choose (t - v) : ℤ) * W d v j := by
      rw [W, if_neg (by omega), sum_fin_eq_sum_range]
      congr 1
      apply sum_congr rfl
      intro v hv
      simp [mem_range.mp hv]
    have expand (v : ℕ) (hv : v < t) :
        (n.choose v : ℤ) = ∑ j ∈ range t, W d v j * B d j n := by
      rw [ih v hv n]
      apply sum_subset (range_mono (by omega))
      intro j hjt hjv
      have hvj : v < j := by simp only [mem_range] at hjt hjv; omega
      rw [upper v j hvj, zero_mul]
    have hfirst : B d t n =
        (∑ v ∈ range t, ((d * t).choose (t - v) : ℤ) * (n.choose v : ℤ)) +
        (n.choose t : ℤ) := by
      rw [vand, sum_range_succ]
      simp
    have hdouble : (∑ j ∈ range t, W d t j * B d j n) =
        - ∑ v ∈ range t, ((d * t).choose (t - v) : ℤ) * (n.choose v : ℤ) := by
      calc
        _ = ∑ j ∈ range t,
            (- ∑ v ∈ range t, ((d * t).choose (t - v) : ℤ) * W d v j) * B d j n := by
          apply sum_congr rfl
          intro j hj
          rw [wlow j (mem_range.mp hj)]
        _ = - ∑ j ∈ range t, ∑ v ∈ range t,
            ((d * t).choose (t - v) : ℤ) * (W d v j * B d j n) := by
          simp only [neg_mul, sum_mul, sum_neg_distrib, mul_assoc]
        _ = - ∑ v ∈ range t, ∑ j ∈ range t,
            ((d * t).choose (t - v) : ℤ) * (W d v j * B d j n) := by
          rw [sum_comm]
        _ = _ := by
          congr 1
          apply sum_congr rfl
          intro v hv
          rw [← mul_sum, ← expand v (mem_range.mp hv)]
    rw [sum_range_succ, wdiag, one_mul, hdouble]
    linarith


/-- The B_j coefficient in B_k B_i; no power index occurs here. -/
private def S (d k j i : ℕ) : ℤ :=
  ∑ p ∈ range (k + 1), ∑ q ∈ range (i + 1), ∑ u ∈ range (p + 1),
    (((d * k).choose (k - p) : ℤ) * ((d * i).choose (i - q) : ℤ) *
      ((q + u).choose p : ℤ) * (p.choose u : ℤ)) * W d (q + u) j

private theorem basis_product (d k : ℕ) :
    (∀ i j, i + k < j → S d k j i = 0) ∧
    (∀ i n, B d k n * B d i n =
      ∑ j ∈ range (i + k + 1), S d k j i * B d j n) := by
  have inv := integral_inverse d
  have upper := inv.1
  have inverse := inv.2
  have product (n p q : ℕ) : (n.choose p : ℤ) * (n.choose q : ℤ) =
      ∑ u ∈ range (p + 1),
        ((q + u).choose p : ℤ) * (p.choose u : ℤ) * (n.choose (q + u) : ℤ) := by
    have hn : n.choose p * n.choose q =
        ∑ u ∈ range (p + 1), (q + u).choose p * p.choose u * n.choose (q + u) := by
      by_cases hq : q ≤ n
      · have hv := Nat.add_choose_eq (n - q) q p
        rw [sum_antidiagonal_eq_sum_range_succ_mk, Nat.sub_add_cancel hq] at hv
        rw [hv, sum_mul]
        apply sum_congr rfl
        intro u hu
        have hup : u ≤ p := by simp only [mem_range] at hu; omega
        have h1 : n.choose (q + u) * (q + u).choose q =
            n.choose q * (n - q).choose u := by
          simpa using (Nat.choose_mul (n := n) (k := q + u) (s := q) (by omega))
        have h2 : (q + u).choose p * p.choose u =
            (q + u).choose q * q.choose (p - u) := by
          have hc := Nat.choose_mul (n := q + u) (k := p) (s := u) hup
          rw [Nat.add_sub_cancel] at hc
          have hs : (q + u).choose u = (q + u).choose q := by
            rw [← Nat.choose_symm (by omega : u ≤ q + u), Nat.add_sub_cancel]
          rw [hs] at hc
          exact hc
        calc
          _ = q.choose (p - u) * (n.choose q * (n - q).choose u) := by ring
          _ = q.choose (p - u) * (n.choose (q + u) * (q + u).choose q) := by rw [h1]
          _ = ((q + u).choose q * q.choose (p - u)) * n.choose (q + u) := by ring
          _ = _ := by rw [← h2]
      · have hnq : n < q := by omega
        rw [Nat.choose_eq_zero_of_lt hnq, mul_zero]
        symm
        apply sum_eq_zero
        intro u hu
        rw [Nat.choose_eq_zero_of_lt (by omega : n < q + u), mul_zero]
    exact_mod_cast hn
  have vand (t n : ℕ) : B d t n =
      ∑ v ∈ range (t + 1), ((d * t).choose (t - v) : ℤ) * (n.choose v : ℤ) := by
    have hv := Nat.add_choose_eq n (d * t) t
    rw [sum_antidiagonal_eq_sum_range_succ_mk] at hv
    have hv' : (n + d * t).choose t =
        ∑ v ∈ range (t + 1), (d * t).choose (t - v) * n.choose v :=
      hv.trans (by apply sum_congr rfl; intro v hv; exact Nat.mul_comm _ _)
    dsimp only [B]
    exact_mod_cast hv'
  refine ⟨?_, ?_⟩
  · intro i j hj
    unfold S
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro u hu
    have hju : q + u < j := by
      simp only [mem_range] at hp hq hu
      omega
    rw [upper (q + u) j hju, mul_zero]
  · intro i n
    have extend (p q u : ℕ) (hp : p ≤ k) (hq : q ≤ i) (hu : u ≤ p) :
        (n.choose (q + u) : ℤ) =
          ∑ j ∈ range (i + k + 1), W d (q + u) j * B d j n := by
      rw [inverse]
      apply sum_subset (range_mono (by omega))
      intro j hj hj'
      have hju : q + u < j := by simp only [mem_range] at hj hj'; omega
      rw [upper (q + u) j hju, zero_mul]
    calc
      _ = ∑ p ∈ range (k + 1), ∑ q ∈ range (i + 1),
          ((d * k).choose (k - p) : ℤ) * ((d * i).choose (i - q) : ℤ) *
          ((n.choose p : ℤ) * (n.choose q : ℤ)) := by
        rw [vand k n, vand i n, sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [mul_sum]
        apply sum_congr rfl
        intro q hq
        ring
      _ = ∑ p ∈ range (k + 1), ∑ q ∈ range (i + 1), ∑ u ∈ range (p + 1),
          (((d * k).choose (k - p) : ℤ) * ((d * i).choose (i - q) : ℤ) *
            ((q + u).choose p : ℤ) * (p.choose u : ℤ)) *
          (n.choose (q + u) : ℤ) := by
        simp_rw [product, mul_sum]
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro q hq
        apply sum_congr rfl
        intro u hu
        ring
      _ = ∑ p ∈ range (k + 1), ∑ q ∈ range (i + 1), ∑ u ∈ range (p + 1),
          ∑ j ∈ range (i + k + 1),
          ((((d * k).choose (k - p) : ℤ) * ((d * i).choose (i - q) : ℤ) *
            ((q + u).choose p : ℤ) * (p.choose u : ℤ)) * W d (q + u) j) * B d j n := by
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro q hq
        apply sum_congr rfl
        intro u hu
        rw [extend p q u (by simpa using hp) (by simpa using hq) (by simpa using hu), mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        unfold S
        simp_rw [sum_mul]
        simp_rw [sum_comm (s := range (i + k + 1))]


/-- Initial Kronecker delta and the source's recursion for positive powers. -/
def a (k : ℕ) (T : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => fun _ => 0
  | 1 => fun j => if j = k then 1 else 0
  | r + 2 => fun j => ∑ i ∈ range ((r + 1) * k + 1), T j i * a k T (r + 1) i

/-- Both sentences of Conjecture 4.1, with explicit finite-support bounds. -/
def claim : Prop := ∀ d k : ℕ, ∃ T : ℕ → ℕ → ℤ,
  (∀ i j, i + k < j → T j i = 0) ∧
  let c : ℕ → ℕ → ℤ := a k T
  ∀ r, 1 ≤ r → (∀ j, r * k < j → c r j = 0) ∧
    ∀ n, B d k n ^ r = ∑ j ∈ range (r * k + 1), c r j * B d j n

theorem result : claim := by
  intro d k
  have hp := basis_product d k
  refine ⟨S d k, hp.1, ?_⟩
  change ∀ r, 1 ≤ r → (∀ j, r * k < j → a k (S d k) r j = 0) ∧
    ∀ n, B d k n ^ r = ∑ j ∈ range (r * k + 1), a k (S d k) r j * B d j n
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    constructor
    · intro j hj
      simp only [one_mul] at hj
      simp [a, show j ≠ k by omega]
    · intro n
      simp [a, ite_mul, show k < k + 1 by omega]
  | succ r hr ih =>
    have hrec (j : ℕ) : a k (S d k) (r + 1) j =
        ∑ i ∈ range (r * k + 1), S d k j i * a k (S d k) r i := by
      obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      subst r
      rfl
    constructor
    · intro j hj
      rw [hrec]
      apply sum_eq_zero
      intro i hi
      have hij : i + k < j := by
        simp only [mem_range] at hi
        rw [Nat.add_mul, one_mul] at hj
        omega
      rw [hp.1 i j hij, zero_mul]
    · intro n
      have extend (i : ℕ) (hi : i ≤ r * k) : B d k n * B d i n =
          ∑ j ∈ range ((r + 1) * k + 1), S d k j i * B d j n := by
        rw [hp.2 i n]
        apply sum_subset (range_mono (by nlinarith))
        intro j hj hj'
        have hij : i + k < j := by simp only [mem_range] at hj hj'; omega
        rw [hp.1 i j hij, zero_mul]
      calc
        B d k n ^ (r + 1) = B d k n * B d k n ^ r := pow_succ' _ _
        _ = ∑ i ∈ range (r * k + 1), a k (S d k) r i * (B d k n * B d i n) := by
          rw [ih.2 n, mul_sum]
          apply sum_congr rfl
          intro i hi
          ring
        _ = ∑ i ∈ range (r * k + 1), ∑ j ∈ range ((r + 1) * k + 1),
            (S d k j i * a k (S d k) r i) * B d j n := by
          apply sum_congr rfl
          intro i hi
          rw [extend i (by simpa using hi), mul_sum]
          apply sum_congr rfl
          intro j hj
          ring
        _ = _ := by
          simp_rw [hrec, sum_mul]
          rw [sum_comm]

end D5.S3.Combinatorics.BinomialBases.ShiftedBinomialPowerLinearization
