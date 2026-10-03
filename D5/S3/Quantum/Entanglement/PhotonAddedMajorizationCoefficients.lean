/- GID: D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The photon-addition coefficients c_n^(kk) of arXiv:2312.02066 are non-negative. -/

/-
proof_shape: result: bind-only (Vandermonde's identity, `Nat.choose_mul` and the
  `invOneSubPow` identities of Mathlib, instantiated and normalized coefficientwise; the
  series `B = N_k / N_1` and the cancellation of `N_1` are local steps of `result`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11700)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.PhotonAddedMajorizationCoefficients

/-!
Z. Van Herstraeten, N. J. Cerf, S. Guha and C. N. Gagatsos, *Majorization theoretical approach to
entanglement enhancement via local filtration*, arXiv:2312.02066 (Phys. Rev. A 110 (2024)
042430), Appendix, conjecture that the coefficients `c_n^{(kk)}` defined by
`C(n+k+1,k)² = ∑_{i=0}^{n+1} c_{n-i}^{(kk)} (i+1)²` with `c_{-1}^{(kk)} = 1` are non-negative
for every `k ≥ 2`, so that the matrix comparing `k`-photon addition with single-photon addition
on a two-mode squeezed vacuum is column stochastic. It holds. With `N_k(x) = ∑ C(n+k,k)² xⁿ` the
relation says `(1 + ∑ c_n x^{n+1}) N_1 = N_k`. Vandermonde gives
`N_k = ∑_j C(k,j) C(k+j,j) x^j (1-x)^{-(k+j+1)}` and `N_1 = (1+x)(1-x)^{-3}`, so
`N_k / N_1 = (1 + (k²+k-1)x)(1-x)^{-(k-2)}(1-x²)^{-1}
  + ∑_{j=2}^{k} C(k,j) C(k+j,j) x^j (1-x)^{-(k+j-3)}(1-x²)^{-1}`,
a series with non-negative coefficients.
-/

open PowerSeries

/-- Eq. (eqapp:binomial) of arXiv:2312.02066 for every `n ≥ 0`, with `c n` for `c_n^{(kk)}` and
the term `c_{-1}^{(kk)} (n+2)² = (n+2)²` of the sum written separately. -/
def Expansion (k : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (((n + k + 1).choose k : ℕ) : ℝ) ^ 2 =
    ∑ i ∈ Finset.range (n + 1), c (n - i) * ((i : ℝ) + 1) ^ 2 + ((n : ℝ) + 2) ^ 2

/-- The conjecture of arXiv:2312.02066: for every `k ≥ 2` the coefficients `c_n^{(kk)}` exist and
are non-negative. -/
def claim : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (∃ c : ℕ → ℝ, Expansion k c) ∧ ∀ c : ℕ → ℝ, Expansion k c → ∀ n, 0 ≤ c n

/-- The conjecture holds. -/
theorem result : claim := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  -- `G d = (1 - X)⁻ᵈ`
  set G : ℕ → ℝ⟦X⟧ := fun d => (invOneSubPow ℝ d).val with hGdef
  have hGmul : ∀ a b, G a * G b = G (a + b) := by
    intro a b
    simp only [hGdef, invOneSubPow_add, Units.val_mul]
  have hGsucc : ∀ d n, coeff n (G (d + 1)) = ((d + n).choose d : ℝ) := by
    intro d n
    simp only [hGdef, invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
  have hGstep : ∀ d, (1 - X) * G (d + 1) = G d := by
    intro d
    have h := one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℝ d 1
    simpa [hGdef] using h
  -- the series of the paper
  set Nk : ℝ⟦X⟧ := mk fun n => (((n + (m + 2)).choose (m + 2) : ℕ) : ℝ) ^ 2 with hNk
  set N1 : ℝ⟦X⟧ := mk fun n => ((n : ℝ) + 1) ^ 2 with hN1
  set E : ℝ⟦X⟧ := mk fun n => if Even n then 1 else 0 with hE
  set a : ℕ → ℝ := fun j => (((m + 2).choose j * (m + 2 + j).choose j : ℕ) : ℝ) with ha
  -- `N_1 = (1 + X)(1 - X)⁻³`
  have hN1G : N1 = (1 + X) * G 3 := by
    ext n
    rw [add_mul, one_mul, map_add, hGsucc]
    rcases n with _ | n
    · simp [hN1, coeff_zero_X_mul]
    · rw [coeff_succ_X_mul, hGsucc, hN1, coeff_mk]
      have h1 : ((2 + (n + 1)).choose 2 : ℝ) =
          ((n + 3 : ℕ) : ℝ) * ((n + 3 : ℕ) - 1) / 2 := by
        rw [show 2 + (n + 1) = n + 3 by omega, Nat.cast_choose_two]
      have h2 : ((2 + n).choose 2 : ℝ) = ((n + 2 : ℕ) : ℝ) * ((n + 2 : ℕ) - 1) / 2 := by
        rw [show 2 + n = n + 2 by omega, Nat.cast_choose_two]
      rw [h1, h2]
      push_cast
      ring
  -- `E (1 + X) = (1 - X)⁻¹`
  have hE1 : E * (1 + X) = G 1 := by
    ext n
    rw [mul_add, mul_one, map_add, hGsucc, mul_comm E X]
    rcases n with _ | n
    · simp [hE, coeff_zero_X_mul]
    · rw [coeff_succ_X_mul, hE, coeff_mk, coeff_mk]
      rcases Nat.even_or_odd n with h | h
      · have h' : ¬ Even (n + 1) := by rw [Nat.even_add_one]; exact not_not.mpr h
        simp [h, h']
      · have h' : Even (n + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr h
        have h'' : ¬ Even n := Nat.not_even_iff_odd.mpr h
        simp [h', h'']
  -- Vandermonde: `C(n+k,k)² = ∑_j C(k,j) C(k+j,j) C(n+k,k+j)`
  have hvand : ∀ n, ((n + (m + 2)).choose (m + 2)) ^ 2 =
      ∑ j ∈ Finset.range (m + 3),
        (m + 2).choose j * (m + 2 + j).choose j * (n + (m + 2)).choose (m + 2 + j) := by
    intro n
    set k := m + 2 with hk
    have hv : (n + k).choose k = ∑ j ∈ Finset.range (k + 1), n.choose j * k.choose j := by
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => n.choose i * k.choose j)]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.choose_symm (by simp at hj; omega)]
    have hprod : ∀ j,
        (n + k).choose k * n.choose j = (k + j).choose j * (n + k).choose (k + j) := by
      intro j
      rcases le_or_gt j n with hjn | hjn
      · have e1 := Nat.choose_mul (n := n + k) (k := n) (s := j) hjn
        have e2 := Nat.choose_mul (n := n + k) (k := k + j) (s := j) (by omega)
        have e3 : (n + k).choose k = (n + k).choose n := by
          rw [Nat.add_comm n k, Nat.choose_symm_add]
        have e4 : (n + k - j).choose (n - j) = (n + k - j).choose (k + j - j) := by
          rw [show n + k - j = (n - j) + k by omega, show k + j - j = k by omega,
            Nat.choose_symm_add]
        rw [e3, e1, e4, ← e2, Nat.mul_comm]
      · rw [Nat.choose_eq_zero_of_lt hjn,
          Nat.choose_eq_zero_of_lt (show n + k < k + j by omega), mul_zero, mul_zero]
    have hsq : (n + k).choose k ^ 2 =
        (n + k).choose k * ∑ j ∈ Finset.range (k + 1), n.choose j * k.choose j := by
      rw [sq, ← hv]
    rw [hsq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (n + k).choose k * (n.choose j * k.choose j)
        = k.choose j * ((n + k).choose k * n.choose j) by ring, hprod, Nat.mul_assoc]
  -- `N_k = ∑_j a_j X^j (1 - X)^{-(k+j+1)}`
  have hNkG : Nk = ∑ j ∈ Finset.range (m + 3), C (a j) * X ^ j * G (m + 2 + j + 1) := by
    ext n
    rw [map_sum, hNk, coeff_mk]
    have hterm : ∀ j ∈ Finset.range (m + 3), coeff n (C (a j) * X ^ j * G (m + 2 + j + 1)) =
        (((m + 2).choose j * (m + 2 + j).choose j * (n + (m + 2)).choose (m + 2 + j) : ℕ) :
          ℝ) := by
      intro j _
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', ha]
      split_ifs with hjn
      · rw [hGsucc, show m + 2 + j + (n - j) = n + (m + 2) by omega]
        push_cast
        ring
      · rw [Nat.choose_eq_zero_of_lt (show n + (m + 2) < m + 2 + j by omega)]
        simp
    rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, ← hvand]
    push_cast
    ring
  -- the quotient `N_k / N_1`
  set B : ℝ⟦X⟧ := (1 + C (((m : ℝ) + 2) * ((m : ℝ) + 3) - 1) * X) * G m * E +
    ∑ i ∈ Finset.range (m + 1),
      C (a (i + 1 + 1)) * X ^ (i + 1 + 1) * G (m + (i + 1 + 1) - 1) * E with hB
  have hBN : B * N1 = Nk := by
    have hfac : ∀ T : ℝ⟦X⟧, ∀ d, T * G d * E * N1 = T * G (d + 4) := by
      intro T d
      rw [hN1G, show T * G d * E * ((1 + X) * G 3) = T * G d * (E * (1 + X)) * G 3 by ring,
        hE1, mul_assoc, mul_assoc, hGmul, hGmul]
    have hNk3 : Nk = ∑ i ∈ Finset.range (m + 1),
          C (a (i + 1 + 1)) * X ^ (i + 1 + 1) * G (m + 2 + (i + 1 + 1) + 1) +
        C (a (0 + 1)) * X ^ (0 + 1) * G (m + 2 + (0 + 1) + 1) +
        C (a 0) * X ^ 0 * G (m + 2 + 0 + 1) := by
      rw [hNkG, Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : C (a 0) * X ^ 0 * G (m + 2 + 0 + 1) = G (m + 3) := by
      simp [ha]
    have h1 : (1 + C (((m : ℝ) + 2) * ((m : ℝ) + 3) - 1) * X) * G (m + 4) =
        C (a (0 + 1)) * X ^ (0 + 1) * G (m + 2 + (0 + 1) + 1) + G (m + 3) := by
      have ha1 : a (0 + 1) = ((m : ℝ) + 2) * ((m : ℝ) + 3) := by
        simp only [ha, zero_add, Nat.choose_one_right]
        push_cast
        ring
      have hs : G (m + 3) = (1 - X) * G (m + 4) := (hGstep (m + 3)).symm
      rw [ha1, hs, show m + 2 + (0 + 1) + 1 = m + 4 by omega, map_sub, map_one]
      ring
    have hsum : ∑ i ∈ Finset.range (m + 1),
          C (a (i + 1 + 1)) * X ^ (i + 1 + 1) * G (m + (i + 1 + 1) - 1 + 4) =
        ∑ i ∈ Finset.range (m + 1),
          C (a (i + 1 + 1)) * X ^ (i + 1 + 1) * G (m + 2 + (i + 1 + 1) + 1) :=
      Finset.sum_congr rfl fun i _ => by
        rw [show m + (i + 1 + 1) - 1 + 4 = m + 2 + (i + 1 + 1) + 1 by omega]
    rw [hB, add_mul, Finset.sum_mul, hfac]
    simp_rw [hfac]
    rw [hNk3, h0, h1, hsum]
    ring
  -- coefficients of `B` are non-negative
  have hmul : ∀ f g : ℝ⟦X⟧, (∀ n, 0 ≤ coeff n f) → (∀ n, 0 ≤ coeff n g) →
      ∀ n, 0 ≤ coeff n (f * g) := by
    intro f g hf hg n
    rw [coeff_mul]
    exact Finset.sum_nonneg fun p _ => mul_nonneg (hf _) (hg _)
  have hG0 : ∀ d n, 0 ≤ coeff n (G d) := by
    intro d n
    rcases d with _ | d
    · simp only [hGdef, invOneSubPow_zero, Units.val_one, coeff_one]
      split_ifs <;> norm_num
    · rw [hGsucc]
      positivity
  have hE0 : ∀ n, 0 ≤ coeff n E := by
    intro n
    rw [hE, coeff_mk]
    split_ifs <;> norm_num
  have hCX : ∀ (r : ℝ) (j : ℕ), 0 ≤ r → ∀ n, 0 ≤ coeff n (C r * X ^ j) := by
    intro r j hr n
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp [hr]
  have hB0 : ∀ n, 0 ≤ coeff n B := by
    intro n
    rw [hB, map_add]
    refine add_nonneg ?_ ?_
    · refine hmul _ _ (hmul _ _ ?_ (hG0 m)) hE0 n
      intro p
      rw [map_add]
      have := hCX (((m : ℝ) + 2) * ((m : ℝ) + 3) - 1) 1 (by nlinarith) p
      rw [pow_one] at this
      refine add_nonneg ?_ this
      rw [coeff_one]
      split_ifs <;> norm_num
    · rw [map_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      exact hmul _ _ (hmul _ _ (hCX _ _ (by rw [ha]; positivity)) (hG0 _)) hE0 n
  -- the relation of the paper as a product of series
  set S : (ℕ → ℝ) → ℝ⟦X⟧ := fun c => mk fun p => if p = 0 then 1 else c (p - 1)
    with hS
  have hS0 : ∀ c, coeff 0 (S c) = 1 := by
    intro c
    simp [hS]
  have hSs : ∀ c p, coeff (p + 1) (S c) = c p := by
    intro c p
    simp [hS]
  have hN1c : ∀ q, coeff q N1 = ((q : ℝ) + 1) ^ 2 := by
    intro q
    rw [hN1, coeff_mk]
  have hNkc : ∀ q, coeff q Nk = (((q + (m + 2)).choose (m + 2) : ℕ) : ℝ) ^ 2 := by
    intro q
    rw [hNk, coeff_mk]
  have hiff : ∀ c, Expansion (m + 2) c ↔ S c * N1 = Nk := by
    intro c
    have hcoeff : ∀ n, coeff (n + 1) (S c * N1) =
        ∑ i ∈ Finset.range (n + 1), c (n - i) * ((i : ℝ) + 1) ^ 2 + ((n : ℝ) + 2) ^ 2 := by
      intro n
      rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun p q => coeff p N1 * coeff q (S c)), Finset.sum_range_succ, Nat.sub_self, hS0,
        hN1c]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        rw [show n + 1 - i = (n - i) + 1 by omega, hSs, hN1c]
        ring
      · push_cast
        ring
    constructor
    · intro h
      ext q
      rcases q with _ | n
      · rw [mul_comm, coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hS0, hN1c,
          hNkc]
        simp
      · rw [hcoeff, ← h n, hNkc, show n + 1 + (m + 2) = n + (m + 2) + 1 by omega]
    · intro h n
      have := congrArg (coeff (n + 1)) h
      rw [hcoeff, hNkc, show n + 1 + (m + 2) = n + (m + 2) + 1 by omega] at this
      rw [this]
  have hN1ne : N1 ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    rw [hN1c, map_zero] at this
    norm_num at this
  have hG00 : ∀ d, coeff 0 (G d) = 1 := by
    intro d
    rcases d with _ | d
    · simp [hGdef, invOneSubPow_zero]
    · rw [hGsucc]
      simp
  have hB00 : coeff 0 B = 1 := by
    have hz : ∀ i ∈ Finset.range (m + 1), coeff 0
        (C (a (i + 1 + 1)) * X ^ (i + 1 + 1) * G (m + (i + 1 + 1) - 1) * E) = 0 := by
      intro i _
      rw [mul_assoc, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
        if_neg (show ¬ (i + 1 + 1 ≤ 0) by omega), mul_zero]
    rw [hB, map_add, map_sum, Finset.sum_eq_zero hz, add_zero, coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, hG00, hE, coeff_mk]
    simp
  refine ⟨⟨fun n => coeff (n + 1) B, ?_⟩, fun c hc n => ?_⟩
  · rw [hiff]
    have hSB : S (fun n => coeff (n + 1) B) = B := by
      ext p
      rcases p with _ | p
      · exact (hS0 (fun n => coeff (n + 1) B)).trans hB00.symm
      · exact hSs (fun n => coeff (n + 1) B) p
    rw [hSB, hBN]
  · have hSc : S c = B := mul_right_cancel₀ hN1ne (((hiff c).mp hc).trans hBN.symm)
    rw [← hSs c n, hSc]
    exact hB0 (n + 1)

end D5.S3.Quantum.Entanglement.PhotonAddedMajorizationCoefficients
