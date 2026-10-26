/- GID: D5/S3/Arith/Robin/ZeroPowerSum
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ZeroPowerSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite complex family containing one has a bounded positive real power sum. -/

import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Newton's identities force a nonnegative real power sum in a conjugate-paired
family. Removing and restoring an entry equal to one gives the Cassel selection. -/

namespace D5.S3.Arith.Robin.ZeroPowerSum

open scoped BigOperators

private theorem exists_nonneg_power_sum {α : Type*} [Fintype α] (x : α → ℂ)
    (hreal : ∀ k : ℕ, (∑ i, x i ^ k).im = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card α + 1 ∧ 0 ≤ (∑ i, x i ^ k).re := by
  classical
  let e : ℕ → ℂ := fun k =>
    (-1 : ℂ) ^ k * MvPolynomial.eval x (MvPolynomial.esymm α ℂ k)
  let c : ℕ → ℝ := fun k => (e k).re
  have hc0 : c 0 = 1 := by simp [c, e]
  have hNewton (k : ℕ) :
      (k : ℝ) * c k =
        -∑ a ∈ Finset.antidiagonal k with a.1 < k, c a.1 * (∑ i, x i ^ a.2).re := by
    have h := congrArg (MvPolynomial.eval x) (MvPolynomial.mul_esymm_eq_sum α ℂ k)
    have h' : (k : ℂ) * MvPolynomial.eval x (MvPolynomial.esymm α ℂ k) =
        (-1 : ℂ) ^ (k + 1) *
          ∑ a ∈ Finset.antidiagonal k with a.1 < k,
            (-1 : ℂ) ^ a.1 * MvPolynomial.eval x (MvPolynomial.esymm α ℂ a.1) *
              ∑ i, x i ^ a.2 := by
      simpa [MvPolynomial.psum] using h
    have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ (k + 1) = -1 := by
      rw [← pow_add]
      simp [show k + (k + 1) = 2 * k + 1 by omega, pow_succ]
    have heq : (k : ℂ) * e k =
        -∑ a ∈ Finset.antidiagonal k with a.1 < k, e a.1 * ∑ i, x i ^ a.2 := by
      calc
        (k : ℂ) * e k = (-1 : ℂ) ^ k *
            ((k : ℂ) * MvPolynomial.eval x (MvPolynomial.esymm α ℂ k)) := by dsimp [e]; ring
        _ = -∑ a ∈ Finset.antidiagonal k with a.1 < k,
            e a.1 * ∑ i, x i ^ a.2 := by
          rw [h', ← mul_assoc, hsign]
          simp only [neg_one_mul, e]
    have hre := congrArg Complex.re heq
    change Complex.reCLM ((k : ℂ) * e k) =
      Complex.reCLM (-∑ a ∈ Finset.antidiagonal k with a.1 < k,
        e a.1 * ∑ i, x i ^ a.2) at hre
    simpa only [map_neg, map_sum, Complex.reCLM_apply, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.neg_re, hreal, mul_zero, c] using hre
  by_contra hnot
  have hneg (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ Fintype.card α + 1) :
      (∑ i, x i ^ k).re < 0 := by
    exact lt_of_not_ge (fun h => hnot ⟨k, hk, hkd, h⟩)
  have hpos : ∀ k ≤ Fintype.card α + 1, 0 < c k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk0 : k = 0
      · simp [hk0, hc0]
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hsum : (∑ a ∈ Finset.antidiagonal k with a.1 < k,
          c a.1 * (∑ i, x i ^ a.2).re) < 0 := by
        apply Finset.sum_neg
        · intro a ha
          rcases Finset.mem_filter.mp ha with ⟨ha, halt⟩
          have hasum := Finset.mem_antidiagonal.mp ha
          exact mul_neg_of_pos_of_neg (ih a.1 halt (by omega))
            (hneg a.2 (by omega) (by omega))
        · exact ⟨(0, k), by simp [hkpos]⟩
      have hmul : 0 < (k : ℝ) * c k := by linarith [hNewton k]
      exact pos_of_mul_pos_right hmul (Nat.cast_nonneg k)
  have hzero : c (Fintype.card α + 1) = 0 := by
    have hcard : (Finset.univ.val.map x).card < Fintype.card α + 1 := by simp
    have hz := Multiset.esymm_of_card_lt (R := ℂ) hcard
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm α ℂ] at hz
    simpa [c, e] using congrArg (fun z : ℂ => ((-1 : ℂ) ^ (Fintype.card α + 1) * z).re) hz
  have := hpos (Fintype.card α + 1) le_rfl
  linarith

/-- A designated entry equal to one forces a power sum with real part at least one,
without any restriction on the moduli of the other entries. -/
theorem exists_pow_sum_re_ge_one {n : ℕ} (z : Fin n → ℂ) (h : ∃ i, z i = 1) :
    ∃ ν : ℕ, 1 ≤ ν ∧ ν ≤ 2 * n + 1 ∧ 1 ≤ (∑ i, z i ^ ν).re := by
  classical
  obtain ⟨i₀, hi₀⟩ := h
  let s := Finset.univ.erase i₀
  let x : Sum s s → ℂ := Sum.elim (fun i => z i) (fun i => star (z i))
  have hsum (k : ℕ) : (∑ i, x i ^ k) =
      (∑ i ∈ s, z i ^ k) + star (∑ i ∈ s, z i ^ k) := by
    simp only [x, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      ← star_pow]
    rw [Finset.sum_coe_sort s (fun i => z i ^ k),
      Finset.sum_coe_sort s (fun i => star (z i ^ k)), ← star_sum]
  have hreal (k : ℕ) : (∑ i, x i ^ k).im = 0 := by
    rw [hsum]
    simp only [Complex.add_im, Complex.star_def, Complex.conj_im, add_neg_cancel]
  obtain ⟨ν, hν, hbound, hnonneg⟩ := exists_nonneg_power_sum x hreal
  have hcard : Fintype.card (Sum s s) = 2 * (n - 1) := by
    simp [s, Fintype.card_sum, two_mul]
  have hrem : 0 ≤ (∑ i ∈ s, z i ^ ν).re := by
    rw [hsum] at hnonneg
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at hnonneg
    linarith
  refine ⟨ν, hν, ?_, ?_⟩
  · rw [hcard] at hbound
    omega
  · have hsplit : (∑ i, z i ^ ν) = (∑ i ∈ s, z i ^ ν) + 1 := by
      have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun i => z i ^ ν) (Finset.mem_univ i₀)
      simpa only [s, hi₀, one_pow] using he.symm
    rw [hsplit]
    simp only [Complex.add_re, Complex.one_re]
    linarith

end D5.S3.Arith.Robin.ZeroPowerSum
