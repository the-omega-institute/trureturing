/- GID: D5/S3/Analytic/Polynomial/HermiteSignedMode
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteSignedMode
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed coefficient modes of physicists Hermite polynomials. -/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

namespace D5.S3.Analytic.Polynomial.HermiteSignedMode

open Finset

/-- DLMF 18.5.13, with a zero coefficient outside the parity support. -/
def signedCoeff (n j : ℕ) : ℚ :=
  if j ≤ n ∧ (n - j) % 2 = 0 then
    (-1 : ℚ) ^ ((n - j) / 2) * n.factorial * 2 ^ j /
      (((n - j) / 2).factorial * j.factorial)
  else 0

/-- The physicists polynomial, specified by its exact finite coefficient formula. -/
noncomputable def physicistsHermite (n : ℕ) : Polynomial ℚ :=
  ∑ j ∈ range (n + 1), Polynomial.monomial j (signedCoeff n j)

private def fourth (j : ℕ) : ℕ := (j+1)*(j+2)*(j+3)*(j+4)
private def divisor (r : ℕ) : ℕ := 16*(2*r)*(2*r-1)
private def rises (n r : ℕ) : Prop := 4*r ≤ n ∧ divisor r ≤ fourth (n-4*r)
private instance (n r : ℕ) : Decidable (rises n r) := inferInstanceAs (Decidable (_ ∧ _))
private def candidates (n : ℕ) := (range (n+1)).filter (rises n)
private theorem zero_candidate (n : ℕ) : 0 ∈ candidates n := by
  simp [candidates, rises, divisor, fourth]
private def mode (n : ℕ) : ℕ := (candidates n).max' ⟨0, zero_candidate n⟩
private theorem mode_rises (n : ℕ) : rises n (mode n) :=
  (mem_filter.mp (max'_mem _ _)).2
private theorem le_mode {n r : ℕ} (h : rises n r) : r ≤ mode n := by
  apply le_max'
  exact mem_filter.mpr ⟨mem_range.mpr (by have := h.1; omega), h⟩

private theorem fourth_mono : Monotone fourth := by
  intro a b h
  unfold fourth
  gcongr
private theorem divisor_mono : Monotone divisor := by
  intro a b h
  unfold divisor
  gcongr
private theorem rises_lower {n r s : ℕ} (h : rises n r) (hs : s ≤ r) : rises n s := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (divisor_mono hs).trans (h.2.trans (fourth_mono (by omega)))
private theorem rises_next {n r : ℕ} (h : rises n r) : rises (n+1) r :=
  ⟨by have := h.1; omega, h.2.trans (fourth_mono (by omega))⟩
private theorem rises_previous {n r : ℕ} (h : rises (n+1) (r+1)) : rises n r := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (divisor_mono (by omega : r ≤ r+1)).trans
    (h.2.trans (fourth_mono (by omega)))
private theorem mode_step (n : ℕ) : mode n ≤ mode (n+1) ∧ mode (n+1) ≤ mode n + 1 := by
  refine ⟨le_mode (rises_next (mode_rises n)), ?_⟩
  cases h : mode (n+1) with
  | zero => omega
  | succ r =>
    have hr := mode_rises (n+1)
    rw [h] at hr
    have := le_mode (rises_previous hr)
    omega

private def weight (n r : ℕ) : ℚ :=
  2 ^ (n-4*r) / ((2*r).factorial * (n-4*r).factorial)

private theorem weight_pos (n r : ℕ) : 0 < weight n r := by
  unfold weight
  positivity

private theorem adjacent (n r : ℕ) (h : 4*(r+1) ≤ n) :
    weight n (r+1) * divisor (r+1) = weight n r * fourth (n-4*(r+1)) := by
  let j := n-4*(r+1)
  have hj : n-4*r = j+4 := by dsimp [j]; omega
  have hr : 2*(r+1) = 2*r+2 := by omega
  have hr' : 2*(r+1)-1 = 2*r+1 := by omega
  simp only [weight, divisor, fourth, hj, hr, hr']
  change 2^j / (↑((2*r+2).factorial) * ↑(j.factorial)) *
      (16 * ↑(2*r+2) * ↑(2*r+1)) =
    2^(j+4) / (↑((2*r).factorial) * ↑((j+4).factorial)) *
      (↑(j+1)*↑(j+2)*↑(j+3)*↑(j+4))
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, pow_add]
  have hrf : (↑((2*r).factorial) : ℚ) ≠ 0 := by positivity
  have hjf : (↑(j.factorial) : ℚ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem adjacent_le (n r : ℕ) (h : 4*(r+1) ≤ n) :
    weight n r ≤ weight n (r+1) ↔ rises n (r+1) := by
  have hd : (0 : ℚ) < divisor (r+1) := by
    unfold divisor
    have : 0 < 2*(r+1)-1 := by omega
    positivity
  have hw := weight_pos n r
  have he := adjacent n r h
  constructor
  · intro hh
    refine ⟨h, ?_⟩
    have hh' := mul_le_mul_of_nonneg_right hh hd.le
    rw [he] at hh'
    exact_mod_cast (mul_le_mul_left hw).mp hh'
  · intro hh
    have hh' : (divisor (r+1) : ℚ) ≤ fourth (n-4*(r+1)) := by exact_mod_cast hh.2
    apply (mul_le_mul_right hd).mp
    rw [he]
    exact mul_le_mul_of_nonneg_left hh' hw.le

end D5.S3.Analytic.Polynomial.HermiteSignedMode
