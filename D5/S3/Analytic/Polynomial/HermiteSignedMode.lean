/- GID: D5/S3/Analytic/Polynomial/HermiteSignedMode
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteSignedMode
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed coefficient modes of physicists Hermite polynomials. -/

/-
admission_basis: open-problem-resolution (#25634; Proved).
escape_witness: none. The independent external assertion is the admission basis.
proof_shape: content for weight_le_mode, weight_lt_mode, a_spec and result;
all other theorem helpers are bind-only, with live consumers in these proofs.
Utility is none: the result is universal, not a finite computation or instance.
Source: OEIS A381423 revision 8; physicists normalization is DLMF 18.5.13.
The polynomial uses the literal finite physicists coefficient formula over ℚ.
No uniqueness of the maximizing coefficient is assumed or concluded.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact physicists Hermite coefficients and their signed modes. -/

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
  ∑ k ∈ range (n / 2 + 1), Polynomial.monomial (n - 2 * k)
    ((-1 : ℚ) ^ k * n.factorial * 2 ^ (n - 2 * k) /
      (k.factorial * (n - 2 * k).factorial))

private def fourth (j : ℕ) : ℕ := (j + 1) * (j + 2) * (j + 3) * (j + 4)
private def divisor (r : ℕ) : ℕ := 16 * (2 * r) * (2 * r - 1)
private def rises (n r : ℕ) : Prop := 4 * r ≤ n ∧ divisor r ≤ fourth (n - 4 * r)
private instance (n r : ℕ) : Decidable (rises n r) := inferInstanceAs (Decidable (_ ∧ _))
private def candidates (n : ℕ) := (range (n + 1)).filter (rises n)
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
private theorem rises_next {n r : ℕ} (h : rises n r) : rises (n + 1) r :=
  ⟨by have := h.1; omega, h.2.trans (fourth_mono (by omega))⟩
private theorem rises_previous {n r : ℕ} (h : rises (n + 1) (r + 1)) : rises n r := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (divisor_mono (by omega : r ≤ r + 1)).trans
    (h.2.trans (fourth_mono (by omega)))
private theorem mode_step (n : ℕ) : mode n ≤ mode (n + 1) ∧ mode (n + 1) ≤ mode n + 1 := by
  refine ⟨le_mode (rises_next (mode_rises n)), ?_⟩
  cases h : mode (n + 1) with
  | zero => omega
  | succ r =>
    have hr := mode_rises (n + 1)
    rw [h] at hr
    have := le_mode (rises_previous hr)
    omega

private def weight (n r : ℕ) : ℚ :=
  2 ^ (n - 4 * r) / ((2 * r).factorial * (n - 4 * r).factorial)

private theorem weight_pos (n r : ℕ) : 0 < weight n r := by
  unfold weight
  positivity

private theorem adjacent (n r : ℕ) (h : 4 * (r + 1) ≤ n) :
    weight n (r + 1) * divisor (r + 1) = weight n r * fourth (n - 4 * (r + 1)) := by
  let j := n - 4 * (r + 1)
  have hj : n - 4 * r = j + 4 := by dsimp [j]; omega
  have hr : 2 * (r + 1) = 2 * r + 2 := by omega
  have hr' : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  simp only [weight, divisor, fourth, hj, hr, hr']
  change (2 : ℚ)^j / (↑((2 * r + 2).factorial) * ↑(j.factorial)) *
      ↑(16 * (2 * r + 2) * (2 * r + 1)) =
    2^(j + 4) / (↑((2 * r).factorial) * ↑((j + 4).factorial)) *
      ↑((j + 1) * (j + 2) * (j + 3) * (j + 4))
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, pow_add]
  have hrf : (↑((2 * r).factorial) : ℚ) ≠ 0 := by positivity
  have hjf : (↑(j.factorial) : ℚ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem adjacent_le (n r : ℕ) (h : 4 * (r + 1) ≤ n) :
    weight n r ≤ weight n (r + 1) ↔ rises n (r + 1) := by
  have hd : (0 : ℚ) < divisor (r + 1) := by
    unfold divisor
    have : 0 < 2 * (r + 1) - 1 := by omega
    positivity
  have hw := weight_pos n r
  have he := adjacent n r h
  constructor
  · intro hh
    refine ⟨h, ?_⟩
    have hh' := mul_le_mul_of_nonneg_right hh hd.le
    rw [he] at hh'
    exact_mod_cast (by nlinarith : (divisor (r + 1) : ℚ) ≤ fourth (n - 4 * (r + 1)))
  · intro hh
    have hh' : (divisor (r + 1) : ℚ) ≤ fourth (n - 4 * (r + 1)) := by exact_mod_cast hh.2
    have hm := mul_le_mul_of_nonneg_left hh' hw.le
    nlinarith [he]

private theorem weight_le_mode (n r : ℕ) (hr : 4 * r ≤ n) : weight n r ≤ weight n (mode n) := by
  by_cases h : r ≤ mode n
  · have aux : ∀ k, k ≤ mode n → ∀ i, i ≤ k → weight n i ≤ weight n k := by
      intro k
      induction k with
      | zero =>
        intro hk i hi
        have : i = 0 := by omega
        subst i
        rfl
      | succ k ih =>
        intro hk i hi
        by_cases hik : i ≤ k
        · exact (ih (by omega) i hik).trans
            ((adjacent_le n k (by have := (mode_rises n).1; omega)).mpr
              (rises_lower (mode_rises n) hk))
        · have : i = k + 1 := by omega
          subst i
          rfl
    exact aux _ le_rfl r h
  · have aux : ∀ k, 4 * k ≤ n → mode n ≤ k → weight n k ≤ weight n (mode n) := by
      intro k
      induction k with
      | zero =>
        intro hk hm
        have : mode n = 0 := by omega
        rw [this]
      | succ k ih =>
        intro hk hm
        by_cases hkm : mode n ≤ k
        · have hnot : ¬ rises n (k + 1) := fun hh => by have := le_mode hh; omega
          have hlt : weight n (k + 1) < weight n k :=
            lt_of_not_ge (fun hh => hnot ((adjacent_le n k hk).mp hh))
          exact hlt.le.trans (ih (by omega) hkm)
        · have : mode n = k + 1 := by omega
          rw [this]
    exact aux r hr (by omega)

private theorem weight_lt_mode (n r : ℕ) (hr : 4 * r ≤ n) (hm : mode n < r) :
    weight n r < weight n (mode n) := by
  cases r with
  | zero => omega
  | succ r =>
    have hnot : ¬ rises n (r + 1) := fun hh => by have := le_mode hh; omega
    have hlt : weight n (r + 1) < weight n r :=
      lt_of_not_ge (fun hh => hnot ((adjacent_le n r hr).mp hh))
    exact hlt.trans_le (weight_le_mode n r (by omega))

private theorem positive_coefficient (n r : ℕ) (hr : 4 * r ≤ n) :
    signedCoeff n (n - 4 * r) = n.factorial * weight n r := by
  have hs : n - (n - 4 * r) = 4 * r := by omega
  have he : 4 * r/2 = 2 * r := by omega
  simp [signedCoeff, hs, he, show (4 * r)%2 = 0 by omega, show (n - 4 * r ≤ n) by omega, weight,
    show (-1 : ℚ)^(2 * r) = 1 by rw [pow_mul]; norm_num]
  <;> ring

private theorem coefficient_cases (n j : ℕ) : signedCoeff n j ≤ 0 ∨
    ∃ r, 4 * r ≤ n ∧ j = n - 4 * r ∧ signedCoeff n j = n.factorial * weight n r := by
  by_cases h : j ≤ n ∧ (n - j)%2 = 0
  · by_cases h4 : (n - j)%4 = 0
    · right
      let r := (n - j)/4
      have hr : n - j = 4 * r := by dsimp [r]; omega
      have hj : j = n - 4 * r := by omega
      exact ⟨r, by omega, hj, hj ▸ positive_coefficient n r (by omega)⟩
    · left
      have he : (n - j)/2 = 2 * ((n - j)/4) + 1 := by omega
      have hp : (-1 : ℚ)^((n - j)/2) = -1 := by
        rw [he, pow_add, pow_mul]
        norm_num
      rw [signedCoeff, if_pos h, hp]
      have : (0 : ℚ) < n.factorial := by positivity
      have : (0 : ℚ) < 2^j := by positivity
      have : (0 : ℚ) < ((n - j)/2).factorial * j.factorial := by positivity
      exact (div_neg_of_neg_of_pos (by nlinarith) this).le
  · left
    simp [signedCoeff, h]

/-- The smallest exponent maximizing the signed coefficient. -/
noncomputable def a (n : ℕ) : ℕ := n - 4 * mode n

/-- Exact source predicate: all exponents, signed order, smallest - index ties. -/
def IsSmallestMax (n j : ℕ) : Prop :=
  j ≤ n ∧ (∀ k, k ≤ n → (physicistsHermite n).coeff k ≤ (physicistsHermite n).coeff j) ∧
    ∀ k, k ≤ n → (physicistsHermite n).coeff k = (physicistsHermite n).coeff j → j ≤ k

theorem polynomial_coeff (n j : ℕ) (hj : j ≤ n) :
    (physicistsHermite n).coeff j = signedCoeff n j := by
  classical
  simp only [physicistsHermite, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases h : j ≤ n ∧ (n - j)%2 = 0
  · rw [signedCoeff, if_pos h]
    have he : n - 2 * ((n - j)/2) = j := by omega
    rw [sum_eq_single ((n - j)/2)]
    · simp [he]
    · intro b hb hne
      have hn : 2 * b ≤ n := by have := mem_range.mp hb; omega
      have hh : n - 2 * b ≠ j := by omega
      simp [hh, Ne.symm hh]
    · intro hh
      exact (hh (mem_range.mpr (by omega))).elim
  · rw [signedCoeff, if_neg h]
    apply sum_eq_zero
    intro b hb
    have hn : 2 * b ≤ n := by have := mem_range.mp hb; omega
    have hh : n - 2 * b ≠ j := by
      intro he
      apply h
      constructor <;> omega
    simp [hh, Ne.symm hh]

private theorem a_spec (n : ℕ) : IsSmallestMax n (a n) := by
  have hm := (mode_rises n).1
  have ha : a n ≤ n := Nat.sub_le _ _
  have hcoeff := positive_coefficient n (mode n) hm
  have hp : (0 : ℚ) < n.factorial * weight n (mode n) := by
    have := weight_pos n (mode n)
    positivity
  refine ⟨ha, ?_, ?_⟩
  · intro k hk
    rw [polynomial_coeff n k hk, polynomial_coeff n (a n) ha]
    change signedCoeff n k ≤ signedCoeff n (n - 4 * mode n)
    rw [hcoeff]
    rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
    · exact h.trans hp.le
    · rw [hc]
      exact mul_le_mul_of_nonneg_left (weight_le_mode n r hr) (by positivity)
  · intro k hk he
    rw [polynomial_coeff n k hk, polynomial_coeff n (a n) ha] at he
    change signedCoeff n k = signedCoeff n (n - 4 * mode n) at he
    rw [hcoeff] at he
    rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
    · linarith
    · have hle : r ≤ mode n := by
        by_contra hh
        have ht := weight_lt_mode n r hr (by omega)
        have hnf : (0 : ℚ) < n.factorial := by positivity
        rw [hc] at he
        nlinarith
      dsimp [a]
      omega

/-- OEIS A381423's independent difference assertion, with its exact source selector. -/
def claim : Prop :=
  (∀ n, IsSmallestMax n (a n)) ∧
  ∀ n : ℕ, (a (n + 1) : ℤ) - (a n : ℤ) = 1 ∨ (a (n + 1) : ℤ) - (a n : ℤ) = -3

/-- The signed maximum's smallest exponent changes by one or minus three at every index. -/
theorem result : claim := by
  refine ⟨a_spec, ?_⟩
  intro n
  have hs := mode_step n
  have hm := (mode_rises n).1
  have hn := (mode_rises (n + 1)).1
  have hcases : mode (n + 1) = mode n ∨ mode (n + 1) = mode n + 1 := by omega
  dsimp [a]
  rcases hcases with h | h
  · left; omega
  · right; omega

end D5.S3.Analytic.Polynomial.HermiteSignedMode
