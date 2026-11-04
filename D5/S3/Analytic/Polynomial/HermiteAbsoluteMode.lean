/- GID: D5/S3/Analytic/Polynomial/HermiteAbsoluteMode
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteAbsoluteMode
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Absolute coefficient modes of physicists Hermite polynomials. -/

/-
admission_basis: open-problem-resolution (#25789), OEIS A381524 revision 18.
escape_witness: none. The complete external assertion is the admission basis.
proof_shape: content for weight_le_mode, weight_lt_mode, b_spec and result;
all other theorem helpers are bind-only, with live consumers in these proofs.
The original physicists polynomial and signed coefficient supplier are reused.
-/

import D5.S3.Analytic.Polynomial.HermiteSignedMode

/-! Exact smallest absolute-coefficient modes and consecutive-order transitions. -/

namespace D5.S3.Analytic.Polynomial.HermiteAbsoluteMode

open Finset HermiteSignedMode

def second (j : ℕ) : ℕ := (j + 1) * (j + 2)
def rises (n r : ℕ) : Prop := 2 * r ≤ n ∧ 4 * r ≤ second (n - 2 * r)
private instance (n r : ℕ) : Decidable (rises n r) := inferInstanceAs (Decidable (_ ∧ _))
private def candidates (n : ℕ) := (range (n + 1)).filter (rises n)
private theorem zero_candidate (n : ℕ) : 0 ∈ candidates n := by
  simp [candidates, rises, second]
def mode (n : ℕ) : ℕ := (candidates n).max' ⟨0, zero_candidate n⟩
theorem mode_rises (n : ℕ) : rises n (mode n) :=
  (mem_filter.mp (max'_mem _ _)).2
theorem le_mode {n r : ℕ} (h : rises n r) : r ≤ mode n := by
  apply le_max'
  exact mem_filter.mpr ⟨mem_range.mpr (by have := h.1; omega), h⟩

theorem second_mono : Monotone second := by
  intro a b h
  unfold second
  gcongr
private theorem rises_lower {n r s : ℕ} (h : rises n r) (hs : s ≤ r) : rises n s := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (Nat.mul_le_mul_left 4 hs).trans (h.2.trans (second_mono (by omega)))
private theorem rises_next {n r : ℕ} (h : rises n r) : rises (n + 1) r :=
  ⟨by have := h.1; omega, h.2.trans (second_mono (by omega))⟩
private theorem rises_previous {n r : ℕ} (h : rises (n + 1) (r + 1)) : rises n r := by
  refine ⟨by have := h.1; omega, ?_⟩
  exact (Nat.mul_le_mul_left 4 (by omega : r ≤ r + 1)).trans
    (h.2.trans (second_mono (by omega)))
private theorem mode_step (n : ℕ) : mode n ≤ mode (n + 1) ∧ mode (n + 1) ≤ mode n + 1 := by
  refine ⟨le_mode (rises_next (mode_rises n)), ?_⟩
  cases h : mode (n + 1) with
  | zero => omega
  | succ r =>
    have hr := mode_rises (n + 1)
    rw [h] at hr
    have := le_mode (rises_previous hr)
    omega

/-- The original signed coefficient observed through absolute value. -/
def weight (n r : ℕ) : ℚ := |signedCoeff n (n - 2 * r)|

theorem weight_pos (n r : ℕ) (hr : 2 * r ≤ n) : 0 < weight n r := by
  have h : n - 2 * r ≤ n ∧ (n - (n - 2 * r)) % 2 = 0 := by constructor <;> omega
  simp only [weight, signedCoeff, if_pos h, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, Nat.abs_cast, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  positivity

theorem adjacent (n r : ℕ) (h : 2 * (r + 1) ≤ n) :
    weight n (r + 1) * (4 * (r + 1)) =
      weight n r * second (n - 2 * (r + 1)) := by
  let j := n - 2 * (r + 1)
  have hj : n - 2 * r = j + 2 := by dsimp [j]; omega
  have hs : n - (n - 2 * (r + 1)) = 2 * (r + 1) := by omega
  have ht : n - (n - 2 * r) = 2 * r := by omega
  have he : 2 * (r + 1) / 2 = r + 1 := by omega
  have hf : 2 * r / 2 = r := by omega
  simp only [weight, signedCoeff, show n - 2 * (r + 1) ≤ n by omega,
    show n - 2 * r ≤ n by omega, hs, ht, he, hf,
    show 2 * (r + 1) % 2 = 0 by omega, show (2 * r) % 2 = 0 by omega,
    and_self, ite_true, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, Nat.abs_cast, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  rw [hj]
  change (↑n.factorial * 2^j / (↑(r + 1).factorial * ↑j.factorial)) *
      (4 * ((r : ℚ) + 1)) =
    (↑n.factorial * 2^(j + 2) / (↑r.factorial * ↑(j + 2).factorial)) *
      ↑((j + 1) * (j + 2))
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, pow_add]
  have hrf : (↑r.factorial : ℚ) ≠ 0 := by positivity
  have hjf : (↑j.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem adjacent_le (n r : ℕ) (h : 2 * (r + 1) ≤ n) :
    weight n r ≤ weight n (r + 1) ↔ rises n (r + 1) := by
  have hd : (0 : ℚ) < 4 * (r + 1) := by positivity
  have hw := weight_pos n r (by omega)
  have he := adjacent n r h
  constructor
  · intro hh
    refine ⟨h, ?_⟩
    have hh' := mul_le_mul_of_nonneg_right hh hd.le
    rw [he] at hh'
    exact_mod_cast (by nlinarith : (4 * (r + 1) : ℚ) ≤ second (n - 2 * (r + 1)))
  · intro hh
    have hh' : (4 * (r + 1) : ℚ) ≤ second (n - 2 * (r + 1)) := by exact_mod_cast hh.2
    have hm := mul_le_mul_of_nonneg_left hh' hw.le
    nlinarith [he]

theorem weight_le_mode (n r : ℕ) (hr : 2 * r ≤ n) : weight n r ≤ weight n (mode n) := by
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
  · have aux : ∀ k, 2 * k ≤ n → mode n ≤ k → weight n k ≤ weight n (mode n) := by
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

theorem weight_lt_mode (n r : ℕ) (hr : 2 * r ≤ n) (hm : mode n < r) :
    weight n r < weight n (mode n) := by
  cases r with
  | zero => omega
  | succ r =>
    have hnot : ¬ rises n (r + 1) := fun hh => by have := le_mode hh; omega
    have hlt : weight n (r + 1) < weight n r :=
      lt_of_not_ge (fun hh => hnot ((adjacent_le n r hr).mp hh))
    exact hlt.trans_le (weight_le_mode n r (by omega))

theorem coefficient_cases (n j : ℕ) : |signedCoeff n j| = 0 ∨
    ∃ r, 2 * r ≤ n ∧ j = n - 2 * r ∧ |signedCoeff n j| = weight n r := by
  by_cases h : j ≤ n ∧ (n - j) % 2 = 0
  · right
    let r := (n - j) / 2
    have hr : n - j = 2 * r := by dsimp [r]; omega
    have hj : j = n - 2 * r := by omega
    exact ⟨r, by omega, hj, by rw [hj]; rfl⟩
  · left
    simp [signedCoeff, h]

/-- The smallest exponent maximizing the absolute coefficient. -/
noncomputable def b (n : ℕ) : ℕ := n - 2 * mode n

/-- Maximal absolute value over the whole row, with the smallest exponent among ties. -/
def IsSmallestAbsMax (n j : ℕ) : Prop :=
  j ≤ n ∧ (∀ k, k ≤ n → |(physicistsHermite n).coeff k| ≤ |(physicistsHermite n).coeff j|) ∧
    ∀ k, k ≤ n → |(physicistsHermite n).coeff k| = |(physicistsHermite n).coeff j| → j ≤ k

private theorem b_spec (n : ℕ) : IsSmallestAbsMax n (b n) := by
  have hm := (mode_rises n).1
  have hb : b n ≤ n := Nat.sub_le _ _
  have hp := weight_pos n (mode n) hm
  refine ⟨hb, ?_, ?_⟩
  · intro k hk
    rw [polynomial_coeff n k hk, polynomial_coeff n (b n) hb]
    change |signedCoeff n k| ≤ weight n (mode n)
    rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
    · rw [h]; exact hp.le
    · rw [hc]
      exact weight_le_mode n r hr
  · intro k hk he
    rw [polynomial_coeff n k hk, polynomial_coeff n (b n) hb] at he
    change |signedCoeff n k| = weight n (mode n) at he
    rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
    · rw [h] at he
      linarith
    · have hle : r ≤ mode n := by
        by_contra hh
        have ht := weight_lt_mode n r hr (by omega)
        rw [hc] at he
        linarith
      dsimp [b]
      omega

/-- The complete A381524 adjacent-difference assertion and exact selector certificate. -/
def claim : Prop :=
  (∀ n, IsSmallestAbsMax n (b n)) ∧
  ∀ n : ℕ, (b (n + 1) : ℤ) - (b n : ℤ) = 1 ∨ (b (n + 1) : ℤ) - (b n : ℤ) = -1

/-- Every consecutive smallest absolute-coefficient mode changes by one or minus one. -/
theorem result : claim := by
  refine ⟨b_spec, ?_⟩
  intro n
  have hs := mode_step n
  have hm := (mode_rises n).1
  have hn := (mode_rises (n + 1)).1
  have hcases : mode (n + 1) = mode n ∨ mode (n + 1) = mode n + 1 := by omega
  dsimp [b]
  rcases hcases with h | h
  · left; omega
  · right; omega

end D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
