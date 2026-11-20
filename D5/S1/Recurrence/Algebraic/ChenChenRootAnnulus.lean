/- GID: D5/S1/Recurrence/Algebraic/ChenChenRootAnnulus
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/ChenChenRootAnnulus
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For real m ≤ -3 and even n, the roots of the row polynomial lie in the ratio annulus. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#6)
escape_witness: no_root_outside (Eneström–Kakeya in monotone form: if 0 < b 0 ≤ … ≤ b d then
  ∑ b k w^k ≠ 0 for |w| > 1, from (1 - w) ∑ b k w^k = b 0 + ∑ (b (k+1) - b k) w^(k+1) -
  b d w^(d+1) and b d |w|^(d+1) > b d |w|^d ≥ |b 0 + …|), applied after scaling by the largest
  coefficient ratio, and the palindromic symmetry of even rows, which carries every root z to
  the root 1/z and makes the set of consecutive ratios closed under reciprocation.
proof_shape:
  lowRatio, highRatio, claim: source definitions; consumer: result.
  telescope_identity: bind-only helper (induction with sum_range_succ and ring); consumer:
    no_root_outside.
  no_root_outside: content; consumer: result.
  row_eq_range: bind-only helper (reindexing Icc 1 n to range n); consumer: result.
  result: content (scaling to the monotone case, the reciprocal root from reflection, and
    L = 1/U from the reciprocal ratio pairing); positivity of even rows is
    ChenChenRealStepSigns.result.
Direct frozen dependencies:
  D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums (Source, reflection)
    sha256:babe59678caa4efa35d42893011defa557b4e926070bb618982cee210a4d67c0
  D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns (result)
    sha256:c78f33a81b52b954c31e8cf7b15c8712256186bd64e332743f86a1ce590edce4
Search record (§3.1): Mathlib has no Eneström–Kakeya theorem (no hit for Enestrom or Kakeya
  under Mathlib/); Polynomial root bounds there (Cauchy-type bounds) do not give the ratio
  annulus. No D5 declaration bounds roots by coefficient ratios.
-/

import D5.S1.Recurrence.Algebraic.ChenChenRealStepSigns
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Root annulus of even-row polynomials of the step-`m` Eulerian triangle

For real `m ≤ -3` and even `n ≥ 2`, every complex root `z` of the row polynomial
`R(z) = ∑_{k=1}^{n} T(n,k) z^(k-1)` satisfies `L ≤ |z| ≤ U`, where `L` and `U` are the least and
largest of the positive consecutive ratios `T(n,k)/T(n,k+1)`, `1 ≤ k < n`, and `L U = 1`. This is
the Eneström–Kakeya bound, proved here in its monotone form and combined with the palindromic
symmetry of the row.
-/

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.ChenChenRootAnnulus

open Finset D5.S1.Recurrence.Algebraic.ChenChenRealStepRowSums

private theorem telescope_identity (b : ℕ → ℝ) (w : ℂ) (d : ℕ) :
    (1 - w) * ∑ k ∈ range (d + 1), (b k : ℂ) * w ^ k =
      ((b 0 : ℂ) + ∑ k ∈ range d, ((b (k + 1) - b k : ℝ) : ℂ) * w ^ (k + 1)) -
        (b d : ℂ) * w ^ (d + 1) := by
  induction d with
  | zero => simp; ring
  | succ d ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    push_cast
    ring

/-- Eneström–Kakeya, monotone form: a real polynomial with positive nondecreasing coefficients
has no root of modulus greater than one. -/
theorem no_root_outside {d : ℕ} (b : ℕ → ℝ) (hb0 : 0 < b 0)
    (hmono : ∀ k < d, b k ≤ b (k + 1)) (w : ℂ) (hw : 1 < ‖w‖) :
    ∑ k ∈ range (d + 1), (b k : ℂ) * w ^ k ≠ 0 := by
  intro h0
  have hpos : ∀ k ≤ d, 0 < b k := by
    intro k hk
    induction k with
    | zero => exact hb0
    | succ k ih => exact lt_of_lt_of_le (ih (by omega)) (hmono k (by omega))
  have hid := telescope_identity b w d
  rw [h0, mul_zero] at hid
  have key : (b 0 : ℂ) + ∑ k ∈ range d, ((b (k + 1) - b k : ℝ) : ℂ) * w ^ (k + 1) =
      (b d : ℂ) * w ^ (d + 1) := by linear_combination -hid
  have hn1 : (1 : ℝ) ≤ ‖w‖ := hw.le
  have hbound : ‖(b 0 : ℂ) + ∑ k ∈ range d, ((b (k + 1) - b k : ℝ) : ℂ) * w ^ (k + 1)‖ ≤
      ‖w‖ ^ d * b d := by
    calc _ ≤ ‖(b 0 : ℂ)‖ + ‖∑ k ∈ range d, ((b (k + 1) - b k : ℝ) : ℂ) * w ^ (k + 1)‖ :=
          norm_add_le _ _
      _ ≤ b 0 + ∑ k ∈ range d, (b (k + 1) - b k) * ‖w‖ ^ (k + 1) := by
          gcongr
          · rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
          · refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k hk => ?_))
            have := hmono k (mem_range.mp hk)
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr this), norm_pow]
      _ ≤ ‖w‖ ^ d * b 0 + ∑ k ∈ range d, (b (k + 1) - b k) * ‖w‖ ^ d := by
          gcongr with k hk
          · exact le_mul_of_one_le_left hb0.le (one_le_pow₀ hn1)
          · exact sub_nonneg.mpr (hmono k (mem_range.mp hk))
          · exact Nat.succ_le_of_lt (mem_range.mp hk)
      _ = ‖w‖ ^ d * b d := by
          rw [← sum_mul, sum_range_sub (fun k => b k) d]
          ring
  have hbd := hpos d le_rfl
  rw [key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hbd.le, norm_pow] at hbound
  have : ‖w‖ ^ d < ‖w‖ ^ (d + 1) := pow_lt_pow_right₀ hw (by omega)
  nlinarith [mul_lt_mul_of_pos_left this hbd]


/-- The least consecutive coefficient ratio `min_{1≤k<n} T(n,k)/T(n,k+1)`. -/
noncomputable def lowRatio (T : ℕ → ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) : ℝ :=
  (Ico 1 n).inf' (nonempty_Ico.mpr (by omega)) fun k => T n k / T n (k + 1)

/-- The largest consecutive coefficient ratio `max_{1≤k<n} T(n,k)/T(n,k+1)`. -/
noncomputable def highRatio (T : ℕ → ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) : ℝ :=
  (Ico 1 n).sup' (nonempty_Ico.mpr (by omega)) fun k => T n k / T n (k + 1)

/-- Positivity of the ratios, `L U = 1`, and the annulus `L ≤ |z| ≤ U` for every root. -/
def claim : Prop :=
  ∀ m : ℝ, m ≤ -3 → ∀ T : ℕ → ℕ → ℝ, Source m T → ∀ n (hn : 2 ≤ n), Even n →
    (∀ k ∈ Ico 1 n, 0 < T n k / T n (k + 1)) ∧
    lowRatio T n hn * highRatio T n hn = 1 ∧
    ∀ z : ℂ, ∑ k ∈ Icc 1 n, (T n k : ℂ) * z ^ (k - 1) = 0 →
      lowRatio T n hn ≤ ‖z‖ ∧ ‖z‖ ≤ highRatio T n hn

private theorem row_eq_range (T : ℕ → ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ∑ k ∈ Icc 1 n, (T n k : ℂ) * z ^ (k - 1) = ∑ j ∈ range n, (T n (j + 1) : ℂ) * z ^ j := by
  rw [show Icc 1 n = Ico 1 (n + 1) from rfl, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun j _ => ?_
  rw [add_comm 1 j, Nat.add_sub_cancel]

/-- The root annulus holds. -/
theorem result : claim := by
  intro m hm T h n hn he
  have hr : (3 : ℝ) ≤ -m := by linarith
  have h' : Source (-(-m)) T := by rwa [neg_neg]
  have hpos : ∀ k, 1 ≤ k → k ≤ n → 0 < T n k := fun k hk hkn =>
    ((D5.S1.Recurrence.Algebraic.ChenChenRealStepSigns.result _ hr).2 T h').1 n (by omega) he
      k hk hkn
  have hrefl : ∀ k, 1 ≤ k → k ≤ n → T n k = T n (n + 1 - k) := fun k hk hkn =>
    reflection h n k (by omega) hk hkn
  set f : ℕ → ℝ := fun k => T n k / T n (k + 1) with hf
  have fpos : ∀ k ∈ Ico 1 n, 0 < f k := by
    intro k hk
    have := mem_Ico.mp hk
    exact div_pos (hpos k this.1 (by omega)) (hpos (k + 1) (by omega) (by omega))
  have fsym : ∀ k ∈ Ico 1 n, f (n - k) = 1 / f k := by
    intro k hk
    have := mem_Ico.mp hk
    simp only [hf]
    rw [show n - k + 1 = n + 1 - k by omega, ← hrefl k this.1 (by omega),
      show n - k = n + 1 - (k + 1) by omega, ← hrefl (k + 1) (by omega) (by omega)]
    rw [one_div_div]
  have hne : (Ico 1 n).Nonempty := nonempty_Ico.mpr (by omega)
  set U := highRatio T n hn with hU
  set L := lowRatio T n hn with hL
  have hfU : ∀ k ∈ Ico 1 n, f k ≤ U := fun k hk => le_sup' f hk
  obtain ⟨k0, hk0, hk0U⟩ := exists_mem_eq_sup' hne f
  have hUpos : 0 < U := by rw [hU, highRatio, hk0U]; exact fpos k0 hk0
  have hmem : ∀ k ∈ Ico 1 n, n - k ∈ Ico 1 n := by
    intro k hk; have := mem_Ico.mp hk; exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hLU : L = 1 / U := by
    apply le_antisymm
    · calc L ≤ f (n - k0) := inf'_le f (hmem k0 hk0)
        _ = 1 / U := by rw [fsym k0 hk0, hU, highRatio, hk0U]
    · apply le_inf'
      intro k hk
      have h1 := fsym (n - k) (hmem k hk)
      rw [show n - (n - k) = k by have := mem_Ico.mp hk; omega] at h1
      have h2 := hfU (n - k) (hmem k hk)
      have h3 := fpos (n - k) (hmem k hk)
      show 1 / U ≤ f k
      rw [h1]
      exact one_div_le_one_div_of_le h3 h2
  -- upper bound for any root
  have upper : ∀ z : ℂ, ∑ j ∈ range n, (T n (j + 1) : ℂ) * z ^ j = 0 → ‖z‖ ≤ U := by
    intro z hz
    by_contra hlt
    push Not at hlt
    set w : ℂ := z / (U : ℂ)
    have hUc : (U : ℂ) ≠ 0 := by exact_mod_cast hUpos.ne'
    have hw : 1 < ‖w‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hUpos.le, one_lt_div hUpos]
      exact hlt
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
    refine no_root_outside (d := d) (fun j => T (d + 1) (j + 1) * U ^ j) ?_ ?_ w hw ?_
    · simp [(h.1 (d + 1) (by omega)).1]
    · intro j hj
      have hj1 : j + 1 ∈ Ico 1 (d + 1) := mem_Ico.mpr ⟨by omega, by omega⟩
      have hfj := hfU (j + 1) hj1
      have hden := hpos (j + 1 + 1) (by omega) (by omega)
      simp only [hf] at hfj
      rw [div_le_iff₀ hden] at hfj
      rw [pow_succ]
      nlinarith [pow_pos hUpos j]
    · rw [← hz]
      refine sum_congr rfl fun j _ => ?_
      simp only [w]
      push_cast
      rw [div_pow, mul_assoc, mul_div_assoc', mul_comm ((U : ℂ) ^ j), mul_div_assoc,
        div_self (pow_ne_zero _ hUc), mul_one]
  refine ⟨fpos, ?_, ?_⟩
  · rw [hLU]; field_simp
  · intro z hz
    rw [row_eq_range] at hz
    have hzU := upper z hz
    refine ⟨?_, hzU⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      obtain ⟨d, hd⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
      rw [hd, sum_range_succ'] at hz
      simp [← hd, (h.1 n (by omega)).1] at hz
    -- the reciprocal is also a root
    have hinv : ∑ j ∈ range n, (T n (j + 1) : ℂ) * z⁻¹ ^ j = 0 := by
      have hpal : ∑ j ∈ range n, (T n (j + 1) : ℂ) * z⁻¹ ^ j =
          z⁻¹ ^ (n - 1) * ∑ j ∈ range n, (T n (j + 1) : ℂ) * z ^ j := by
        rw [mul_sum, ← sum_range_reflect]
        refine sum_congr rfl fun j hj => ?_
        have hjn := mem_range.mp hj
        rw [hrefl (j + 1) (by omega) (by omega), show n + 1 - (j + 1) = n - 1 - j + 1 by omega]
        have hp : z⁻¹ ^ (n - 1) * z ^ j = z⁻¹ ^ (n - 1 - j) := by
          rw [show n - 1 = (n - 1 - j) + j by omega, pow_add, mul_assoc, ← mul_pow,
            inv_mul_cancel₀ hz0, one_pow, mul_one, Nat.add_sub_cancel]
        rw [← hp]
        ring
      rw [hpal, hz, mul_zero]
    have := upper z⁻¹ hinv
    rw [norm_inv] at this
    rw [hLU, one_div]
    exact (inv_le_comm₀ (norm_pos_iff.mpr hz0) hUpos).mp this

end D5.S1.Recurrence.Algebraic.ChenChenRootAnnulus
