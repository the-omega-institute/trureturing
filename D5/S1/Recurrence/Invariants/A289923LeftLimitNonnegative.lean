/- GID: D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/A289923LeftLimitNonnegative
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Coefficientwise left limits and a positive recurrence for A289923. -/

import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! The normalized formal inverse and its coefficientwise left limit at 19/21. -/

open PowerSeries
namespace D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative

private def d (n : ℕ) : ℤ := (-1) ^ n * ((19 * (n + 1) + 20) / 21 : ℕ)
private noncomputable def D : PowerSeries ℤ := mk d
private noncomputable def E : PowerSeries ℤ := D * (1 + X) ^ 2
private noncomputable def P : PowerSeries ℤ := (1 + X) ^ 2 * (1 + X ^ 21)
private noncomputable def Q : PowerSeries ℤ := 1 - X ^ 10 - X ^ 11 - X ^ 20

private theorem d_shift (n : ℕ) : d (n + 21) = -d n - 19 * (-1) ^ n := by
  have hd : (19 * (n + 21 + 1) + 20) / 21 = (19 * (n + 1) + 20) / 21 + 19 := by omega
  simp only [d, hd, Nat.cast_add, Nat.cast_ofNat, pow_add]
  norm_num
  ring

private theorem e_coeff (n : ℕ) : coeff n E =
    d n + 2 * (if 1 ≤ n then d (n - 1) else 0) +
      (if 2 ≤ n then d (n - 2) else 0) := by
  have he : E = D + 2 * (X ^ 1 * D) + X ^ 2 * D := by unfold E; ring
  rw [he]
  simp only [map_add, coeff_ofNat_mul, coeff_X_pow_mul', D, coeff_mk]

private theorem e_shift (n : ℕ) : coeff (n + 2 + 21) E = -coeff (n + 2) E := by
  rw [e_coeff, e_coeff]
  simp only [show 1 ≤ n + 2 + 21 by omega, show 2 ≤ n + 2 + 21 by omega,
    show 1 ≤ n + 2 by omega, show 2 ≤ n + 2 by omega, ite_true]
  rw [show n + 2 + 21 - 1 = (n + 1) + 21 by omega,
    show n + 2 + 21 - 2 = n + 21 by omega,
    show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  rw [d_shift, d_shift, d_shift]
  simp only [pow_add]
  norm_num
  ring

private theorem denominator_identity : D * P = Q := by
  have he : D * P = E + X ^ 21 * E := by unfold P E; ring
  rw [he]
  ext n
  rw [map_add, coeff_X_pow_mul']
  by_cases hn : n < 23
  · interval_cases n <;> norm_num [e_coeff, d, Q, coeff_X_pow]
  · have h23 : 23 ≤ n := by omega
    have hs := e_shift (n - 23)
    rw [show n - 23 + 2 + 21 = n by omega,
      show n - 23 + 2 = n - 21 by omega] at hs
    rw [ite_eq_left (by omega : 21 ≤ n), hs]
    simp [Q, coeff_X_pow, show n ≠ 0 by omega, show n ≠ 10 by omega,
      show n ≠ 11 by omega, show n ≠ 20 by omega]

private theorem positive_recurrence (F : PowerSeries ℤ) (h : Q * F = P) :
    ∀ n, 0 ≤ coeff n F := by
  have hp : P = 1 + 2 * X ^ 1 + X ^ 2 + X ^ 21 + 2 * X ^ 22 + X ^ 23 := by
    unfold P
    ring
  have hp0 (n : ℕ) : 0 ≤ coeff n P := by
    rw [hp]
    simp only [map_add, coeff_ofNat_mul, coeff_X_pow, coeff_one]
    positivity
  have he : F = P + X ^ 10 * F + X ^ 11 * F + X ^ 20 * F := by
    unfold Q at h
    linear_combination h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc := congrArg (coeff n) he
    simp only [map_add, coeff_X_pow_mul'] at hc
    have h10 : 0 ≤ (if 10 ≤ n then coeff (n - 10) F else 0) := by
      split_ifs with hh
      · exact ih _ (by omega)
      · exact le_rfl
    have h11 : 0 ≤ (if 11 ≤ n then coeff (n - 11) F else 0) := by
      split_ifs with hh
      · exact ih _ (by omega)
      · exact le_rfl
    have h20 : 0 ≤ (if 20 ≤ n then coeff (n - 20) F else 0) := by
      split_ifs with hh
      · exact ih _ (by omega)
      · exact le_rfl
    linarith [hp0 n]

/-- The literal real-parameter denominator in the OEIS definition. -/
noncomputable def parameterDenominator (r : ℝ) : PowerSeries ℤ :=
  mk (fun k => (-1) ^ k * ⌊1 + ((k : ℝ) + 1) * r⌋)

/-- Its normalized formal inverse; the relevant domain is 0 < r < 1. -/
noncomputable def parameterInverse (r : ℝ) : PowerSeries ℤ :=
  invOfUnit (parameterDenominator r) 1

/-- Coefficientwise stabilization on an index-dependent left neighborhood. -/
def IsLeftLimit (a : ℕ → ℤ) : Prop :=
  ∀ n, ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ,
    0 < r → r < 1 → 19 / 21 - δ < r → r < 19 / 21 →
      coeff n (parameterInverse r) = a n

private theorem floor_stable (n k : ℕ) (hk : k ≤ n) (r : ℝ)
    (hl : 19 / 21 - 1 / (21 * ((n : ℝ) + 1)) < r) (hr : r < 19 / 21) :
    ⌊1 + ((k : ℝ) + 1) * r⌋ = ((19 * (k + 1) + 20) / 21 : ℕ) := by
  let q := (19 * (k + 1) + 20) / 21
  have hq1 : 21 * q ≤ 19 * (k + 1) + 20 := by dsimp [q]; omega
  have hq2 : 19 * (k + 1) ≤ 21 * q := by dsimp [q]; omega
  have hq1' : 21 * (q : ℝ) ≤ 19 * ((k : ℝ) + 1) + 20 := by exact_mod_cast hq1
  have hq2' : 19 * ((k : ℝ) + 1) ≤ 21 * (q : ℝ) := by exact_mod_cast hq2
  have hn : 0 < 21 * ((n : ℝ) + 1) := by positivity
  have ht : 0 < 19 / 21 - r := by linarith
  have ht' : (19 / 21 - r) * (21 * ((n : ℝ) + 1)) < 1 := by
    apply (lt_div_iff₀ hn).mp
    linarith
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hprod : (19 / 21 - r) * (21 * ((k : ℝ) + 1)) ≤
      (19 / 21 - r) * (21 * ((n : ℝ) + 1)) := by gcongr
  apply Int.floor_eq_iff.mpr
  change (q : ℝ) ≤ 1 + ((k : ℝ) + 1) * r ∧
    1 + ((k : ℝ) + 1) * r < (q : ℝ) + 1
  constructor <;> nlinarith

private theorem parameter_normalized (r : ℝ) (h0 : 0 < r) (h1 : r < 1) :
    constantCoeff (parameterDenominator r) = 1 := by
  simp only [parameterDenominator, constantCoeff_mk, pow_zero, Nat.cast_zero, zero_add,
    one_mul]
  exact Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩

private theorem inverse_stable (n : ℕ) (r : ℝ) (h0 : 0 < r) (h1 : r < 1)
    (hl : 19 / 21 - 1 / (21 * ((n : ℝ) + 1)) < r) (hr : r < 19 / 21) :
    coeff n (parameterInverse r) = coeff n (invOfUnit D 1) := by
  apply AbsoluteReciprocalGeometricParity.agree_inv
    (d := n + 1) (parameter_normalized r h0 h1)
    (show constantCoeff D = 1 by norm_num [D, d]) _ n (by omega)
  intro k hk
  simp only [parameterDenominator, D, coeff_mk, d]
  rw [floor_stable n k (by omega) r hl hr]

private theorem limit_exists : IsLeftLimit (fun n => coeff n (invOfUnit D 1)) := by
  intro n
  refine ⟨1 / (21 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro r h0 h1 hl hr
  exact inverse_stable n r h0 h1 hl hr

private theorem limit_unique (a b : ℕ → ℤ) (ha : IsLeftLimit a) (hb : IsLeftLimit b) :
    a = b := by
  funext n
  obtain ⟨δa, hδa, ha⟩ := ha n
  obtain ⟨δb, hδb, hb⟩ := hb n
  let ε := min (min δa δb) (19 / 42)
  have hε : 0 < ε := lt_min (lt_min hδa hδb) (by norm_num)
  have hεa : ε ≤ δa := (min_le_left _ _).trans (min_le_left _ _)
  have hεb : ε ≤ δb := (min_le_left _ _).trans (min_le_right _ _)
  have hε19 : ε ≤ 19 / 42 := min_le_right _ _
  let r : ℝ := 19 / 21 - ε / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hr : r < 19 / 21 := by dsimp [r]; linarith
  have hla : 19 / 21 - δa < r := by dsimp [r]; linarith
  have hlb : 19 / 21 - δb < r := by dsimp [r]; linarith
  exact (ha r hr0 hr1 hla hr).symm.trans (hb r hr0 hr1 hlb hr)

/-- A289923 is well defined by the stated coefficientwise left limit, and every term,
including index zero, is nonnegative. Uniqueness is among all left-limit sequences. -/
theorem result : ∃ a : ℕ → ℤ, IsLeftLimit a ∧
    (∀ b : ℕ → ℤ, IsLeftLimit b → b = a) ∧ (∀ n : ℕ, 0 ≤ a n) := by
  refine ⟨fun n => coeff n (invOfUnit D 1), limit_exists, ?_, ?_⟩
  · intro b hb
    exact limit_unique _ _ hb limit_exists
  · apply positive_recurrence
    have hD : constantCoeff D = 1 := by norm_num [D, d]
    calc
      Q * invOfUnit D 1 = (D * P) * invOfUnit D 1 := by rw [denominator_identity]
      _ = P * (D * invOfUnit D 1) := by ring
      _ = P := by rw [mul_invOfUnit D 1 hD, mul_one]

end D5.S1.Recurrence.Invariants.A289923LeftLimitNonnegative
