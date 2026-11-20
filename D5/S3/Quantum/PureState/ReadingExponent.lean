/- GID: D5/S3/Quantum/PureState/ReadingExponent
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/ReadingExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multiplicative on [0, 1] with F cos + F sin = 1 forces F s = s ^ 2 on [0, 1]. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The reading exponent

A function `F : ℝ → ℝ` that is multiplicative on `[0, 1]` and satisfies
`F (cos t) + F (sin t) = 1` for `t ∈ [0, π / 2]` equals `s ^ 2` on `[0, 1]`. No continuity is
assumed: multiplicativity gives `0 ≤ F`, the normalization gives `F ≤ 1`, and together they make
`F` monotone on `[0, 1]`. The function `u ↦ F (√u)` is multiplicative, satisfies
`G u + G (1 - u) = 1`, hence `G (1 / 2) = 1 / 2` and `G` is the identity on dyadic rationals;
monotonicity squeezes it to the identity on `[0, 1]`.
-/

namespace D5.S3.Quantum.PureState.ReadingExponent

open Set

/-- On `[0, 1]` the normalization on the quarter circle reads `F s + F (√(1 - s ^ 2)) = 1`. -/
private theorem add_sqrt_one_sub_sq (F : ℝ → ℝ)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), F (Real.cos t) + F (Real.sin t) = 1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : F s + F (Real.sqrt (1 - s ^ 2)) = 1 := by
  have h := hnorm (Real.arccos s)
    ⟨Real.arccos_nonneg s, Real.arccos_le_pi_div_two.2 hs.1⟩
  rwa [Real.cos_arccos (by linarith [hs.1]) hs.2, Real.sin_arccos] at h

/-- `√(1 - s ^ 2)` lies in `[0, 1]`. -/
private theorem sqrt_one_sub_sq_mem (s : ℝ) : Real.sqrt (1 - s ^ 2) ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.2 (by nlinarith [sq_nonneg s])⟩

/-- `√s` lies in `[0, 1]` for `s ∈ [0, 1]`. -/
private theorem sqrt_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Real.sqrt s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.2 hs.2⟩

/-- Multiplicativity and normalization force the values at the endpoints. -/
private theorem zero_and_one (F : ℝ → ℝ)
    (hmul : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, F (s * t) = F s * F t)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), F (Real.cos t) + F (Real.sin t) = 1) :
    F 0 = 0 ∧ F 1 = 1 := by
  have h0 : F 0 = F 0 * F 0 := by
    simpa using hmul 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩
  have h01 : F 0 = F 0 * F 1 := by
    simpa using hmul 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
  have hsum : F 1 + F 0 = 1 := by
    simpa using add_sqrt_one_sub_sq F hnorm ⟨zero_le_one, le_rfl⟩
  have hF0 : F 0 = 0 := by
    by_contra hne
    have h1 : F 0 = 1 := mul_left_cancel₀ hne (h0.symm.trans (mul_one (F 0)).symm)
    have h2 : F 1 = 1 := mul_left_cancel₀ hne (h01.symm.trans (mul_one (F 0)).symm)
    linarith
  exact ⟨hF0, by linarith⟩

section
variable (F : ℝ → ℝ)
    (hmul : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, F (s * t) = F s * F t)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), F (Real.cos t) + F (Real.sin t) = 1)
include hmul hnorm

/-- The function lies in `[0, 1]` on `[0, 1]`. -/
private theorem mem_Icc_zero_one {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : F s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · have h := hmul _ (sqrt_mem hs) _ (sqrt_mem hs)
    rw [Real.mul_self_sqrt hs.1] at h
    rw [h]
    exact mul_self_nonneg _
  · have h := add_sqrt_one_sub_sq F hnorm hs
    have h' := hmul _ (sqrt_mem (sqrt_one_sub_sq_mem s)) _ (sqrt_mem (sqrt_one_sub_sq_mem s))
    rw [Real.mul_self_sqrt (sqrt_one_sub_sq_mem s).1] at h'
    nlinarith [mul_self_nonneg (F (Real.sqrt (Real.sqrt (1 - s ^ 2))))]

/-- The function is monotone on `[0, 1]`. -/
private theorem monotoneOn_Icc : MonotoneOn F (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · have : s = 0 := le_antisymm (h0 ▸ hst) hs.1
    subst this
    rw [← h0]
  · have hq : s / t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 ht.1, (div_le_one hpos).2 hst⟩
    have h := hmul t ht (s / t) hq
    rw [mul_div_cancel₀ s hpos.ne'] at h
    rw [h]
    have h1 := mem_Icc_zero_one F hmul hnorm ht
    have h2 := mem_Icc_zero_one F hmul hnorm hq
    nlinarith [h1.1, h2.2]

omit hmul in
/-- With `G u = F (√u)`: `G u + G (1 - u) = 1` on `[0, 1]`. -/
private theorem sqrt_add_sqrt_one_sub {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    F (Real.sqrt u) + F (Real.sqrt (1 - u)) = 1 := by
  have h := add_sqrt_one_sub_sq F hnorm (sqrt_mem hu)
  rwa [Real.sq_sqrt hu.1] at h

/-- `G` is the identity on the dyadic rationals of `[0, 1]`. -/
private theorem sqrt_dyadic (n : ℕ) :
    ∀ k : ℕ, k ≤ 2 ^ n → F (Real.sqrt ((k : ℝ) / 2 ^ n)) = (k : ℝ) / 2 ^ n := by
  have h01 := zero_and_one F hmul hnorm
  induction n with
  | zero =>
    intro k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using hk) with rfl | rfl
    · simp [h01.1]
    · simp [h01.2]
  | succ n ih =>
    have hhalf : F (Real.sqrt (1 / 2)) = 1 / 2 := by
      have h := sqrt_add_sqrt_one_sub F hnorm (u := 1 / 2) ⟨by norm_num, by norm_num⟩
      norm_num at h ⊢
      linarith
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have hlow : ∀ k : ℕ, k ≤ 2 ^ n →
        F (Real.sqrt ((k : ℝ) / 2 ^ (n + 1))) = (k : ℝ) / 2 ^ (n + 1) := by
      intro k hk
      have hkr : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
      have hmem : (k : ℝ) / 2 ^ n ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hpow).2 hkr⟩
      have heq : (k : ℝ) / 2 ^ (n + 1) = 1 / 2 * ((k : ℝ) / 2 ^ n) := by
        rw [pow_succ]; field_simp
      rw [heq, Real.sqrt_mul (by norm_num), hmul _ (sqrt_mem ⟨by norm_num, by norm_num⟩) _
        (sqrt_mem hmem), hhalf, ih k hk]
    intro k hk
    rcases le_or_gt k (2 ^ n) with hkn | hkn
    · exact hlow k hkn
    · have hj : 2 ^ (n + 1) - k ≤ 2 ^ n := by rw [pow_succ]; omega
      have hcast : ((2 ^ (n + 1) - k : ℕ) : ℝ) = 2 ^ (n + 1) - (k : ℝ) := by
        rw [Nat.cast_sub hk]; push_cast; ring
      have h := hlow _ hj
      rw [hcast] at h
      have hkr : (k : ℝ) ≤ 2 ^ (n + 1) := by exact_mod_cast hk
      have hpow' : (0 : ℝ) < 2 ^ (n + 1) := by positivity
      have hmem : (k : ℝ) / 2 ^ (n + 1) ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hpow').2 hkr⟩
      have hs := sqrt_add_sqrt_one_sub F hnorm hmem
      have hsub : 1 - (k : ℝ) / 2 ^ (n + 1) = (2 ^ (n + 1) - (k : ℝ)) / 2 ^ (n + 1) := by
        field_simp
      rw [hsub, h, sub_div, div_self hpow'.ne'] at hs
      linarith

/-- Monotone squeeze from below by dyadic rationals: `u - 1 / 2 ^ n < G u`. -/
private theorem sub_lt_sqrt {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    u - 1 / 2 ^ n < F (Real.sqrt u) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hnn : 0 ≤ u * 2 ^ n := mul_nonneg hu.1 hpow.le
  set k : ℕ := ⌊u * 2 ^ n⌋₊
  have hk1 : (k : ℝ) ≤ u * 2 ^ n := Nat.floor_le hnn
  have hk2 : u * 2 ^ n < k + 1 := Nat.lt_floor_add_one _
  have hk3 : k ≤ 2 ^ n := Nat.floor_le_of_le (by
    push_cast
    nlinarith [hu.2])
  have hle : (k : ℝ) / 2 ^ n ≤ u := (div_le_iff₀ hpow).2 hk1
  have hmem : (k : ℝ) / 2 ^ n ∈ Icc (0 : ℝ) 1 := ⟨by positivity, hle.trans hu.2⟩
  have hmono := monotoneOn_Icc F hmul hnorm (sqrt_mem hmem) (sqrt_mem hu) (Real.sqrt_le_sqrt hle)
  rw [sqrt_dyadic F hmul hnorm n k hk3] at hmono
  have : u - 1 / 2 ^ n < (k : ℝ) / 2 ^ n := by
    have he : u - 1 / 2 ^ n = (u * 2 ^ n - 1) / 2 ^ n := by field_simp
    rw [he]
    exact (div_lt_div_iff_of_pos_right hpow).2 (by linarith)
  linarith

/-- `G` is the identity on `[0, 1]`. -/
private theorem sqrt_eq {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : F (Real.sqrt u) = u := by
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 1 / (2 : ℝ) ^ n < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, by rwa [one_div_pow] at hn⟩
  have hu' : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  apply le_antisymm
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := hsmall ε hε
    have h1 := sub_lt_sqrt F hmul hnorm hu' n
    have h2 := sqrt_add_sqrt_one_sub F hnorm hu
    linarith
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := hsmall ε hε
    have h1 := sub_lt_sqrt F hmul hnorm hu n
    linarith

end

/-- A function multiplicative on `[0, 1]` with `F (cos t) + F (sin t) = 1` on `[0, π / 2]` is
the square on `[0, 1]`; no continuity is assumed. -/
theorem eq_sq_of_mul_of_cos_add_sin (F : ℝ → ℝ)
    (hmul : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, F (s * t) = F s * F t)
    (hnorm : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), F (Real.cos t) + F (Real.sin t) = 1) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, F s = s ^ 2 := by
  intro s hs
  have h := sqrt_eq F hmul hnorm (u := s ^ 2) ⟨sq_nonneg s, pow_le_one₀ hs.1 hs.2⟩
  rwa [Real.sqrt_sq hs.1] at h

end D5.S3.Quantum.PureState.ReadingExponent
