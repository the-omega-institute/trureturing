/- GID: D5/S3/Constants/Billiards/CollidingBlocksRecords
   generality: G
   mirror-B: D5/B/S3/Constants/Billiards/CollidingBlocksRecords
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: OEIS A331859: every n with a(n) != floor(pi sqrt n) is a record position of a. -/

/-
proof_shape: result: bind-only (instances of `arctan_strictMono`, `lt_tan`, `tan_arctan`,
  `sin_arctan`, `sin_lt` and the floor/ceiling lemmas, with normalization)
escape_witness: null
admission_basis: open-problem-resolution (issue #10098)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Billiards.CollidingBlocksRecords

open Real

/-!
OEIS A331859 (Peter Kagey, 2020): `a(n)` is the total number of elastic collisions between a
block of mass `n` sliding toward a block of mass `1` and a wall, with the entry's formula
`a(n) = ceiling(Pi/arctan(sqrt(1/n))) - 1` (Galperin's count). The entry conjectures that the
values of `n` for which `a(n) ≠ A121854(n) = floor(Pi*sqrt(n))` form a subset of A331903, the
positions of records in A331859.
-/

/-- OEIS A331859 (FORMULA): `a(n) = ceiling(Pi/arctan(sqrt(1/n))) - 1`. -/
noncomputable def a (n : ℕ) : ℤ := ⌈π / arctan (√(1 / (n : ℝ)))⌉ - 1

/-- OEIS A331859, Conjecture: every `n ≥ 1` with `a(n) ≠ floor(Pi*sqrt(n))` (A121854) is a
position of a record of `a` (A331903): `a(k) < a(n)` for all `1 ≤ k < n`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n ≠ ⌊π * √(n : ℝ)⌋ → ∀ k : ℕ, 1 ≤ k → k < n → a k < a n

theorem result : claim := by
  intro n hn hne k hk hkn
  -- `t m = arctan √(1/m)` is positive and below `π/2`
  have tpos : ∀ m : ℕ, 1 ≤ m → 0 < arctan (√(1 / (m : ℝ))) := by
    intro m hm
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact arctan_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  -- monotonicity of `a`
  have mono : ∀ i j : ℕ, 1 ≤ i → i ≤ j → a i ≤ a j := by
    intro i j hi hij
    have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have ht : arctan (√(1 / (j : ℝ))) ≤ arctan (√(1 / (i : ℝ))) := by
      apply arctan_strictMono.monotone
      apply Real.sqrt_le_sqrt
      exact one_div_le_one_div_of_le (by linarith) hij'
    have : π / arctan (√(1 / (i : ℝ))) ≤ π / arctan (√(1 / (j : ℝ))) :=
      div_le_div_of_nonneg_left pi_pos.le (tpos j (le_trans hi hij)) ht
    unfold a
    have := Int.ceil_mono this
    omega
  -- lower bound: `⌊π √n⌋ ≤ a n`
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have sq : √(1 / (n : ℝ)) = 1 / √(n : ℝ) := by
    rw [Real.sqrt_div' 1 (by positivity), Real.sqrt_one]
  have hsqn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have tlt : arctan (√(1 / (n : ℝ))) < √(1 / (n : ℝ)) := by
    have h1 := tpos n hn
    have h2 := arctan_lt_pi_div_two (√(1 / (n : ℝ)))
    have := Real.lt_tan h1 h2
    rwa [tan_arctan] at this
  have fgt : π * √(n : ℝ) < π / arctan (√(1 / (n : ℝ))) := by
    rw [lt_div_iff₀ (tpos n hn)]
    rw [sq] at tlt ⊢
    calc π * √(n : ℝ) * arctan (1 / √(n : ℝ)) < π * √(n : ℝ) * (1 / √(n : ℝ)) := by
          apply mul_lt_mul_of_pos_left tlt; positivity
      _ = π := by field_simp
  have low : ⌊π * √(n : ℝ)⌋ ≤ a n := by
    unfold a
    have : ⌊π * √(n : ℝ)⌋ < ⌈π / arctan (√(1 / (n : ℝ)))⌉ := by
      rw [Int.lt_ceil]
      exact lt_of_le_of_lt (Int.floor_le _) fgt
    omega
  -- so `a n > π √n`
  have agt : π * √(n : ℝ) < (a n : ℝ) := by
    have h1 : ⌊π * √(n : ℝ)⌋ + 1 ≤ a n := by omega
    have h2 := Int.lt_floor_add_one (π * √(n : ℝ))
    have h3 : ((⌊π * √(n : ℝ)⌋ + 1 : ℤ) : ℝ) ≤ (a n : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  -- key step: `a (n-1) < π √n` for `n ≥ 2`
  have n2 : 2 ≤ n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsin : sin (arctan (√(1 / (m : ℝ)))) = 1 / √((m + 1 : ℕ) : ℝ) := by
    rw [sin_arctan, Real.sq_sqrt (by positivity)]
    have e : (1 : ℝ) + 1 / (m : ℝ) = ((m + 1 : ℕ) : ℝ) / m := by
      push_cast; field_simp
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_div' _ (by positivity), Real.sqrt_one]
    have : 0 < √(m : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have tgt : 1 / √((m + 1 : ℕ) : ℝ) < arctan (√(1 / (m : ℝ))) := by
    rw [← hsin]; exact sin_lt (tpos m hm)
  have fm : π / arctan (√(1 / (m : ℝ))) < π * √((m + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ (tpos m hm)]
    have hs : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    calc π = π * √((m + 1 : ℕ) : ℝ) * (1 / √((m + 1 : ℕ) : ℝ)) := by field_simp
      _ < π * √((m + 1 : ℕ) : ℝ) * arctan (√(1 / (m : ℝ))) := by
          apply mul_lt_mul_of_pos_left tgt; positivity
  have am : (a m : ℝ) < π / arctan (√(1 / (m : ℝ))) := by
    unfold a
    push_cast
    have := Int.ceil_lt_add_one (π / arctan (√(1 / (m : ℝ))))
    linarith
  have amn : a m < a (m + 1) := by
    have : (a m : ℝ) < (a (m + 1) : ℝ) := by linarith
    exact_mod_cast this
  exact lt_of_le_of_lt (mono k m hk (by omega)) amn

end D5.S3.Constants.Billiards.CollidingBlocksRecords
