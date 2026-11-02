/- GID: D5/S3/Arith/ModularForms/CubicThetaLattice
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaLattice
   mirror-E: none(waiver:formal-lattice-generating-series)
   anchors: []
   utility: none
   digest: Finite Eisenstein norm fibres and explicit cubic theta residue bijections. -/

import Mathlib.Data.Int.Interval
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ModularForms.CubicThetaLattice

/-- The positive definite binary Eisenstein norm. -/
def eisensteinNorm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2

/-- The integer exponent in the three-core lattice sum. -/
def coreExponent (p : ℤ × ℤ) : ℤ := 3 * eisensteinNorm p - 2 * p.1 - p.2

abbrev NormFiber (n : ℕ) := {p : ℤ × ℤ // eisensteinNorm p = (n : ℤ)}
abbrev CoreFiber (n : ℕ) := {p : ℤ × ℤ // coreExponent p = (n : ℤ)}

theorem norm_coercive (p : ℤ × ℤ) :
    p.1 ^ 2 + p.2 ^ 2 ≤ 2 * eisensteinNorm p := by
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (p.1 + p.2)]

theorem norm_nonneg (p : ℤ × ℤ) : 0 ≤ eisensteinNorm p := by
  have := norm_coercive p
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

theorem core_shift_norm (p : ℤ × ℤ) :
    eisensteinNorm (3 * p.1 - 1, 3 * p.2) = 3 * coreExponent p + 1 := by
  dsimp [eisensteinNorm, coreExponent]
  ring

theorem core_exponent_nonneg (p : ℤ × ℤ) : 0 ≤ coreExponent p := by
  have h := norm_nonneg (3 * p.1 - 1, 3 * p.2)
  rw [core_shift_norm] at h
  omega

instance normFiber_finite (n : ℕ) : Finite (NormFiber n) := by
  have hfinite : Set.Finite {p : ℤ × ℤ | eisensteinNorm p = (n : ℤ)} := by
    apply (Set.finite_Icc (-(2 * (n : ℤ) + 2), -(2 * (n : ℤ) + 2))
      (2 * (n : ℤ) + 2, 2 * (n : ℤ) + 2)).subset
    intro p hp
    have h := norm_coercive p
    rw [hp] at h
    have hx : p.1 ^ 2 ≤ (2 * (n : ℤ) + 2) ^ 2 := by
      nlinarith [sq_nonneg p.2, sq_nonneg (n : ℤ)]
    have hy : p.2 ^ 2 ≤ (2 * (n : ℤ) + 2) ^ 2 := by
      nlinarith [sq_nonneg p.1, sq_nonneg (n : ℤ)]
    have hx' := abs_le_of_sq_le_sq' hx (by omega)
    have hy' := abs_le_of_sq_le_sq' hy (by omega)
    exact ⟨⟨hx'.1, hy'.1⟩, ⟨hx'.2, hy'.2⟩⟩
  exact hfinite.to_subtype

instance coreFiber_finite (n : ℕ) : Finite (CoreFiber n) := by
  let f : CoreFiber n → NormFiber (3 * n + 1) := fun p =>
    ⟨(3 * p.1.1 - 1, 3 * p.1.2), by
      rw [core_shift_norm, p.2]
      push_cast
      rfl⟩
  apply Finite.of_injective f
  intro p q hpq
  have h := congrArg Subtype.val hpq
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Subtype.ext
  exact Prod.ext (by dsimp [f] at hx; omega) (by dsimp [f] at hy; omega)

/-- The norm theta series counts the complete finite integer fibres. -/
noncomputable def normTheta : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.card (NormFiber n) : ℚ)

/-- This is a lattice series; no Euler-product identity is built into its definition. -/
noncomputable def coreTheta : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.card (CoreFiber n) : ℚ)

private theorem integer_sq_ge_self (x : ℤ) : x ≤ x ^ 2 := by
  by_cases h : x ≤ 0
  · nlinarith [sq_nonneg x]
  · have : 1 ≤ x := by omega
    nlinarith [sq_nonneg (x - 1)]

theorem core_fiber_zero (p : CoreFiber 0) : p.1 = (0, 0) := by
  have he := p.2
  have hs := core_shift_norm p.1
  have hc := norm_coercive (3 * p.1.1 - 1, 3 * p.1.2)
  rw [hs, he] at hc
  have hy : p.1.2 = 0 := by
    have : p.1.2 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (3 * p.1.1 - 1)]
    nlinarith [sq_nonneg p.1.2]
  have hx : p.1.1 = 0 := by
    have hxq := integer_sq_ge_self p.1.1
    have hxqn := integer_sq_ge_self (-p.1.1)
    dsimp at hc
    rw [hy] at hc
    nlinarith
  exact Prod.ext hx hy

theorem theta_nonnegative_and_normalized :
    (∀ n, 0 ≤ PowerSeries.coeff n normTheta) ∧
    (∀ n, 0 ≤ PowerSeries.coeff n coreTheta) ∧
    PowerSeries.constantCoeff normTheta = 1 ∧
    PowerSeries.constantCoeff coreTheta = 1 := by
  have hnorm : Nat.card (NormFiber 0) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨(0, 0), by norm_num [eisensteinNorm]⟩, ?_⟩
    intro p
    apply Subtype.ext
    have h := norm_coercive p.1
    rw [p.2] at h
    have hx : p.1.1 = 0 := by nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
    have hy : p.1.2 = 0 := by nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
    exact Prod.ext hx hy
  have hcore : Nat.card (CoreFiber 0) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    exact ⟨⟨(0, 0), by norm_num [coreExponent, eisensteinNorm]⟩,
      fun p => Subtype.ext (core_fiber_zero p)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n; simp [normTheta]
  · intro n; simp [coreTheta]
  · simpa [← PowerSeries.coeff_zero_eq_constantCoeff, normTheta] using
      congrArg (fun x : ℕ => (x : ℚ)) hnorm
  · simpa [← PowerSeries.coeff_zero_eq_constantCoeff, coreTheta] using
      congrArg (fun x : ℕ => (x : ℚ)) hcore

end D5.S3.Arith.ModularForms.CubicThetaLattice
