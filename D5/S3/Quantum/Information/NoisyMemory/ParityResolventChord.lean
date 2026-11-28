/- GID: D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/NoisyMemory/ParityResolventChord
   mirror-E: none(waiver:analytic-collision-comparison)
   anchors: []
   utility: none
   digest: A quadratic inverse has a sharp squared-attenuation upper chord. -/

import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Variational estimate for attenuating the odd part of a quadratic inverse.
The even and odd sectors may be the real Hilbert–Schmidt subspaces of a
matrix involution. The parameter multiplies both the odd source and the
off-diagonal coupling.
-/

namespace ParityResolventChord

open scoped InnerProductSpace
set_option autoImplicit false

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- The variational objective for a quadratic form with an attenuated coupling. -/
def trialValue (B : E →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : F →ₗ[ℝ] E)
    (x : E) (y : F) (a : ℝ) (u : E) (v : F) : ℝ :=
  2 * ⟪u, x⟫_ℝ - ⟪u, B u⟫_ℝ +
    2 * a * ⟪v, y⟫_ℝ - 2 * a * ⟪u, C v⟫_ℝ - ⟪v, D v⟫_ℝ

private theorem trialValue_attenuated
    (B : E →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : F →ₗ[ℝ] E)
    (x : E) (y : F) (a : ℝ) (u : E) (v : F) :
    trialValue B D C x y a u (a • v) =
      (1 - a ^ 2) * trialValue B D C x y 0 u 0 +
        a ^ 2 * trialValue B D C x y 1 u v := by
  simp only [trialValue, map_smul, real_inner_smul_left, real_inner_smul_right,
    map_zero, inner_zero_left, inner_zero_right]
  ring

/-- The supremal inverse quadratic objective has an upper chord with weight a². -/
theorem sSup_trialValue_chord
    (B : E →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : F →ₗ[ℝ] E)
    (x : E) (y : F) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (h₀ : BddAbove (Set.range fun z : E × F => trialValue B D C x y 0 z.1 z.2))
    (h₁ : BddAbove (Set.range fun z : E × F => trialValue B D C x y 1 z.1 z.2)) :
    sSup (Set.range fun z : E × F => trialValue B D C x y a z.1 z.2) ≤
      (1 - a ^ 2) * sSup (Set.range fun z : E × F => trialValue B D C x y 0 z.1 z.2) +
        a ^ 2 * sSup (Set.range fun z : E × F => trialValue B D C x y 1 z.1 z.2) := by
  by_cases hz : a = 0
  · subst a
    simp
  have hweight : 0 ≤ 1 - a ^ 2 := sub_nonneg.mpr
    (by nlinarith [mul_nonneg ha₀ (sub_nonneg.mpr ha₁)])
  have hne : (Set.range fun z : E × F => trialValue B D C x y a z.1 z.2).Nonempty :=
    Set.range_nonempty _
  apply csSup_le hne
  rintro _ ⟨⟨u, w⟩, rfl⟩
  let v : F := a⁻¹ • w
  have hw : a • v = w := by
    simp [v, smul_smul, mul_inv_cancel₀ hz]
  change trialValue B D C x y a u w ≤ _
  rw [← hw, trialValue_attenuated]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (le_csSup h₀ ⟨(u, 0), rfl⟩) hweight)
    (mul_le_mul_of_nonneg_left (le_csSup h₁ ⟨(u, v), rfl⟩) (sq_nonneg a))

/-- A nonnegative symmetric quadratic form attains its variational optimum at
any solution of the linear equation with the prescribed source. -/
theorem variationalValue_eq_inner_of_solve
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (hpos : ∀ z, 0 ≤ ⟪z, A z⟫_ℝ)
    {r w : E} (hw : A w = r) :
    sSup (Set.range fun z : E => 2 * ⟪z, r⟫_ℝ - ⟪z, A z⟫_ℝ) = ⟪w, r⟫_ℝ := by
  have hbound (z : E) : 2 * ⟪z, r⟫_ℝ - ⟪z, A z⟫_ℝ ≤ ⟪w, r⟫_ℝ := by
    have hsq := hpos (z - w)
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hw] at hsq
    have hcross : ⟪w, A z⟫_ℝ = ⟪z, r⟫_ℝ := by
      rw [← hA w z, hw, real_inner_comm]
    linarith
  have hbdd : BddAbove (Set.range fun z : E => 2 * ⟪z, r⟫_ℝ - ⟪z, A z⟫_ℝ) :=
    ⟨_, by
      rintro _ ⟨z, rfl⟩
      exact hbound z⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact hbound z
  · apply le_csSup hbdd
    refine ⟨w, ?_⟩
    change 2 * ⟪w, r⟫_ℝ - ⟪w, A w⟫_ℝ = ⟪w, r⟫_ℝ
    rw [hw]
    ring

#print axioms sSup_trialValue_chord
#print axioms variationalValue_eq_inner_of_solve

end ParityResolventChord
