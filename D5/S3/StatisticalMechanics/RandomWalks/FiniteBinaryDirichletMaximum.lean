/- GID: D5/S3/StatisticalMechanics/RandomWalks/FiniteBinaryDirichletMaximum
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/RandomWalks/FiniteBinaryDirichletMaximum
   mirror-E: none(waiver:abstract-matrix-family)
   anchors: []
   utility: none
   digest: A two-successor maximum principle with absorbing exit paths. -/

/-
proof_shape: maximum_zero_of_two_successor_exit: content.
Helper: convex_max_propagates: bind-only; consumer maximum_zero_of_two_successor_exit.
escape_witness: maximum_zero_of_two_successor_exit: induction along positive-weight exit paths.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
Utility: none; all parameters are arbitrary, with no finite-instance certificate or enumeration.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace D5.S3.StatisticalMechanics.RandomWalks.FiniteBinaryDirichletMaximum

private theorem convex_max_propagates (a b x y z M : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x = a*y + b*z) (hm : |x| = M)
    (hy : |y| ≤ M) (hz : |z| ≤ M) :
    (0 < a → |y| = M) ∧ (0 < b → |z| = M) := by
  have hh : M ≤ a*|y|+b*|z| := by
    rw [← hm, hx]
    calc
      _ ≤ |a*y|+|b*z| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have h₁ : 0 ≤ a*(M-|y|) := mul_nonneg ha (sub_nonneg.mpr hy)
  have h₂ : 0 ≤ b*(M-|z|) := mul_nonneg hb (sub_nonneg.mpr hz)
  have hbudget : a*M + b*M = M := by rw [← add_mul, hab, one_mul]
  have hs : a*(M-|y|) + b*(M-|z|) ≤ 0 := by nlinarith [hbudget]
  constructor
  · intro hpos
    have hzero : a*(M-|y|) = 0 := by linarith
    have := (mul_eq_zero.mp hzero).resolve_left hpos.ne'
    linarith
  · intro hpos
    have hzero : b*(M-|z|) = 0 := by linarith
    have := (mul_eq_zero.mp hzero).resolve_left hpos.ne'
    linarith

/-- The maximum principle only needs a uniform bound, an attained maximum, and exit paths. -/
theorem maximum_zero_of_two_successor_exit {S : Type*}
    (f : S → ℝ) (M : ℝ) (boundary : S → Prop) (l r : S → S) (a b : S → ℝ)
    (hbound : ∀ s, |f s| ≤ M) (hattain : ∃ s, |f s| = M)
    (hboundary : ∀ s, boundary s → f s = 0)
    (hweights : ∀ s, ¬boundary s → 0 ≤ a s ∧ 0 ≤ b s ∧ a s + b s = 1)
    (hharmonic : ∀ s, ¬boundary s → f s = a s*f (l s) + b s*f (r s))
    (hexit : ∀ s, ∃ t, boundary t ∧ Relation.ReflTransGen
      (fun s t => ¬boundary s ∧ ((0 < a s ∧ l s = t) ∨ (0 < b s ∧ r s = t))) s t) : M = 0 := by
  obtain ⟨s, hs⟩ := hattain
  obtain ⟨t, ht, hpath⟩ := hexit s
  have he : |f t|=M := by
    clear ht
    induction hpath with
    | refl => exact hs
    | @tail u v hp huv ih =>
      obtain ⟨ha, hb, hab⟩ := hweights u huv.1
      have hprop := convex_max_propagates (a u) (b u) (f u) (f (l u)) (f (r u)) M
        ha hb hab (hharmonic u huv.1) ih (hbound _) (hbound _)
      rcases huv.2 with ⟨hpos, rfl⟩ | ⟨hpos, rfl⟩
      · exact hprop.1 hpos
      · exact hprop.2 hpos
  rw [hboundary t ht, abs_zero] at he
  exact he.symm
end D5.S3.StatisticalMechanics.RandomWalks.FiniteBinaryDirichletMaximum
