/- GID: D5/S3/Arith/Additive/NathansonProblem12AffineInvariance
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/NathansonProblem12AffineInvariance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nonzero affine images preserve the sum intersection set in Nathanson Problem 12. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#18994; Proved)
  Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19056.
The definitions retain the expressions in issue #18994; the namespace follows the module path.
The proof composes mul_left_cancel₀, add_right_cancel, Set.InjOn.image_iInter_eq,
nsmul_add, Set.image_nsmul, Set.nsmul_singleton and Set.image_eq_image from pinned Mathlib.
Both decreasing-family premises are unused; the multiplier premise supplies only s ≠ 0.
Utility kind=none: arbitrary integer sets and unbounded sum lengths; no finite instance is asserted.
-/

import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Set.Lattice.Image

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Additive.NathansonProblem12AffineInvariance

open scoped Pointwise

/-- Nathanson, arXiv:2604.04781, Section 2: a sequence of sets is decreasing if `A_q ⊇ A_{q+1}` for
all `q ∈ ℕ`, and a decreasing sequence is asymptotically strictly decreasing if `A_q ≠ A_{q+1}` for
infinitely many `q`. -/
def AsymptoticallyStrictlyDecreasing (A : ℕ+ → Set ℤ) : Prop :=
  (∀ q : ℕ+, A (q + 1) ⊆ A q) ∧ {q : ℕ+ | A q ≠ A (q + 1)}.Infinite

/-- The sum intersection set `H(A_q) = {h ∈ ℕ : hA = ⋂_q hA_q}` with `A = ⋂_q A_q`, where `hB` is the
`h`-fold sumset `{b₁ + ⋯ + b_h : bᵢ ∈ B}` (Mathlib's pointwise `h • B`). -/
def H (A : ℕ+ → Set ℤ) : Set ℕ :=
  {h : ℕ | 0 < h ∧ h • (⋂ q, A q) = ⋂ q, h • A q}

/-- Nathanson, arXiv:2604.04781, Problem 12: "Let (A_q) and (A′_q) be asymptotically strictly
decreasing sequences of sets of integers such that A′_q = sA_q + t for all q ∈ ℕ and some s, t ∈ ℤ
with s ∉ {0, ±1}. Does this imply H(A_q) = H(A′_q)?" Here `sA + t = {sa + t : a ∈ A}`. -/
def claim : Prop :=
  ∀ (A A' : ℕ+ → Set ℤ) (s t : ℤ),
    AsymptoticallyStrictlyDecreasing A → AsymptoticallyStrictlyDecreasing A' →
    (∀ q, A' q = (fun a => s * a + t) '' A q) → s ∉ ({0, 1, -1} : Set ℤ) →
    H A = H A'

end D5.S3.Arith.Additive.NathansonProblem12AffineInvariance

namespace D5.S3.Arith.Additive.NathansonProblem12AffineInvariance
open scoped Pointwise

theorem result : claim := by
  intro A A' s t _ _ hA' hs
  have hs0 : s ≠ 0 := by
    intro hs0
    exact hs (by simp [hs0])
  have hinj (u : ℤ) : Function.Injective (fun x : ℤ => s * x + u) := by
    intro x y hxy
    exact mul_left_cancel₀ hs0 (add_right_cancel hxy)
  have hsum (h : ℕ) (B : Set ℤ) :
      h • ((fun a : ℤ => s * a + t) '' B) =
        (fun x : ℤ => s * x + (h : ℤ) * t) '' (h • B) := by
    let f : ℤ →+ ℤ := AddMonoidHom.mulLeft s
    calc
      _ = h • (f '' B + {t}) := by
        rw [Set.add_singleton, Set.image_image]
        rfl
      _ = h • (f '' B) + h • ({t} : Set ℤ) := nsmul_add _ _ _
      _ = f '' (h • B) + {h • t} := by
        rw [← Set.image_nsmul, Set.nsmul_singleton]
      _ = _ := by
        rw [Set.add_singleton, Set.image_image]
        simp [f]
  have hinter (C : ℕ+ → Set ℤ) (u : ℤ) :
      (fun x : ℤ => s * x + u) '' (⋂ q, C q) =
        ⋂ q, (fun x : ℤ => s * x + u) '' C q :=
    (hinj u).injOn.image_iInter_eq
  have hbase : (⋂ q, A' q) = (fun a : ℤ => s * a + t) '' (⋂ q, A q) := by
    simp_rw [hA']
    exact (hinter A t).symm
  apply Set.ext
  intro h
  change (0 < h ∧ h • (⋂ q, A q) = ⋂ q, h • A q) ↔
    (0 < h ∧ h • (⋂ q, A' q) = ⋂ q, h • A' q)
  rw [hbase, hsum]
  simp_rw [hA', hsum]
  rw [← hinter]
  exact and_congr_right fun _ => (Set.image_eq_image (hinj ((h : ℤ) * t))).symm

end D5.S3.Arith.Additive.NathansonProblem12AffineInvariance
