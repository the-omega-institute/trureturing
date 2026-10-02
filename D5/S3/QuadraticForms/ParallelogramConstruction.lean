/- GID: D5/S3/QuadraticForms/ParallelogramConstruction
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ParallelogramConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lit/tauceti2026canonicalheight]
   utility: none
   digest: Injective doubling converts the parallelogram law into an integer quadratic map with its polar bilinear companion. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026canonicalheight.md.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# A function satisfying the parallelogram law is a quadratic form

Let `M` and `N` be additive commutative groups, suppose doubling is injective on `N`,
and let `f : M → N` satisfy the **parallelogram law**

```
f (x + y) + f (x - y) = 2 • f x + 2 • f y.
```

Then `f` is a quadratic form: its polarisation `QuadraticMap.polar f x y = f (x + y) - f x - f y`
is biadditive, and `f (n • x) = n ^ 2 • f x`. This file proves that, and packages it as a
`QuadraticMap ℤ M N`. Both `f 0 = 0` and evenness of `f` come free from the law rather than being
assumed.

Mathlib has the converse direction — `QuadraticMap.polar_add_left` and friends read biadditivity
*off* a `QuadraticMap`, and `LinearMap.BilinMap.toQuadraticMap` builds one from a bilinear map —
but nothing in the other direction from the parallelogram law alone. Its `parallelogram_law` and
`parallelogram_law_with_norm` are statements about inner product spaces, and the Jordan–von Neumann
construction in `Analysis/InnerProductSpace/OfNorm.lean` recovers an inner product from a *norm* on
a real or complex space, using continuity. Neither applies to a function on a bare abelian group.

Natural quadratic scaling needs only a right-cancellative additive monoid as target, and
therefore applies to targets with `2`-torsion.

## The quadratic-map construction requires absence of `2`-torsion

`htwo : IsSMulRegular N 2` says that doubling is injective on `N`. It is sharp in both directions.

It is *not* `IsAddTorsionFree N`, which is strictly stronger and excludes codomains where the
conclusion holds: `IsSMulRegular (ZMod 3) 2` is true even though `ZMod 3` has `3`-torsion.

Nor can it be weakened away. With `M = N = ZMod 2` *every* function satisfies the parallelogram
law, because `x - y = x + y` and `2 • z = 0` there; the constant function `1` is then one that
satisfies it while failing even `f 0 = 0`, which every quadratic form obeys — and correspondingly
`¬ IsSMulRegular (ZMod 2) 2`. Even assuming `f 0 = 0` is insufficient for biadditivity:
on `(ZMod 2)³`, the function `f(x) = x₁x₂x₃` satisfies the law and preserves zero, but violates
the three-variable identity at the three standard basis vectors.

For a torsion-free codomain it is one term: `smul_right_injective N two_ne_zero` supplies it for
`N = ℝ`, the canonical height's target, and for `N = ℤ`, the degree form's.

## Main results

* `TauCeti.QuadraticMap.ofParallelogram`: the integer quadratic map with its
  polarisation as companion bilinear map. Its construction derives the three-variable
  identity and integer quadratic scaling from the parallelogram law.

## Where this is used

Two constructions in arithmetic geometry arrive at a function *known to satisfy the parallelogram
law* and want it as a quadratic form.

The canonical height of an elliptic curve is one. It satisfies the parallelogram law exactly, and
its polarisation is the Néron–Tate height pairing **up to a factor of two**: by
`QuadraticMap.polar_self` the polarisation here has `polar f x x = 2 • f x`, whereas the pairing
whose Gram determinant on a basis of the free part of the Mordell–Weil group is the regulator is
normalised so that `⟨P, P⟩` is the height itself. A consumer wanting the regulator convention
halves this one; the choice is not made here, since halving is not available in a general abelian
group.

The degree form on `End E` is the other: its polarisation is the trace form, and non-negativity of
the degree gives the Hasse bound by Cauchy–Schwarz (Silverman, *The Arithmetic of Elliptic
Curves*, V.1.2).

Both take values in a torsion-free group — `ℝ` and `ℤ` respectively — so both satisfy the
hypothesis below with room to spare. Stated for a general abelian group so that neither carries
its own copy.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {f : M → N}
  (htwo : IsSMulRegular N (2 : ℕ))
  (hf : ∀ x y : M, f (x + y) + f (x - y) = 2 • f x + 2 • f y)

include htwo hf

/-- **A function satisfying the parallelogram law is a quadratic form.** Its companion bilinear
map is `QuadraticMap.polarBilin` of it, which is the polarisation. -/
def ofParallelogram : _root_.QuadraticMap ℤ M N := by
  have hzero : f 0 = 0 := by
    apply htwo
    apply add_left_cancel (a := 2 • f 0)
    simpa only [add_zero, sub_zero, smul_zero, two_nsmul] using (hf 0 0).symm
  have hneg (x : M) : f (-x) = f x := by
    have h₀ : 2 • f 0 = 0 := by
      apply add_left_cancel (a := 2 • f 0)
      simpa only [add_zero, sub_zero, two_nsmul] using (hf 0 0).symm
    apply add_left_cancel (a := f x)
    simpa only [zero_add, zero_sub, h₀, two_nsmul] using hf 0 x
  have hnsmul (n : ℕ) (x : M) : f (n • x) = (n * n) • f x := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using hzero
    | one => simp
    | more n ih ih' =>
      have h := hf ((n + 1) • x) x
      rw [← succ_nsmul x (n + 1), show (n + 1) • x - x = n • x by
        rw [succ_nsmul, add_sub_cancel_right], ih, ih'] at h
      apply add_right_cancel (b := (n * n) • f x)
      calc
        f ((n + 2) • x) + (n * n) • f x =
            2 • ((n + 1) * (n + 1)) • f x + 2 • f x := h
        _ = ((n + 2) * (n + 2)) • f x + (n * n) • f x := by
          rw [smul_smul, ← add_nsmul, ← add_nsmul]
          congr 1
          ring
  have hscale (n : ℤ) (x : M) : f (n • x) = (n * n) • f x := by
    obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa only [← Int.natCast_mul, natCast_zsmul] using
        hnsmul m x
    · rw [neg_zsmul, hneg, neg_mul_neg]
      simpa only [← Int.natCast_mul, natCast_zsmul] using
        hnsmul m x
  have hthree (x y z : M) :
      f (x + y + z) + (f x + f y + f z) = f (x + y) + f (y + z) + f (z + x) := by
    rw [show z + x = x + z from by abel]
    have p1 := hf (x + y) z
    have p2 := hf x (y - z)
    have p3 := hf y z
    have p4 := hf (x + z) y
    rw [show x + y - z = x + (y - z) by abel] at p1
    rw [show x - (y - z) = x + z - y by abel] at p2
    rw [show x + z + y = x + y + z by abel] at p4
    apply htwo
    linear_combination (norm := module) p1 + p4 - p2 - (2 : ℤ) • p3
  have hpolarAdd (x x' y : M) :
      polar f (x + x') y = polar f x y + polar f x' y :=
    polar_add_left_iff.mpr <| hthree x x' y
  have hpolarScale (a : ℤ) (x y : M) :
      polar f (a • x) y = a • polar f x y :=
    AddMonoidHom.map_zsmul
      (AddMonoidHom.mk' (polar f · y) fun p q ↦ hpolarAdd p q y) a x
  exact .ofPolar f hscale hpolarAdd hpolarScale

end QuadraticMap

end TauCeti
