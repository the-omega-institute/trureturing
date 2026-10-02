/- GID: D5/S3/Factorization/Mordell/CanonicalPointHeight
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/CanonicalPointHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The doubling height sequence converges uniformly up to bounded comparison and yields the exact parallelogram law. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026canonicalheight.md.
Authors: The Tau Ceti contributors
-/
module

public import D5.S3.Factorization.Mordell.SymmetricSquareAddition
public import Mathlib.NumberTheory.Height.EllipticCurve
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Order.Northcott
import D5.S3.QuadraticForms.ParallelogramConstruction

/-!
# The canonical (Néron–Tate) height

The naïve height `h` is quadratic only up to a bounded error: the proof below gives a
constant `C` with `|h(P + Q) + h(P - Q) - 2(h P + h Q)| ≤ C`. Tate's observation is that averaging
that error away along the doubling map removes it. This file carries
out that construction and records the facts that pin the definition down: the limit exists, it
stays within a bounded distance of half of `h`, and it is *honestly* quadratic — it satisfies
the parallelogram law exactly, which is
what the whole averaging was for.

`canonicalHeight P = (1/2) · lim_{n → ∞} h(2ⁿ P) / 4ⁿ`

The factor `1/2` is the standard normalisation and is not cosmetic. The naïve height here is the
height of the `x`-coordinate, and `x` has a *double* pole at the point at infinity, so `h_x` is the
height attached to the divisor `2(O)`. Heights scale linearly in the divisor, so the height
attached to `(O)` — the one the Néron–Tate pairing, the regulator and the BSD formula are stated
with — is half of it. Getting this wrong would scale every later invariant.

## Main definitions

* `WeierstrassCurve.Affine.Point.canonicalHeight`: the limit above.
The exact parallelogram law lets a consumer construct the associated `ℤ`-quadratic map using
`TauCeti.QuadraticMap.ofParallelogram`.

## Main results

`Point.canonicalHeight_properties` proves convergence, bounded comparison with half the naïve
height, and the exact parallelogram law in one construction. The quadratic map and Northcott
finiteness supply the zero-height torsion argument where it is needed.

## Implementation notes

The doubling bound `|h(2P) - 4 h(P)| ≤ C` is the approximate parallelogram law at `Q = P`, where
`P - Q = 0` and `h(0) = 0`. **Convergence** needs only that specialisation;
the exact parallelogram clause needs the full two-point law.

Convergence is `cauchySeq_of_le_geometric` at ratio `1/4`: consecutive terms of
`h(2ⁿ P) / (2 · 4ⁿ)` differ by
`|h(2 · 2ⁿ P) - 4 h(2ⁿ P)| / (2 · 4ⁿ⁺¹) ≤ C / (2 · 4ⁿ⁺¹) = (C/8) · (1/4)ⁿ`. The same estimate
feeds Mathlib's
`dist_le_of_le_geometric_of_tendsto₀`, which bounds the distance from the *zeroth* term — and the
zeroth term is `h(P) / 2` — giving `|canonicalHeight P - h(P)/2| ≤ (C / 8) / (1 - 1/4) = C / 6`
with no further work.

The `[DecidableEq F]` hypothesis is not incidental: `W.Point`'s `AddCommGroup` instance needs it,
since the addition formula case-splits on whether the two points share an `x`-coordinate. Without
it `2 ^ n • P` does not elaborate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

open Filter Height Topology

namespace WeierstrassCurve.Affine

open Height

/-- The logarithmic height of the homogeneous x-coordinate, including infinity. -/
@[expose] noncomputable def Point.naiveHeight {F : Type*} [Field F]
    [AdmissibleAbsValues F] {W : Affine F} (P : W.Point) : ℝ :=
  logHeight P.xRep

variable {F : Type*} [Field F] {W : Affine F} [AdmissibleAbsValues F] [DecidableEq F]

/-- **The canonical (Néron–Tate) height** `canonicalHeight P = lim h(2ⁿ P) / (2 · 4ⁿ)`.

The `2` is the standard normalisation: `h` is the height of the `x`-coordinate, which has a double
pole at infinity, so `h` is attached to `2(O)` and the Néron–Tate height to `(O)` is half of it.

The limit exists whenever the curve is elliptic
  (as one clause of `Point.canonicalHeight_properties`); the definition itself needs no hypothesis
beyond those making `2 ^ n • P` meaningful, so it is stated without one. -/
@[expose] noncomputable def Point.canonicalHeight (P : W.Point) : ℝ :=
  limUnder atTop fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n)

/-- The canonical-height construction converges, stays at bounded distance from half the naïve
height, and satisfies the exact parallelogram law. The shared proof obtains its bounded defect
from the group-law identity on the symmetric square of the `x`-coordinates. -/
theorem Point.canonicalHeight_properties [W.toAffine.IsElliptic] :
    (∀ P : W.Point, Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n))
      atTop (𝓝 P.canonicalHeight)) ∧
    (∃ D, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight / 2| ≤ D) ∧
    (∀ P Q : W.Point, (P + Q).canonicalHeight + (P - Q).canonicalHeight =
      2 * (P.canonicalHeight + Q.canonicalHeight)) := by
  have happrox : ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight -
        2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
    have hsym : ∃ C, ∀ P Q : W.Point,
        |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
      obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
      refine ⟨C, fun P Q ↦ ?_⟩
      have hsym2x : P.sym2x Q =
          ![P.xRep 0 * Q.xRep 0,
            P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
            P.xRep 1 * Q.xRep 1] := by
        cases P <;> cases Q <;> simp (config := { congrConsts := false }) [← Point.zero_def]
      simp (config := { congrConsts := false }) only [Point.naiveHeight, hsym2x]
      have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
      have H (v : Fin 2 → F) : ![v 0, v 1] = v := by
        ext i : 1
        fin_cases i <;> simp (config := { congrConsts := false })
      have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
      specialize hC (h₀ P) (h₀ Q)
      rw [H P.xRep, H Q.xRep] at *
      grind only [= abs.eq_1, = max_def]
    obtain ⟨C₁, hC₁⟩ := hsym
    obtain ⟨C₂, hC₂⟩ := WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
    refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
    obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
    replace ht := congrArg logHeight ht
    rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
    have hPQ := hC₁ P Q
    have haddsub := hC₁ (P + Q) (P - Q)
    have hC := ht ▸ hC₂ (P.sym2x Q)
    generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
    generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
    generalize logHeight (P.sym2x Q) = B' at hPQ hC
    generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
    grind only [= abs.eq_1, = max_def]
  obtain ⟨C, hbound⟩ := happrox
  have hC (Q : W.Point) : |(2 • Q).naiveHeight - 4 * Q.naiveHeight| ≤ C := by
    have h := hbound Q Q
    have hz : (0 : W.Point).naiveHeight = 0 := by
      simp (config := { congrConsts := false }) [Point.naiveHeight, Point.xRep_zero]
    rw [sub_self, hz] at h
    rw [two_nsmul]
    convert h using 2
    ring
  have hstep (P : W.Point) (n : ℕ) :
      dist (((2 ^ n) • P).naiveHeight / (2 * 4 ^ n))
          (((2 ^ (n + 1)) • P).naiveHeight / (2 * 4 ^ (n + 1)))
        ≤ C / 8 * (1 / 4) ^ n := by
    have key : ((2 : ℕ) ^ (n + 1)) • P = 2 • (((2 : ℕ) ^ n) • P) := by
      rw [smul_smul]; congr 1; ring
    have e : ((2 : ℕ) ^ n • P).naiveHeight / (2 * 4 ^ n)
          - ((2 : ℕ) ^ (n + 1) • P).naiveHeight / (2 * 4 ^ (n + 1))
        = (4 * ((2 : ℕ) ^ n • P).naiveHeight - (2 • ((2 : ℕ) ^ n • P)).naiveHeight)
            / (2 * 4 ^ (n + 1)) := by
      rw [key]; field_simp [pow_succ]; ring
    rw [Real.dist_eq, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * 4 ^ (n + 1)),
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * 4 ^ (n + 1))]
    have h := hC ((2 : ℕ) ^ n • P)
    rw [abs_sub_comm] at h
    calc |4 * ((2 : ℕ) ^ n • P).naiveHeight - (2 • ((2 : ℕ) ^ n • P)).naiveHeight| ≤ C := h
      _ = C / 8 * (1 / 4 : ℝ) ^ n * (2 * 4 ^ (n + 1)) := by
          have h1 : ((1 : ℝ) / 4) ^ n * 4 ^ n = 1 := by rw [← mul_pow]; norm_num
          linear_combination (-C) * h1
  have hlim (P : W.Point) :
      Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n)) atTop
        (𝓝 P.canonicalHeight) :=
    (cauchySeq_of_le_geometric (1 / 4) (C / 8) (by norm_num)
      (hstep P)).tendsto_limUnder
  have hbounded : ∃ D, ∀ P : W.Point,
      |P.canonicalHeight - P.naiveHeight / 2| ≤ D := by
    refine ⟨C / 8 / (1 - 1 / 4), fun P ↦ ?_⟩
    have hd := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (C / 8) (by norm_num)
      (hstep P) (hlim P)
    simpa (config := { congrConsts := false }) [Real.dist_eq, abs_sub_comm] using hd
  have hlaw (P Q : W.Point) :
      (P + Q).canonicalHeight + (P - Q).canonicalHeight =
        2 * (P.canonicalHeight + Q.canonicalHeight) := by
    set f : W.Point → ℕ → ℝ := fun X n ↦ ((2 ^ n) • X).naiveHeight / (2 * 4 ^ n) with hf
    have hlimits : ∀ X : W.Point, Tendsto (f X) atTop (𝓝 X.canonicalHeight) :=
      fun X ↦ hlim X
    have hg : Tendsto (fun n ↦ f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)) atTop
        (𝓝 ((P + Q).canonicalHeight + (P - Q).canonicalHeight
              - 2 * (P.canonicalHeight + Q.canonicalHeight))) :=
      ((hlimits _).add (hlimits _)).sub (((hlimits _).add (hlimits _)).const_mul 2)
    have hscaled : ∀ n,
        ‖f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)‖ ≤ C / 4 ^ n := by
      intro n
      have h := hbound ((2 ^ n) • P) ((2 ^ n) • Q)
      rw [← smul_add, ← smul_sub] at h
      simp (config := { congrConsts := false }) only [hf, Real.norm_eq_abs]
      rw [show f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)
          = (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight
              - 2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)) / (2 * 4 ^ n) from by
        simp (config := { congrConsts := false }) only [hf]; field_simp]
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * 4 ^ n),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h, abs_nonneg (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight
        - 2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)),
        pow_pos (by norm_num : (0 : ℝ) < 4) n]
    have hzero : Tendsto (fun n ↦ f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm hscaled ?_
      simpa (config := { congrConsts := false }) using (tendsto_const_nhds (x := C)).div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))
    linarith [tendsto_nhds_unique hg hzero]
  exact ⟨hlim, hbounded, hlaw⟩

end WeierstrassCurve.Affine
