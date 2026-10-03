/- GID: D5/S3/Factorization/Mordell/SymmetricSquareAddition
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/SymmetricSquareAddition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric-square point coordinates satisfy the homogeneous addition and subtraction identity. -/

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026canonicalheight.md.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination

public section

namespace WeierstrassCurve.Affine.Point

attribute [simp] sym2x_neg_left sym2x_neg_right

variable {F : Type*} [Field F] {W : Affine F}

variable [DecidableEq F]

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = (addSubMap W · |>.eval <| sym2x P Q) := by
  have hden_or_num {x y : F} (h : W.Nonsingular x y) :
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
        x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
    have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
    rw [equation_iff x y] at h₁
    by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
    · right
      replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
      contrapose h₂
      rw [b₄, b₆, b₈] at h₂
      grobner
    · left
      clear h₂
      contrapose H
      rw [b₂, b₄, b₆] at H
      grobner
  have hsym2x {A B : W.Point} :
      sym2x A B =
        ![A.xRep 0 * B.xRep 0,
          A.xRep 0 * B.xRep 1 + A.xRep 1 * B.xRep 0,
          A.xRep 1 * B.xRep 1] := by
    cases A <;> cases B <;> simp [← zero_def]
  have hselfEq (A : W.Point) :
      sym2x A A = (addSubMap W · |>.eval <| sym2x A 0) := by
    match A with
    | 0 => ext i : 1; fin_cases i <;> simp [addSubMap]
    | some .. => ext i : 1; fin_cases i <;> simp [pow_two, two_mul, addSubMap]
  have haddSubSomeSome {xP yP xQ yQ : F}
      (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) :
      (addSubMap W · |>.eval <| sym2x (some xP yP hP) (some xQ yQ hQ)) =
        ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
          2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) +
            W.b₄ * (xP + xQ) + W.b₆, (xP - xQ) ^ 2] := by
    ext i : 1
    fin_cases i <;> simp [addSubMap]
    ring
  have haddSubSomeSelf {x y : F} (h : W.Nonsingular x y) :
      (addSubMap W · |>.eval <| sym2x (some x y h) (some x y h)) =
        ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
          4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
    rw [haddSubSomeSome]
    ext i : 1
    fin_cases i <;> dsimp <;> ring
  have hdenZero {x y : F} (heq : W.Equation x y) :
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 ↔
        y = W.negY x y := by
    have hden : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
      have H := (W.equation_iff x y).mp heq
      simp only [b₂, b₄, b₆]
      linear_combination -4 * H
    rw [hden, sq_eq_zero_iff, negY]
    grind only
  have haddXSelf {x y : F} (heq : W.Equation x y)
      (hn : y ≠ W.negY x y) :
      W.addX x x (W.slope x x y y) =
        (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
    have hden : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
      have H := (W.equation_iff x y).mp heq
      simp only [b₂, b₄, b₆]
      linear_combination -4 * H
    have hn' := (hdenZero heq).not.mpr hn
    have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
    refine mul_left_cancel₀ hn' ?_
    have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
      rw [hden] at hn'
      grind
    rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
    simp only [slope, ↓reduceIte, hn]
    rw [negY, show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring, div_pow]
    nth_rewrite 1 2 [hden]
    rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
    linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp heq
  have haddX {x₁ y₁ x₂ y₂ : F} (hn : x₁ ≠ x₂) :
      W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) =
        ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
          (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) / (x₁ - x₂) ^ 2 := by
    grind only [addX, slope]
  have hxRepSelf {x y : F} (h : W.Nonsingular x y)
      (hn : y ≠ W.negY x y) :
      (some x y h + some x y h).xRep =
        ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
    simp only [add_self_of_Y_ne hn, ← haddXSelf h.1 hn, xRep_some]
  have hxRepAdd {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
      (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
      (some xP yP hP + some xQ yQ hQ).xRep =
        ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
          (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) / (xP - xQ) ^ 2, 1] := by
    simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some, haddX hn]
  have hxRepSub {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
      (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
      (some xP yP hP - some xQ yQ hQ).xRep =
        ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 +
          W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ) -
          (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) / (xP - xQ) ^ 2, 1] := by
    simp only [sub_eq_add_neg (some ..), neg_some hQ,
      add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn,
      xRep_some, haddX hn]
    grind only [negY]
  have hself (A : W.Point) :
      ∃ t : F, t ≠ 0 ∧ t • sym2x (A + A) 0 =
        (addSubMap W · |>.eval <| sym2x A A) := by
    match A with
    | 0 => exact ⟨1, one_ne_zero, by ext i : 1; fin_cases i <;> simp [addSubMap]⟩
    | some x y h =>
      rw [haddSubSomeSelf]
      by_cases H : y = W.negY x y
      · have H' := (hdenZero h.1).mpr H
        rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
        refine ⟨_, (hden_or_num h).neg_resolve_left H', ?_⟩
        simp
      · have H' := (hdenZero h.1).not.mpr H
        exact ⟨_, H', by simp [hsym2x, hxRepSelf h H, mul_div_cancel₀ _ H']⟩
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using hself P
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_comm] using hself P
  match P, Q with
  | P, 0 => exact ⟨1, one_ne_zero, by simpa using hselfEq P⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_comm] using hselfEq Q
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := by
      intro Heq
      rcases X_eq_iff.mp Heq with h | h
      · exact hPQ h
      · exact hPQ' (by simpa only [neg_neg] using congrArg Neg.neg h.symm)
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 (sub_ne_zero_of_ne hxPQ), ?_⟩
    rw [haddSubSomeSome, hsym2x, hxRepAdd hP hQ hxPQ,
      hxRepSub hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i : 1
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    fin_cases i <;> simp [field] <;> grobner

end WeierstrassCurve.Affine.Point
