/- GID: D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Native counting and inverse definitions for the whole A252505 convolution. -/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution

open Finset ArithmeticFunction
noncomputable section

/-- No prime fourth power divides the positive integer being counted. -/
def FourthPowerFree (d : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ 4 ∣ d

/-- A252505, defined by its positive-divisor counting problem. -/
def a (n : ℕ) : ℤ := by
  classical
  exact ((n.divisors.filter (fun d => FourthPowerFree d)).card : ℤ)

/-- The original rational equation, including equal denominators. -/
def UnitFractionPair (n : ℕ) (xy : ℕ × ℕ) : Prop :=
  0 < xy.1 ∧ 0 < xy.2 ∧ xy.1 ≤ xy.2 ∧
    (1 / (n : ℚ) = 1 / (xy.1 : ℚ) + 1 / (xy.2 : ℚ))

/-- A018892 counts the actual positive solutions, rather than a divisor formula. -/
def b (n : ℕ) : ℤ := (Nat.card {xy : ℕ × ℕ // UnitFractionPair n xy} : ℤ)

/-- Ordinary positive divisor count. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- A140773 uses the ordinary ceiling after rational division. -/
def h (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (⌈(tau d : ℚ) / 2⌉₊ : ℤ)

/-- A369255 is the integer remainder, with values zero and one. -/
def g (n : ℕ) : ℤ := h n % 2

private theorem g_one : g 1 = 1 := by
  norm_num [g, h, tau]

private def gFunction : ArithmeticFunction ℤ :=
  ⟨g, by simp [g, h]⟩

private def gOneInvertible : Invertible (gFunction 1) := by
  have he : gFunction 1 = 1 := g_one
  rw [he]
  infer_instance

/-- A378214, the canonical recursive Dirichlet inverse of the independently defined g. -/
def c (n : ℕ) : ℤ := ArithmeticFunction.dirichletInverse gFunction gOneInvertible n

/-- The unchanged all-positive-integer OEIS A252505 conjecture. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n = ∑ d ∈ n.divisors, b d * c (n / d)

/-- The independent source recursion, without its irrelevant value at zero. -/
def InverseRecursion (v : ℕ → ℤ) : Prop :=
  v 1 = 1 ∧ ∀ n : ℕ, 1 < n →
    v n = - ∑ d ∈ n.properDivisors, g (n / d) * v d

private theorem unit_fraction_iff_factor {n x y : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    (1 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ)) ↔
      n < x ∧ n < y ∧ (x - n) * (y - n) = n ^ 2 := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  have heq : (1 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ)) ↔
      x * y = n * (x + y) := by
    constructor
    · intro H
      field_simp at H
      exact_mod_cast (show (x : ℚ) * y = n * (x + y) by nlinarith [H])
    · intro H
      have Hq : (x : ℚ) * y = n * (x + y) := by exact_mod_cast H
      field_simp
      nlinarith [Hq]
  rw [heq]
  constructor
  · intro H
    have hnx : n < x := by
      by_contra hh
      have hh' : x ≤ n := by omega
      have := Nat.mul_le_mul_right y hh'
      nlinarith
    have hny : n < y := by
      by_contra hh
      have hh' : y ≤ n := by omega
      have := Nat.mul_le_mul_left x hh'
      nlinarith
    refine ⟨hnx, hny, ?_⟩
    have hxn : x = n + (x - n) := by omega
    have hyn : y = n + (y - n) := by omega
    nlinarith
  · rintro ⟨hnx, hny, H⟩
    have hxn : x = n + (x - n) := by omega
    have hyn : y = n + (y - n) := by omega
    nlinarith

end
end D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
