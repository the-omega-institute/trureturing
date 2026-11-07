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
import Mathlib.SetTheory.Cardinal.Finite

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
  have hc : ⌈(1 : ℚ) / 2⌉₊ = 1 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num [g, h, tau, hc]

private def gFunction : ArithmeticFunction ℤ :=
  ⟨g, by simp [g, h]⟩

private def gOneInvertible : Invertible (gFunction 1) := by
  have he : gFunction 1 = 1 := g_one
  rw [he]
  exact invertibleOne

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


/-- Positive factor pairs, ordered by size; the diagonal is retained. -/
def factorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n ^ 2).divisorsAntidiagonal.filter (fun uv => uv.1 ≤ uv.2)

private def unitFractionEquiv (n : ℕ) (hn : 0 < n) :
    {xy : ℕ × ℕ // UnitFractionPair n xy} ≃ ↥(factorPairs n) where
  toFun xy := by
    have H := (unit_fraction_iff_factor hn xy.property.1 xy.property.2.1).mp
      xy.property.2.2.2
    exact ⟨(xy.val.1 - n, xy.val.2 - n),
      Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
        ⟨H.2.2, pow_ne_zero _ hn.ne'⟩,
        Nat.sub_le_sub_right xy.property.2.2.1 n⟩⟩
  invFun uv := by
    have H := Finset.mem_filter.mp uv.property
    have hu := Nat.left_ne_zero_of_mem_divisorsAntidiagonal H.1
    have hv := Nat.right_ne_zero_of_mem_divisorsAntidiagonal H.1
    refine ⟨(n + uv.val.1, n + uv.val.2), ?_⟩
    refine ⟨by omega, by omega, by simpa using H.2, ?_⟩
    apply (unit_fraction_iff_factor hn (by omega) (by omega)).mpr
    refine ⟨by omega, by omega, ?_⟩
    simpa using (Nat.mem_divisorsAntidiagonal.mp H.1).1
  left_inv xy := by
    apply Subtype.ext
    have H := (unit_fraction_iff_factor hn xy.property.1 xy.property.2.1).mp
      xy.property.2.2.2
    exact Prod.ext (by dsimp; omega) (by dsimp; omega)
  right_inv uv := by
    apply Subtype.ext
    simp

/-- The actual rational solutions are counted by the ordered positive factor pairs. -/
theorem unit_fraction_count (n : ℕ) (hn : 0 < n) :
    b n = ((factorPairs n).card : ℤ) := by
  have H := Nat.card_congr (unitFractionEquiv n hn)
  simpa only [b, Nat.card_eq_fintype_card, Fintype.card_coe] using
    congrArg (fun k : ℕ => (k : ℤ)) H

private theorem c_recursion : InverseRecursion c := by
  letI : Invertible (gFunction 1) := gOneInvertible
  have hi : ⅟(gFunction 1) = 1 := invOf_eq_iff_right.mpr (by
    change g 1 * 1 = 1
    rw [g_one, mul_one])
  constructor
  · change ArithmeticFunction.dirichletInverseFun gFunction gOneInvertible 1 = 1
    rw [ArithmeticFunction.dirichletInverseFun_apply_one, hi]
  · intro n hn
    change ArithmeticFunction.dirichletInverseFun gFunction gOneInvertible n = _
    rw [ArithmeticFunction.dirichletInverseFun_apply_ne (by omega) (by omega), hi]
    simp only [neg_mul, one_mul]
    rfl

/-- The source recursion has a unique positive-domain solution. -/
theorem inverse_recursion_unique (v : ℕ → ℤ) (hv : InverseRecursion v) :
    ∀ n : ℕ, 0 < n → v n = c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      exact hv.1.trans c_recursion.1.symm
    · rw [hv.2 n (by omega), c_recursion.2 n (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [ih d (Nat.mem_properDivisors.mp hd).2
        (Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd).1 hn)]


end
end D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
