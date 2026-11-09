/- GID: D5/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity
   generality: G
   mirror-B: D5/B/S3/Arith/DirichletInverse/OeisA322026DirichletInverseIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: Sequence Machine's A322026 identity is forced by 5-insensitivity and Dirichlet inversion. -/

/-
proof_shape: content (result; the 5-insensitive inverse-support argument is consumed); bind-only (a, b and local arithmetic helpers; consumers: result).
escape_witness: result uses the non-normalization inverse-prime-square-support argument on its live path.
admission_basis: open-problem-resolution (#26072; Proved).
Registration audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26181; no declared_validated claim.
Direct frozen dependencies after inlining local helpers: Mathlib arithmetic-function Dirichlet inversion and natural-number divisor/factorization APIs.
Utility: none; this is an unbounded symbolic resolution of the preregistered A322026 identity.
Declaration classification (names relative to this module):
declaration | proof_shape | escape_witness | direct consumers
a | bind-only | none | result
a_one | bind-only | none | inverse_prime_square_support, result
a_mul_five | content | none | result
inverse_prime_square_support | content | result | result
result | content | result | none
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped BigOperators
open ArithmeticFunction

namespace D5.S3.Arith.DirichletInverse.OeisA322026DirichletInverseIdentity

private def latticeCount (c : ℕ) : ℤ :=
  ((Finset.filter (fun ij : ℕ × ℕ => 2 ^ ij.1 * 3 ^ ij.2 ≤ c)
    (Finset.Icc 0 c ×ˢ Finset.Icc 0 c)).card : ℤ)

private def aValue (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    latticeCount (2 ^ n.factorization 2 * 3 ^ n.factorization 3)

def a : ArithmeticFunction ℤ :=
  { toFun := aValue
    map_zero' := by simp [aValue] }

/-- The formula has unit head. -/
private lemma a_one : a 1 = 1 := by
  change aValue 1 = 1
  norm_num [aValue, latticeCount]
  have hfilter :
      {x ∈ Finset.Icc 0 1 ×ˢ Finset.Icc 0 1 |
          2 ^ x.1 * 3 ^ x.2 ≤ 1} = {(0, 0)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hineq⟩
      have hxone : x.1 = 0 := by
        by_contra hne
        have hpos : 1 ≤ x.1 := by omega
        have hpow : 2 ≤ 2 ^ x.1 := by
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ x.1 := Nat.pow_le_pow_right (by decide) hpos
        have hprod : 2 ≤ 2 ^ x.1 * 3 ^ x.2 := by
          calc
            2 = 2 * 1 := by norm_num
            _ ≤ 2 ^ x.1 * 3 ^ x.2 :=
              Nat.mul_le_mul hpow (Nat.one_le_pow _ _ (by decide))
        omega
      have hyzero : x.2 = 0 := by
        by_contra hne
        have hpos : 1 ≤ x.2 := by omega
        have hpow : 3 ≤ 3 ^ x.2 := by
          calc
            3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ x.2 := Nat.pow_le_pow_right (by decide) hpos
        have hprod : 3 ≤ 2 ^ x.1 * 3 ^ x.2 := by
          calc
            3 = 1 * 3 := by norm_num
            _ ≤ 2 ^ x.1 * 3 ^ x.2 :=
              Nat.mul_le_mul (Nat.one_le_pow _ _ (by decide)) hpow
        omega
      exact Prod.ext hxone hyzero
    · rintro rfl
      norm_num
  rw [hfilter]
  simp

private lemma factorization_five_two : (5 : ℕ).factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  norm_num

private lemma factorization_five_three : (5 : ℕ).factorization 3 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  norm_num

private lemma a_mul_five (n : ℕ) : a (5 * n) = a n := by
  by_cases hn : n = 0
  · subst n
    simp [a, aValue]
  have hn0 : n ≠ 0 := hn
  have hfac2 : (5 * n).factorization 2 = n.factorization 2 := by
    rw [Nat.factorization_mul (by norm_num) hn0]
    simp [factorization_five_two]
  have hfac3 : (5 * n).factorization 3 = n.factorization 3 := by
    rw [Nat.factorization_mul (by norm_num) hn0]
    simp [factorization_five_three]
  change aValue (5 * n) = aValue n
  simp only [aValue, if_neg (by positivity : 5 * n ≠ 0), if_neg hn]
  rw [hfac2, hfac3]



private noncomputable def delta (p : ℕ) (hp : p ≠ 0) : ArithmeticFunction ℤ :=
  { toFun := fun n => if n = p then 1 else 0
    map_zero' := by simp [Ne.symm hp] }

private lemma delta_mul_apply (f : ArithmeticFunction ℤ) (p n : ℕ) (hp : p.Prime) :
    (delta p hp.ne_zero * f) n = if p ∣ n then f (n / p) else 0 := by
  classical
  rw [mul_apply]
  change (∑ x ∈ n.divisorsAntidiagonal, (delta p hp.ne_zero) x.1 * f x.2) = _
  rw [Nat.sum_divisorsAntidiagonal (fun x y => (delta p hp.ne_zero) x * f y)]
  change (∑ b ∈ n.divisors, (delta p hp.ne_zero) b * f (n / b)) = _
  by_cases hn0 : n = 0
  · subst n
    simp [delta]
  by_cases h : p ∣ n
  · rw [if_pos h]
    have hn : p ∈ n.divisors := Nat.mem_divisors.mpr ⟨h, hn0⟩
    refine (Finset.sum_eq_single (s := n.divisors)
      (f := fun b => (delta p hp.ne_zero) b * f (n / b)) p ?_ ?_).trans ?_
    · intro b hb hbn
      simp [delta]
      intro heq
      subst b
      exact (hbn rfl).elim
    · intro hnmem
      exact (hnmem hn).elim
    · simp [delta]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    simp [delta]
    intro heq
    subst b
    exact (h (Nat.mem_divisors.mp hb).1).elim

private noncomputable def killed (f : ArithmeticFunction ℤ) (p : ℕ) (hp : p.Prime) : ArithmeticFunction ℤ :=
  f - delta p hp.ne_zero * f

private lemma killed_apply_of_dvd {f : ArithmeticFunction ℤ} {p n : ℕ} (hp : p.Prime)
    (hper : ∀ n, f (p * n) = f n) (hn : p ∣ n) :
    killed f p hp n = 0 := by
  change f n - (delta p hp.ne_zero * f) n = 0
  rw [delta_mul_apply f p n hp, if_pos hn]
  rw [← hper (n / p), Nat.mul_div_cancel' hn]
  ring

private lemma killed_apply_one {f : ArithmeticFunction ℤ} {p : ℕ} (hp : p.Prime)
    (h1 : f 1 = 1) : killed f p hp 1 = 1 := by
  change f 1 - (delta p hp.ne_zero * f) 1 = 1
  rw [delta_mul_apply f p 1 hp]
  simp [h1, hp.not_dvd_one]

private lemma inverse_prime_square_support {f : ArithmeticFunction ℤ} {p : ℕ} (hp : p.Prime)
    (h1 : f 1 = 1) (hper : ∀ n, f (p * n) = f n)
    (hf : Invertible (f 1)) :
    ∀ {m : ℕ}, p ^ 2 ∣ m → ArithmeticFunction.dirichletInverse f hf m = 0 := by
  let g : ArithmeticFunction ℤ := ArithmeticFunction.dirichletInverse f hf
  let h : ArithmeticFunction ℤ := killed f p hp
  have hconv : h * g = 1 - delta p hp.ne_zero := by
    change (f - delta p hp.ne_zero * f) * ArithmeticFunction.dirichletInverse f hf =
      1 - delta p hp.ne_zero
    rw [sub_mul, mul_assoc, ArithmeticFunction.self_mul_dirichletInverse f hf]
    simp
  have hzero : ∀ {d : ℕ}, p ∣ d → h d = 0 := by
    intro d hd
    exact killed_apply_of_dvd hp hper hd
  have hone : h 1 = 1 := killed_apply_one hp h1
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hm0 : m = 0
    · subst m
      simp [g]
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have heval := congrArg (fun q : ArithmeticFunction ℤ => q m) hconv
    rw [mul_apply] at heval
    have hrewrite :
        (∑ x ∈ m.divisorsAntidiagonal, h x.1 * g x.2) =
          ∑ d ∈ m.divisors, h (m / d) * g d :=
      Nat.sum_divisorsAntidiagonal' (fun x y => h x * g y)
    rw [hrewrite] at heval
    have hm1 : m ≠ 1 := by
      intro hm1
      subst m
      have hle : p ^ 2 ≤ 1 := Nat.le_of_dvd (by decide) hm
      have hp2le : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
      omega
    have hmp : m ≠ p := by
      intro hmp
      subst m
      have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hm
      nlinarith [hp.two_le]
    have hright : (1 - delta p hp.ne_zero) m = 0 := by
      change ((1 : ArithmeticFunction ℤ) m - (delta p hp.ne_zero) m) = 0
      simp only [ArithmeticFunction.one_apply, delta]
      simp [hm1, hmp]
    rw [hright] at heval
    have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm0⟩
    have hsum := Finset.sum_eq_single (s := m.divisors)
      (f := fun d => h (m / d) * g d) m (by
        intro d hd hdm
        by_cases hpd : p ∣ m / d
        · rw [hzero hpd, zero_mul]
        · have hcop : (m / d).Coprime (p ^ 2) := hp.coprime_pow_of_not_dvd hpd
          have hfactor : p ^ 2 ∣ d * (m / d) := by
            rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
            exact hm
          have hpdvd : p ^ 2 ∣ d := hcop.symm.dvd_of_dvd_mul_right hfactor
          have hdlt : d < m := by
            have hle : d ≤ m := Nat.le_of_dvd hmpos (Nat.mem_divisors.mp hd).1
            omega
          rw [ih d hdlt hpdvd]
          simp)
      (by intro hmnot; exact (hmnot hm_mem).elim)
    rw [hsum] at heval
    rw [Nat.div_self hmpos, hone, one_mul] at heval
    change g m = 0
    exact heval

private noncomputable def aInv : Invertible (a 1) := by
  exact a_one ▸ invertibleOne

noncomputable def b : ArithmeticFunction ℤ := ArithmeticFunction.dirichletInverse a aInv

/-- The whole A322026 identity: the inverse correction vanishes after multiplying by 25. -/
theorem result : ∀ n : ℕ, a n = a (25 * n) + b (25 * n) := by
  intro n
  have hper := a_mul_five
  have hb : b (25 * n) = 0 := by
    change ArithmeticFunction.dirichletInverse a aInv (25 * n) = 0
    apply inverse_prime_square_support (f := a) (p := 5) (by decide : Nat.Prime 5) a_one hper aInv
    simpa [pow_two] using (dvd_mul_right 25 n)
  have ha : a (25 * n) = a n := by
    calc
      a (25 * n) = a (5 * (5 * n)) := by congr 1 <;> ring
      _ = a (5 * n) := a_mul_five (5 * n)
      _ = a n := a_mul_five n
  rw [ha, hb]
  ring

end D5.S3.Arith.DirichletInverse.OeisA322026DirichletInverseIdentity
