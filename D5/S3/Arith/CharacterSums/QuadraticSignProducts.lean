/- GID: D5/S3/Arith/CharacterSums/QuadraticSignProducts
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/QuadraticSignProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sum of a finite sign family modulo four is determined by its product. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace D5.S3.Arith.CharacterSums.QuadraticSignProducts

open scoped BigOperators

/-- This integral form of the sign-product parity rule avoids assigning a natural
exponent to a possibly negative half sum. Repeated signs may be indexed separately. -/
theorem sign_sum_mod_four {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℤ)
    (hsq : ∀ i ∈ s, a i ^ 2 = 1) :
    Int.ModEq 4 (∑ i ∈ s, a i) ((s.card : ℤ) - 1 + ∏ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ha := sq_eq_one_iff.mp (hsq i (Finset.mem_insert_self i s))
    have hs : ∀ j ∈ s, a j ^ 2 = 1 := fun j hj =>
      hsq j (Finset.mem_insert_of_mem hj)
    have hp : (∏ j ∈ s, a j) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      calc
        _ = ∏ _j ∈ s, (1 : ℤ) := Finset.prod_congr rfl hs
        _ = 1 := by simp
    have h := ih hs
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Finset.prod_insert hi]
    change (a i + ∑ j ∈ s, a j) % 4 =
      ((s.card : ℤ) + 1 - 1 + a i * ∏ j ∈ s, a j) % 4
    change (∑ j ∈ s, a j) % 4 = ((s.card : ℤ) - 1 + ∏ j ∈ s, a j) % 4 at h
    rcases ha with ha | ha <;> rcases sq_eq_one_iff.mp hp with hp | hp <;>
      simp only [ha, hp] at h ⊢ <;> omega

/-- The odd factors below twice the endpoint. -/
def oddProduct (r : ℕ) : ℕ := ∏ k ∈ Finset.range r, (2 * k + 1)

theorem oddProduct_succ (r : ℕ) :
    oddProduct (r + 1) = oddProduct r * (2 * r + 1) :=
  Finset.prod_range_succ _ _

/-- Separating the even and odd factors of a factorial, with no quotient in N. -/
theorem factorial_even_split (r : ℕ) :
    (2 * r).factorial = 2 ^ r * r.factorial * oddProduct r := by
  induction r with
  | zero => simp [oddProduct]
  | succ r ih =>
    have h : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
    rw [h, Nat.factorial_succ, Nat.factorial_succ, ih,
      Nat.factorial_succ, pow_succ, oddProduct_succ]
    ring

/-- Pairing an odd lower-half index j with 2m+1-j gives this integer product. -/
def oddPairProduct (m : ℕ) : ℕ :=
  ∏ k ∈ Finset.range ((m + 1) / 2), (2 * k + 1) * (2 * (m - k))

theorem oddPairProduct_eq (m : ℕ) :
    oddPairProduct m = oddProduct ((m + 1) / 2) * 2 ^ ((m + 1) / 2) *
      m.descFactorial ((m + 1) / 2) := by
  simp only [oddPairProduct, oddProduct, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, Nat.descFactorial_eq_prod_range]
  ring

/-- The even m factorial-product identity used in the odd-prime-family parity proof.
Multiplying through by the square denominator keeps the statement integral. -/
theorem oddPairProduct_even (r : ℕ) :
    oddPairProduct (2 * r) * r.factorial ^ 2 = (2 * r).factorial ^ 2 := by
  have hr : (2 * r + 1) / 2 = r := by omega
  have hf : r.factorial * (2 * r).descFactorial r = (2 * r).factorial := by
    simpa only [show 2 * r - r = r by omega] using
      Nat.factorial_mul_descFactorial (show r ≤ 2 * r by omega)
  rw [oddPairProduct_eq, hr]
  calc
    _ = (2 ^ r * r.factorial * oddProduct r) *
        (r.factorial * (2 * r).descFactorial r) := by ring
    _ = _ := by rw [← factorial_even_split, hf]; ring

/-- For odd m the corresponding product is twice a square; the supplement at two
will show that this extra factor has quadratic character one. -/
theorem oddPairProduct_odd (r : ℕ) :
    oddPairProduct (2 * r + 1) * r.factorial ^ 2 =
      2 * (2 * r + 1).factorial ^ 2 := by
  have hr : (2 * r + 1 + 1) / 2 = r + 1 := by omega
  have hf : r.factorial * (2 * r + 1).descFactorial (r + 1) =
      (2 * r + 1).factorial := by
    simpa only [show 2 * r + 1 - (r + 1) = r by omega] using
      Nat.factorial_mul_descFactorial (show r + 1 ≤ 2 * r + 1 by omega)
  have ho : oddProduct (r + 1) * 2 ^ (r + 1) * r.factorial =
      2 * (2 * r + 1).factorial := by
    rw [oddProduct_succ, pow_succ, Nat.factorial_succ, factorial_even_split]
    ring
  rw [oddPairProduct_eq, hr]
  calc
    _ = (oddProduct (r + 1) * 2 ^ (r + 1) * r.factorial) *
        (r.factorial * (2 * r + 1).descFactorial (r + 1)) := by ring
    _ = _ := by rw [ho, hf]; ring

/-- The denominator factorials in the product identities are genuinely nonzero
modulo p. This discharges the cancellation rather than treating a quotient formally. -/
theorem factorial_character_square (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : r < p) :
    legendreSym p ((r.factorial : ℤ) ^ 2) = 1 := by
  apply legendreSym.sq_one'
  simp only [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
  exact fun h => (not_le_of_gt hr) ((Fact.out : p.Prime).dvd_factorial.mp h)

/-- The common factorial product has character one or character two according to
the parity of m. This lemma applies to both prime families in Chen-Sun. -/
theorem oddPairProduct_character (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m < p) :
    legendreSym p (oddPairProduct m : ℤ) = legendreSym p 2 ^ (m % 2) := by
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨r, hr⟩ := he
    have hmr : m = 2 * r := by omega
    have hid : (oddPairProduct (2 * r) : ℤ) * (r.factorial : ℤ) ^ 2 =
        ((2 * r).factorial : ℤ) ^ 2 := by
      exact_mod_cast oddPairProduct_even r
    have h := congrArg (legendreSym p) hid
    simp only [legendreSym.mul,
      factorial_character_square p r (by omega),
      factorial_character_square p (2 * r) (by omega), mul_one] at h
    rw [hmr, show (2 * r) % 2 = 0 by omega, pow_zero]
    exact h
  · obtain ⟨r, hr⟩ := ho
    have hmr : m = 2 * r + 1 := by omega
    have hid : (oddPairProduct (2 * r + 1) : ℤ) * (r.factorial : ℤ) ^ 2 =
        2 * ((2 * r + 1).factorial : ℤ) ^ 2 := by
      exact_mod_cast oddPairProduct_odd r
    have h := congrArg (legendreSym p) hid
    simp only [legendreSym.mul,
      factorial_character_square p r (by omega),
      factorial_character_square p (2 * r + 1) (by omega), mul_one] at h
    rw [hmr, show (2 * r + 1) % 2 = 1 by omega, pow_one]
    exact h

/-- A central interval of even length, before evaluating the sign family. -/
def intervalProduct (a : ℕ → ℤ) (m i : ℕ) : ℤ :=
  ∏ k ∈ Finset.range (2 * (m - i)), a (i + k + 1)

/-- Reflection of the upper half pairs j with 2m+1-j. -/
theorem intervalProduct_pair (a : ℕ → ℤ) (m i : ℕ) (hi : i ≤ m) :
    intervalProduct a m i =
      ∏ k ∈ Finset.range (m - i),
        (a (i + k + 1) * a (2 * m + 1 - (i + k + 1))) := by
  have hu : (∏ k ∈ Finset.range (m - i), a (i + (m - i + k) + 1)) =
      ∏ k ∈ Finset.range (m - i), a (2 * m + 1 - (i + k + 1)) := by
    rw [← Finset.prod_range_reflect (fun k => a (i + (m - i + k) + 1)) (m - i)]
    apply Finset.prod_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    congr 1
    omega
  rw [intervalProduct, show 2 * (m - i) = (m - i) + (m - i) by omega,
    Finset.prod_range_add, hu, Finset.prod_mul_distrib]

/-- The actual nested interval product is a weighted triangular product. The finite
diagonal-flip supplier accounts for the multiplicities, rather than assuming them. -/
theorem intervalProduct_triangle (a : ℕ → ℤ) (m : ℕ) :
    (∏ i ∈ Finset.range m, intervalProduct a m i) =
      ∏ j ∈ Finset.range m, (a (j + 1) * a (2 * m - j)) ^ (j + 1) := by
  let f : ℕ → ℤ := fun j => a j * a (2 * m + 1 - j)
  calc
    _ = ∏ i ∈ Finset.range m, ∏ k ∈ Finset.range (m - i), f (i + k + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact intervalProduct_pair a m i (by have := Finset.mem_range.mp hi; omega)
    _ = ∏ j ∈ Finset.range m, ∏ i ∈ Finset.range (j + 1), f (i + (j - i) + 1) :=
      (Finset.prod_range_diag_flip m (fun i k => f (i + k + 1))).symm
    _ = ∏ j ∈ Finset.range m, f (j + 1) ^ (j + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      calc
        _ = ∏ _i ∈ Finset.range (j + 1), f (j + 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hi' := Finset.mem_range.mp hi
          congr 1
          omega
        _ = _ := by simp
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have harg : 2 * m + 1 - (j + 1) = 2 * m - j := by omega
      simp only [f, harg]

/-- Square-one factors at even weights disappear from the triangular product. -/
theorem weighted_sign_product_even (f : ℕ → ℤ) (r : ℕ)
    (hsq : ∀ j, 1 ≤ j → j ≤ 2 * r → f j ^ 2 = 1) :
    (∏ j ∈ Finset.range (2 * r), f (j + 1) ^ (j + 1)) =
      ∏ k ∈ Finset.range r, f (2 * k + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp := ih (fun j hj hn => hsq j hj (by omega))
    have ho : f (2 * r + 1) ^ (2 * r + 1) = f (2 * r + 1) := by
      rw [pow_add, pow_mul, hsq _ (by omega) (by omega)]
      simp
    have he : f (2 * r + 1 + 1) ^ (2 * r + 1 + 1) = 1 := by
      rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul,
        hsq _ (by omega) (by omega), one_pow]
    rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega,
      Finset.prod_range_succ, Finset.prod_range_succ, hp, ho, he, mul_one,
      Finset.prod_range_succ]

/-- The unpaired last odd weight contributes its sign. -/
theorem weighted_sign_product_odd (f : ℕ → ℤ) (r : ℕ)
    (hsq : ∀ j, 1 ≤ j → j ≤ 2 * r + 1 → f j ^ 2 = 1) :
    (∏ j ∈ Finset.range (2 * r + 1), f (j + 1) ^ (j + 1)) =
      ∏ k ∈ Finset.range (r + 1), f (2 * k + 1) := by
  have ho : f (2 * r + 1) ^ (2 * r + 1) = f (2 * r + 1) := by
    rw [pow_add, pow_mul, hsq _ (by omega) (by omega)]
    simp
  rw [Finset.prod_range_succ,
    weighted_sign_product_even f r (fun j hj hn => hsq j hj (by omega)),
    ho, Finset.prod_range_succ]

/-- The full nested product of the genuine Legendre signs is evaluated by the
factorial identities above. The bound ensures every paired factor is nonzero. -/
theorem intervalProduct_character (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 2 * m < p) :
    (∏ i ∈ Finset.range m,
      intervalProduct (fun j => legendreSym p (j : ℤ)) m i) =
        legendreSym p 2 ^ (m % 2) := by
  let a : ℕ → ℤ := fun j => legendreSym p (j : ℤ)
  let f : ℕ → ℤ := fun j => a j * a (2 * m + 1 - j)
  have ha (j : ℕ) (hj : 1 ≤ j) (hjp : j < p) : a j ^ 2 = 1 := by
    apply legendreSym.sq_one
    push_cast
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_cast_of_lt hjp, ZMod.val_zero] at hv
    omega
  have hf (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) : f j ^ 2 = 1 := by
    dsimp only [f]
    rw [mul_pow, ha j hj (by omega), ha _ (by omega) (by omega)]
    norm_num
  have hprod : legendreSym p (oddPairProduct m : ℤ) =
      ∏ k ∈ Finset.range ((m + 1) / 2), f (2 * k + 1) := by
    calc
      _ = (legendreSym.hom p)
          (∏ k ∈ Finset.range ((m + 1) / 2),
            (((2 * k + 1) * (2 * (m - k)) : ℕ) : ℤ)) := by
        rw [oddPairProduct, Nat.cast_prod]
        rfl
      _ = ∏ k ∈ Finset.range ((m + 1) / 2),
          legendreSym p ((((2 * k + 1) * (2 * (m - k)) : ℕ) : ℤ)) :=
        map_prod (legendreSym.hom p) _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have harg : 2 * m + 1 - (2 * k + 1) = 2 * (m - k) := by omega
        dsimp only [f, a]
        rw [harg, ← legendreSym.mul]
        congr 1
  have hw : (∏ j ∈ Finset.range m, f (j + 1) ^ (j + 1)) =
      ∏ k ∈ Finset.range ((m + 1) / 2), f (2 * k + 1) := by
    rcases Nat.even_or_odd m with he | ho
    · obtain ⟨r, hr⟩ := he
      have hmr : m = 2 * r := by omega
      have h := weighted_sign_product_even f r (fun j hj hn => hf j hj (by omega))
      simpa only [hmr, show (2 * r + 1) / 2 = r by omega] using h
    · obtain ⟨r, hr⟩ := ho
      have hmr : m = 2 * r + 1 := by omega
      have h := weighted_sign_product_odd f r (fun j hj hn => hf j hj (by omega))
      simpa only [hmr, show (2 * r + 1 + 1) / 2 = r + 1 by omega] using h
  rw [intervalProduct_triangle]
  calc
    _ = ∏ j ∈ Finset.range m, f (j + 1) ^ (j + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [f, a, Nat.add_sub_add_right]
    _ = legendreSym p (oddPairProduct m : ℤ) := hw.trans hprod.symm
    _ = _ := oddPairProduct_character p m (by omega)

end D5.S3.Arith.CharacterSums.QuadraticSignProducts
