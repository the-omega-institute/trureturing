/- GID: D5/S3/Factorization/QuadraticIdeals/CubicIdealCharacter
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicIdealCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic characters at Eisenstein prime ideals and factored denominators. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient

namespace D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter

noncomputable def localCubicSymbol (P : Ideal EisensteinOrder) (a : EisensteinOrder) :
    EisensteinOrder := by
  classical
  let q := Ideal.Quotient.mk P
  let t := q a ^ ((Nat.card (EisensteinOrder ⧸ P) - 1) / 3)
  exact if t = 1 then 1 else
    if t = q QuadraticAlgebra.omega then QuadraticAlgebra.omega
    else QuadraticAlgebra.omega ^ 2

noncomputable def factoredCubicSymbol {ι : Type*} (s : Finset ι)
    (P : ι → Ideal EisensteinOrder) (e : ι → ℕ) (a : EisensteinOrder) :
    EisensteinOrder :=
  ∏ i ∈ s, localCubicSymbol (P i) a ^ e i

/-- The local Euler criterion uniquely selects an Eisenstein cube root of unity.
The resulting character multiplies over numerators and over a specified
prime-ideal factorization of a composite denominator. -/
theorem cubic_ideal_character_and_factored_multiplicativity
    {ι : Type*} (s : Finset ι) (P : ι → Ideal EisensteinOrder)
    (hmax : ∀ i ∈ s, (P i).IsMaximal)
    (hfinite : ∀ i ∈ s, Finite (EisensteinOrder ⧸ P i))
    (hcard : ∀ i ∈ s, Nat.card (EisensteinOrder ⧸ P i) % 3 = 1)
    (hthree : ∀ i ∈ s, (3 : EisensteinOrder) ∉ P i) :
    (∀ i ∈ s, ∀ a : EisensteinOrder, a ∉ P i →
      (localCubicSymbol (P i) a = 1 ∨
        localCubicSymbol (P i) a = QuadraticAlgebra.omega ∨
        localCubicSymbol (P i) a = QuadraticAlgebra.omega ^ 2) ∧
      Ideal.Quotient.mk (P i) (localCubicSymbol (P i) a) =
        (Ideal.Quotient.mk (P i) a) ^
          ((Nat.card (EisensteinOrder ⧸ P i) - 1) / 3) ∧
      (∀ z : EisensteinOrder,
        (z = 1 ∨ z = QuadraticAlgebra.omega ∨ z = QuadraticAlgebra.omega ^ 2) →
        Ideal.Quotient.mk (P i) z =
          (Ideal.Quotient.mk (P i) a) ^
            ((Nat.card (EisensteinOrder ⧸ P i) - 1) / 3) →
        z = localCubicSymbol (P i) a)) ∧
    (∀ i ∈ s, ∀ a b : EisensteinOrder, a ∉ P i → b ∉ P i →
      localCubicSymbol (P i) (a * b) =
        localCubicSymbol (P i) a * localCubicSymbol (P i) b) ∧
    (∀ (e : ι → ℕ) (a b : EisensteinOrder),
      (∀ i ∈ s, a ∉ P i ∧ b ∉ P i) →
      factoredCubicSymbol s P e (a * b) =
        factoredCubicSymbol s P e a * factoredCubicSymbol s P e b) ∧
    (∀ (e f : ι → ℕ) (a : EisensteinOrder),
      (∀ i ∈ s, a ∉ P i) →
      factoredCubicSymbol s P (fun i => e i + f i) a =
        factoredCubicSymbol s P e a * factoredCubicSymbol s P f a) := by
  classical
  let w : EisensteinOrder := QuadraticAlgebra.omega
  have hw : w ^ 2 + w + 1 = 0 := by
    change (QuadraticAlgebra.omega : EisensteinOrder) ^ 2 +
      QuadraticAlgebra.omega + 1 = 0
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp
  have hw3 : w ^ 3 = 1 := by
    linear_combination (w - 1) * hw
  have hthree_factor : (1 - w) * (1 - w ^ 2) = (3 : EisensteinOrder) := by
    calc
      (1 - w) * (1 - w ^ 2) = 1 - w - w ^ 2 + w ^ 3 := by ring
      _ = 2 - w - w ^ 2 := by rw [hw3]; ring
      _ = 3 := by linear_combination -hw
  have hlocal (i : ι) (hi : i ∈ s) (a : EisensteinOrder) (ha : a ∉ P i) :
      (localCubicSymbol (P i) a = 1 ∨
        localCubicSymbol (P i) a = w ∨
        localCubicSymbol (P i) a = w ^ 2) ∧
      Ideal.Quotient.mk (P i) (localCubicSymbol (P i) a) =
        (Ideal.Quotient.mk (P i) a) ^
          ((Nat.card (EisensteinOrder ⧸ P i) - 1) / 3) ∧
      (∀ z : EisensteinOrder, (z = 1 ∨ z = w ∨ z = w ^ 2) →
        Ideal.Quotient.mk (P i) z =
          (Ideal.Quotient.mk (P i) a) ^
            ((Nat.card (EisensteinOrder ⧸ P i) - 1) / 3) →
        z = localCubicSymbol (P i) a) := by
    letI : (P i).IsMaximal := hmax i hi
    letI : Field (EisensteinOrder ⧸ P i) := Ideal.Quotient.field (P i)
    letI : Finite (EisensteinOrder ⧸ P i) := hfinite i hi
    letI : Fintype (EisensteinOrder ⧸ P i) := Fintype.ofFinite _
    let q := Ideal.Quotient.mk (P i)
    let m := (Nat.card (EisensteinOrder ⧸ P i) - 1) / 3
    let t := q a ^ m
    have ha0 : q a ≠ 0 := by
      intro hz
      exact ha (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hm : m * 3 = Nat.card (EisensteinOrder ⧸ P i) - 1 := by
      dsimp [m]
      have := hcard i hi
      omega
    have ht3 : t ^ 3 = 1 := by
      calc
        t ^ 3 = (q a) ^ (m * 3) := by simp only [t, pow_mul]
        _ = (q a) ^ (Nat.card (EisensteinOrder ⧸ P i) - 1) := by rw [hm]
        _ = 1 := by
          simpa only [Nat.card_eq_fintype_card] using
            (FiniteField.pow_card_sub_one_eq_one (q a) ha0)
    have hqw : (q w) ^ 2 + q w + 1 = 0 := by
      have h := congrArg q hw
      simpa only [map_add, map_pow, map_one, map_zero] using h
    have hqw3 : (q w) ^ 3 = 1 := by
      rw [← map_pow, hw3, map_one]
    have hqw1 : q w ≠ 1 := by
      intro h
      have hqdiff : q (1 - w) = 0 := by
        rw [map_sub, map_one, h, sub_self]
      have hqthree : q (3 : EisensteinOrder) = 0 := by
        rw [← hthree_factor, map_mul, hqdiff, zero_mul]
      exact hthree i hi (Ideal.Quotient.eq_zero_iff_mem.mp hqthree)
    have hqw2 : (q w) ^ 2 ≠ 1 := by
      intro h
      have h' : q w = 1 := by
        calc
          q w = (q w) ^ 2 * q w := by rw [h]; ring
          _ = (q w) ^ 3 := by ring
          _ = 1 := hqw3
      exact hqw1 h'
    have hqw12 : q w ≠ (q w) ^ 2 := by
      intro h
      have h' : (q w) ^ 3 = q w := by
        calc
          (q w) ^ 3 = (q w) ^ 2 * q w := by ring
          _ = q w * q w := congrArg (· * q w) h.symm
          _ = (q w) ^ 2 := by ring
          _ = q w := h.symm
      exact hqw1 (h'.symm.trans hqw3)
    have hquadratic (u : EisensteinOrder ⧸ P i) :
        (u - 1) * (u - q w) * (u - q (w ^ 2)) = u ^ 3 - 1 := by
      have hqw2eq : (q w) ^ 2 = -q w - 1 := by linear_combination hqw
      have hprod : (u - q w) * (u - q (w ^ 2)) = u ^ 2 + u + 1 := by
        rw [map_pow, hqw2eq]
        calc
          (u - q w) * (u - (-q w - 1)) =
              u ^ 2 + u - ((q w) ^ 2 + q w) := by ring
          _ = u ^ 2 + u + 1 := by linear_combination -hqw
      rw [mul_assoc, hprod]
      ring
    have hroot : t = 1 ∨ t = q w ∨ t = q (w ^ 2) := by
      have hzero : (t - 1) * (t - q w) * (t - q (w ^ 2)) = 0 := by
        rw [hquadratic, ht3, sub_self]
      rcases mul_eq_zero.mp hzero with hleft | hright
      · rcases mul_eq_zero.mp hleft with hfirst | hsecond
        · exact Or.inl (sub_eq_zero.mp hfirst)
        · exact Or.inr (Or.inl (sub_eq_zero.mp hsecond))
      · exact Or.inr (Or.inr (sub_eq_zero.mp hright))
    have hvalue : localCubicSymbol (P i) a = 1 ∨
        localCubicSymbol (P i) a = w ∨ localCubicSymbol (P i) a = w ^ 2 := by
      dsimp [localCubicSymbol]
      split_ifs <;> simp [w]
    have himage : q (localCubicSymbol (P i) a) = t := by
      dsimp [localCubicSymbol]
      split_ifs with hfirst hsecond
      · exact hfirst.symm
      · exact hsecond.symm
      · rcases hroot with hroot | hroot | hroot
        · exact (hfirst hroot).elim
        · exact (hsecond hroot).elim
        · exact hroot.symm
    have hinjective {z z' : EisensteinOrder}
        (hz : z = 1 ∨ z = w ∨ z = w ^ 2)
        (hz' : z' = 1 ∨ z' = w ∨ z' = w ^ 2)
        (heq : q z = q z') : z = z' := by
      rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
      · rfl
      · exact (hqw1 (by simpa only [map_one] using heq.symm)).elim
      · exact (hqw2 (by simpa only [map_one, map_pow] using heq.symm)).elim
      · exact (hqw1 (by simpa only [map_one] using heq)).elim
      · rfl
      · exact (hqw12 (by simpa only [map_pow] using heq)).elim
      · exact (hqw2 (by simpa only [map_one, map_pow] using heq)).elim
      · exact (hqw12 (by simpa only [map_pow] using heq.symm)).elim
      · rfl
    refine ⟨hvalue, ?_, ?_⟩
    · exact himage
    · intro z hz hzq
      exact hinjective hz hvalue (hzq.trans himage.symm)
  have hmul (i : ι) (hi : i ∈ s) (a b : EisensteinOrder)
      (ha : a ∉ P i) (hb : b ∉ P i) :
      localCubicSymbol (P i) (a * b) =
        localCubicSymbol (P i) a * localCubicSymbol (P i) b := by
    have hab : a * b ∉ P i := by
      intro h
      rcases (hmax i hi).isPrime.mem_or_mem h with h | h
      · exact ha h
      · exact hb h
    obtain ⟨hval, himage, hunique⟩ := hlocal i hi (a * b) hab
    obtain ⟨hvala, himagea, _⟩ := hlocal i hi a ha
    obtain ⟨hvalb, himageb, _⟩ := hlocal i hi b hb
    have hvalprod : localCubicSymbol (P i) a * localCubicSymbol (P i) b = 1 ∨
        localCubicSymbol (P i) a * localCubicSymbol (P i) b = w ∨
        localCubicSymbol (P i) a * localCubicSymbol (P i) b = w ^ 2 := by
      rcases hvala with h | h | h <;> rcases hvalb with h' | h' | h'
      · left; rw [h, h']; ring
      · right; left; rw [h, h']; ring
      · right; right; rw [h, h']; ring
      · right; left; rw [h, h']; ring
      · right; right; rw [h, h']; ring
      · left; rw [h, h']; calc
          w * w ^ 2 = w ^ 3 := by ring
          _ = 1 := hw3
      · right; right; rw [h, h']; ring
      · left; rw [h, h']; calc
          w ^ 2 * w = w ^ 3 := by ring
          _ = 1 := hw3
      · right; left; rw [h, h']; calc
          w ^ 2 * w ^ 2 = w ^ 3 * w := by ring
          _ = w := by rw [hw3]; ring
    have hqprod : Ideal.Quotient.mk (P i)
        (localCubicSymbol (P i) a * localCubicSymbol (P i) b) =
        (Ideal.Quotient.mk (P i) (a * b)) ^
          ((Nat.card (EisensteinOrder ⧸ P i) - 1) / 3) := by
      rw [map_mul, himagea, himageb, map_mul, mul_pow]
    exact (hunique _ hvalprod hqprod).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi a ha
    simpa only [w] using hlocal i hi a ha
  · exact hmul
  · intro e a b hab
    simp only [factoredCubicSymbol]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hmul i hi a b (hab i hi).1 (hab i hi).2, mul_pow]
  · intro e f a ha
    simp only [factoredCubicSymbol]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact pow_add _ _ _

#print axioms cubic_ideal_character_and_factored_multiplicativity

end D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter
