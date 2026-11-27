import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Basic.Complex.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# An elementary fourth-moment bound for prime Kloosterman sums

The standard additive character over `ZMod p` gives an exact count of ordered
nonzero quadruples in the two-coefficient fourth moment. A nonzero pair sum
determines the product from the inverse sum, while a zero pair sum forces each
pair to consist of opposites. Scaling the two coefficients bounds a pointwise
fourth power by the joint moment divided by the number of units.
-/

noncomputable section

namespace D5.S3.CharacterSums.PrimeKloostermanFourthMoment

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

local notation "𝔽" => ZMod p
local notation "𝕌" => (ZMod p)ˣ
local notation "Pair" => ((ZMod p)ˣ × (ZMod p)ˣ)
local notation "χ" => (ZMod.stdAddChar (N := p))

/-- The unnormalized prime Kloosterman sum with both coefficients explicit. -/
def primeKloosterman (a b : 𝔽) : ℂ :=
  ∑ x : 𝕌, χ (a * (x : 𝔽) + b * (x : 𝔽)⁻¹)

private def pairSum (x : Pair) : 𝔽 :=
  (x.1 : 𝔽) + (x.2 : 𝔽)

private def pairInvSum (x : Pair) : 𝔽 :=
  (x.1 : 𝔽)⁻¹ + (x.2 : 𝔽)⁻¹

variable (p) in
/-- Ordered pairs of unit pairs having the same sum and the same inverse sum. -/
def fourthMomentSolutions : Finset (Pair × Pair) :=
  Finset.univ.filter fun q => pairSum q.1 = pairSum q.2 ∧ pairInvSum q.1 = pairInvSum q.2

private theorem sum_stdAddChar (d : 𝔽) :
    (∑ k : 𝔽, χ (k * d)) = if d = 0 then (p : ℂ) else 0 := by
  rw [AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  split <;> simp

private theorem stdAddChar_conj (d : 𝔽) : starRingEnd ℂ (χ d) = χ (-d) := by
  rw [AddChar.map_neg_eq_inv χ, ZMod.stdAddChar_apply, ← Circle.coe_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle d)).symm

private theorem sum_stdAddChar_two (d e : 𝔽) :
    (∑ c : 𝔽 × 𝔽, χ (c.1 * d + c.2 * e)) =
      if d = 0 ∧ e = 0 then (p : ℂ) ^ 2 else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_stdAddChar, sum_stdAddChar]
  by_cases hd : d = 0 <;> by_cases he : e = 0 <;> simp [hd, he, pow_two]

private theorem fourthPower_expand (a b : 𝔽) :
    ((‖primeKloosterman a b‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : Pair × Pair,
        χ (a * (pairSum q.1 - pairSum q.2) + b * (pairInvSum q.1 - pairInvSum q.2)) := by
  have hsq : primeKloosterman a b ^ 2 =
      ∑ x : Pair, χ (a * pairSum x + b * pairInvSum x) := by
    rw [pow_two, primeKloosterman, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold pairSum pairInvSum
    ring
  calc
    _ = (primeKloosterman a b ^ 2) * starRingEnd ℂ (primeKloosterman a b ^ 2) := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Complex.sq_norm, Complex.ofReal_pow,
        ← Complex.mul_conj, mul_pow, map_pow]
    _ = _ := by
      conv_rhs => rw [Fintype.sum_prod_type]
      rw [hsq, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [stdAddChar_conj, ← AddChar.map_add_eq_mul]
      congr 1
      ring

/-- Orthogonality in both coefficients gives the exact real fourth moment. -/
theorem fourthMoment_eq :
    (∑ a : 𝔽, ∑ b : 𝔽, ‖primeKloosterman a b‖ ^ 4) =
      (p : ℝ) ^ 2 * ((fourthMomentSolutions p).card : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_pow]
  simp only [Complex.ofReal_sum, Complex.ofReal_natCast]
  calc
    (∑ a : 𝔽, ∑ b : 𝔽, ((‖primeKloosterman a b‖ ^ 4 : ℝ) : ℂ)) =
        ∑ c : 𝔽 × 𝔽, ∑ q : Pair × Pair,
          χ (c.1 * (pairSum q.1 - pairSum q.2) + c.2 * (pairInvSum q.1 - pairInvSum q.2)) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => fourthPower_expand a b
    _ = ∑ q : Pair × Pair, ∑ c : 𝔽 × 𝔽,
          χ (c.1 * (pairSum q.1 - pairSum q.2) + c.2 * (pairInvSum q.1 - pairInvSum q.2)) :=
      Finset.sum_comm
    _ = ∑ q : Pair × Pair,
          if pairSum q.1 = pairSum q.2 ∧ pairInvSum q.1 = pairInvSum q.2
          then (p : ℂ) ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [sum_stdAddChar_two]
      simp only [sub_eq_zero]
    _ = (p : ℂ) ^ 2 * ((fourthMomentSolutions p).card : ℂ) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, fourthMomentSolutions, mul_comm]

private theorem pair_matches_or_swap {x y z w : 𝕌}
    (hs : (x : 𝔽) + (y : 𝔽) = (z : 𝔽) + (w : 𝔽))
    (hi : (x : 𝔽)⁻¹ + (y : 𝔽)⁻¹ = (z : 𝔽)⁻¹ + (w : 𝔽)⁻¹)
    (hzero : (x : 𝔽) + (y : 𝔽) ≠ 0) :
    (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
  have hinv :
      ((x : 𝔽) + (y : 𝔽)) * ((x : 𝔽) * (y : 𝔽))⁻¹ =
        ((x : 𝔽) + (y : 𝔽)) * ((z : 𝔽) * (w : 𝔽))⁻¹ := by
    simpa only [inv_add_inv x.ne_zero y.ne_zero, inv_add_inv z.ne_zero w.ne_zero, ← hs,
      div_eq_mul_inv] using hi
  have hprod : (x : 𝔽) * (y : 𝔽) = (z : 𝔽) * (w : 𝔽) :=
    inv_injective (mul_left_cancel₀ hzero hinv)
  have hroot : ((z : 𝔽) - (x : 𝔽)) * ((z : 𝔽) - (y : 𝔽)) = 0 := by
    calc
      _ = (z : 𝔽) ^ 2 - (z : 𝔽) * ((x : 𝔽) + (y : 𝔽)) + (x : 𝔽) * (y : 𝔽) := by ring
      _ = 0 := by rw [hs, hprod]; ring
  rcases mul_eq_zero.mp hroot with hz | hz
  · have hzx : (z : 𝔽) = (x : 𝔽) := sub_eq_zero.mp hz
    have hw : (x : 𝔽) + (w : 𝔽) = (x : 𝔽) + (y : 𝔽) := by
      simpa only [hzx] using hs.symm
    exact Or.inl ⟨Units.ext hzx, Units.ext (add_left_cancel hw)⟩
  · have hzy : (z : 𝔽) = (y : 𝔽) := sub_eq_zero.mp hz
    have hw : (y : 𝔽) + (w : 𝔽) = (y : 𝔽) + (x : 𝔽) := by
      rw [add_comm (y : 𝔽) (x : 𝔽)]
      simpa only [hzy] using hs.symm
    exact Or.inr ⟨Units.ext hzy, Units.ext (add_left_cancel hw)⟩

/-- The diagonal, swapped and zero-sum families each contribute at most `(p - 1)^2`
ordered quadruples. -/
theorem card_fourthMomentSolutions_le :
    (fourthMomentSolutions p).card ≤ 3 * (p - 1) ^ 2 := by
  classical
  let diagonal (x : Pair) : Pair × Pair := (x, x)
  let swapped (x : Pair) : Pair × Pair := (x, (x.2, x.1))
  let opposite (x : Pair) : Pair × Pair := ((x.1, -x.1), (x.2, -x.2))
  let D := Finset.univ.image diagonal
  let T := Finset.univ.image swapped
  let O := Finset.univ.image opposite
  have hcover : fourthMomentSolutions p ⊆ D ∪ T ∪ O := by
    rintro ⟨⟨x, y⟩, ⟨z, w⟩⟩ hq
    unfold fourthMomentSolutions at hq
    obtain ⟨_, hs, hi⟩ := Finset.mem_filter.mp hq
    change (x : 𝔽) + (y : 𝔽) = (z : 𝔽) + (w : 𝔽) at hs
    change (x : 𝔽)⁻¹ + (y : 𝔽)⁻¹ = (z : 𝔽)⁻¹ + (w : 𝔽)⁻¹ at hi
    by_cases hzero : (x : 𝔽) + (y : 𝔽) = 0
    · have hy : y = -x := Units.ext (by
        rw [Units.val_neg]
        exact eq_neg_of_add_eq_zero_right hzero)
      have hw : w = -z := Units.ext (by
        rw [Units.val_neg]
        exact eq_neg_of_add_eq_zero_right (hs.symm.trans hzero))
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨(x, z), Finset.mem_univ _,
        by simp only [opposite, hy, hw]⟩)
    · rcases pair_matches_or_swap hs hi hzero with ⟨hz, hw⟩ | ⟨hz, hw⟩
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_union.mpr (Or.inl
          (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, by simp only [diagonal, hz, hw]⟩)))
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, by simp only [swapped, hz, hw]⟩)))
  have image_card_le (f : Pair → Pair × Pair) :
      (Finset.univ.image f).card ≤ (p - 1) ^ 2 := by
    calc
      _ ≤ (Finset.univ : Finset Pair).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_univ, Fintype.card_prod, ZMod.card_units, pow_two]
  calc
    _ ≤ (D ∪ T ∪ O).card := Finset.card_le_card hcover
    _ ≤ (D.card + T.card) + O.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ ((p - 1) ^ 2 + (p - 1) ^ 2) + (p - 1) ^ 2 :=
      Nat.add_le_add (Nat.add_le_add (image_card_le diagonal) (image_card_le swapped))
        (image_card_le opposite)
    _ = _ := by ring

/-- Multiplying the summation variable by a unit scales the two coefficients inversely. -/
theorem primeKloosterman_scale (a b : 𝔽) (t : 𝕌) :
    primeKloosterman (a * (t : 𝔽)) (b / (t : 𝔽)) = primeKloosterman a b := by
  unfold primeKloosterman
  refine Fintype.sum_equiv (Equiv.mulLeft t) _ _ fun x => ?_
  rw [Equiv.coe_mulLeft, Units.val_mul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem orbit_le_fourthMoment (a b : 𝔽) (ha : a ≠ 0) :
    ((p - 1 : ℕ) : ℝ) * ‖primeKloosterman a b‖ ^ 4 ≤
      ∑ a' : 𝔽, ∑ b' : 𝔽, ‖primeKloosterman a' b'‖ ^ 4 := by
  classical
  let orbit (t : 𝕌) : 𝔽 × 𝔽 := (a * (t : 𝔽), b / (t : 𝔽))
  have hinj : Function.Injective orbit := by
    intro t u h
    exact Units.ext (mul_left_cancel₀ ha (congrArg Prod.fst h))
  calc
    _ = ∑ t : 𝕌, ‖primeKloosterman (orbit t).1 (orbit t).2‖ ^ 4 := by
      simp only [orbit, primeKloosterman_scale, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ZMod.card_units]
    _ = ∑ c ∈ Finset.univ.image orbit, ‖primeKloosterman c.1 c.2‖ ^ 4 := by
      rw [Finset.sum_image hinj.injOn]
    _ ≤ ∑ c : 𝔽 × 𝔽, ‖primeKloosterman c.1 c.2‖ ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = _ := Fintype.sum_prod_type _

/-- At zero first coefficient, inversion and additive orthogonality give the value `-1`. -/
theorem primeKloosterman_zero_left {b : 𝔽} (hb : b ≠ 0) : primeKloosterman 0 b = -1 := by
  classical
  have hinv : primeKloosterman 0 b = ∑ x : 𝕌, χ (b * (x : 𝔽)) := by
    unfold primeKloosterman
    refine Fintype.sum_equiv (Equiv.inv 𝕌) _ _ fun x => ?_
    change χ (0 * (x : 𝔽) + b * (x : 𝔽)⁻¹) = χ (b * ((x⁻¹ : 𝕌) : 𝔽))
    simp only [zero_mul, zero_add, Units.val_inv_eq_inv_val]
  have himage : ((Finset.univ : Finset 𝕌).image fun x : 𝕌 => (x : 𝔽)) =
      (Finset.univ : Finset 𝔽).erase 0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨u, rfl⟩
      exact u.ne_zero
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hrestrict : (∑ x : 𝕌, χ (b * (x : 𝔽))) =
      ∑ x ∈ (Finset.univ : Finset 𝔽).erase 0, χ (b * x) := by
    rw [← himage, Finset.sum_image Units.val_injective.injOn]
  have hsum : (∑ x : 𝔽, χ (b * x)) = 0 := by
    simpa [mul_comm b, hb] using sum_stdAddChar b
  have hwhole := Finset.sum_erase_add (Finset.univ : Finset 𝔽) (fun x => χ (b * x))
    (Finset.mem_univ (0 : 𝔽))
  rw [hsum, mul_zero, AddChar.map_zero_eq_one] at hwhole
  rw [hinv, hrestrict]
  exact eq_neg_of_add_eq_zero_left hwhole

/-- An elementary prime Kloosterman bound, including a zero first coefficient. -/
theorem norm_primeKloosterman_pow_four_le (a b : 𝔽) (hb : b ≠ 0) :
    ‖primeKloosterman a b‖ ^ 4 ≤ 3 * (p : ℝ) ^ 3 := by
  have hp := (Fact.out : p.Prime).one_lt
  by_cases ha : a = 0
  · rw [ha, primeKloosterman_zero_left hb, norm_neg, norm_one, one_pow]
    have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.le
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ 3 := by
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hp' 3
    nlinarith
  · have hd : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hp
    have hd_le : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast Nat.sub_le p 1
    have hcard : ((fourthMomentSolutions p).card : ℝ) ≤ 3 * ((p - 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast card_fourthMomentSolutions_le (p := p)
    have horbit := orbit_le_fourthMoment a b ha
    rw [fourthMoment_eq] at horbit
    refine le_of_mul_le_mul_left ?_ hd
    calc
      _ ≤ (p : ℝ) ^ 2 * ((fourthMomentSolutions p).card : ℝ) := horbit
      _ ≤ (p : ℝ) ^ 2 * (3 * ((p - 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
      _ = ((p - 1 : ℕ) : ℝ) * (3 * (p : ℝ) ^ 2 * ((p - 1 : ℕ) : ℝ)) := by ring
      _ ≤ ((p - 1 : ℕ) : ℝ) * (3 * (p : ℝ) ^ 2 * (p : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd_le (by positivity)) hd.le
      _ = _ := by ring

end D5.S3.CharacterSums.PrimeKloostermanFourthMoment
