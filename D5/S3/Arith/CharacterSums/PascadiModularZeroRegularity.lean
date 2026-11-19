/- GID: D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiModularZeroRegularity
   mirror-E: none(waiver:symbolic-dividing-branch-bound)
   anchors: []
   utility: none
   digest: Actual dividing pairs supply the regularity for subpower counting. -/

import D5.S3.Arith.CharacterSums.PascadiModularZeroPartners

/-! # Regularity in the actual dividing branch

The actual linear observation and nonalignment exclude exceptional scalars and zero
determinants. The original integer partner set then satisfies the established
subpower estimate without separate regularity assumptions.
-/

namespace D5.S3.Arith.CharacterSums.Original

open Polynomial

noncomputable section

/-- One dividing direction of a nonaligned actual pair has a uniform subpower
partner bound. All line and determinant regularity is derived from the actual
pair and the small coordinate box. -/
theorem actual_dividing_modular_zero_partner_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ : ℝ)
      (E : Finset Coordinate) (α β : ZMod p) (q a b : Coordinate),
      ActualPair E α β q (a, b) → ¬ Aligned q (a, b) →
      (endpointL q (a, b)).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 →
      α ≠ 0 → α * (α + (q.1 : ZMod p) + β * q.2) ≠ 0 →
      CoordinateBound J₁ J₂ q →
      (∀ z ∈ E, CoordinateBound J₁ J₂ z) →
      8 * J₁ * J₂ < p →
      (coordinateDet a (a + b - q) : ZMod p) = 0 →
      ((modularZeroPartners E α β q (a, b)).card : ℝ) ≤ C * (p : ℝ)^ε := by
  obtain ⟨C, hC, hcount⟩ := regular_dividing_modular_zero_partner_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ E α β q a b he hnonaligned hL hα hκ hqBound hE hsmall hdivide
  letI : Fact p.Prime := ⟨hp⟩
  have haBound := hE a he.1
  have hbBound := hE b he.2.1
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod p)) β =
      (n : ZMod p) := map_intCast
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) β) n
  have hLlin : (a.1 : ZMod p) + b.1 - q.1 +
      β * ((a.2 : ZMod p) + b.2 - q.2) ≠ 0 := by
    simpa [endpointL, PrimeCube.linear, coeffL, coeffM, heval, mul_comm] using hL
  have hQlin : ((a.1 : ZMod p) + β * a.2) *
      ((b.1 : ZMod p) + β * b.2) ≠ 0 := by
    intro hz
    have hid : α * ((a.1 : ZMod p) + b.1 - q.1 +
        β * ((a.2 : ZMod p) + b.2 - q.2)) +
        ((a.1 : ZMod p) + β * a.2) * ((b.1 : ZMod p) + β * b.2) = 0 := by
      have h := he.2.2
      dsimp [actualValue] at h
      linear_combination h
    rw [hz, add_zero] at hid
    exact (mul_ne_zero hα hLlin) hid
  have ha : (a.1 : ZMod p) ≠ 0 ∨ (a.2 : ZMod p) ≠ 0 := by
    by_contra hz
    push Not at hz
    exact hQlin (by simp [hz.1, hz.2])
  obtain ⟨c, hc₁, hc₂⟩ := fieldDet_zero_scalar
    ((a.1 : ZMod p), (a.2 : ZMod p))
    ((a.1 : ZMod p) + b.1 - q.1, (a.2 : ZMod p) + b.2 - q.2) ha
    (by simpa [fieldDet, coordinateDet] using hdivide)
  change (a.1 : ZMod p) + b.1 - q.1 = c * a.1 at hc₁
  change (a.2 : ZMod p) + b.2 - q.2 = c * a.2 at hc₂
  have hline : (q.1 : ZMod p) = (b.1 : ZMod p) + (1 - c) * a.1 ∧
      (q.2 : ZMod p) = (b.2 : ZMod p) + (1 - c) * a.2 := by
    constructor
    · linear_combination -hc₁
    · linear_combination -hc₂
  have hc : c ≠ 0 := by
    intro hz
    apply hLlin
    rw [hc₁, hc₂, hz]
    ring
  have hcOne : c ≠ 1 := by
    intro hc1
    have hbq₁ : (b.1 : ZMod p) = q.1 := by
      simpa [hc1] using hline.1.symm
    have hbq₂ : (b.2 : ZMod p) = q.2 := by
      simpa [hc1] using hline.2.symm
    have hqval : actualValue α β q ≠ 0 := (mul_ne_zero_iff.mp hκ).2
    have haval : (a.1 : ZMod p) + β * a.2 ≠ 0 := by
      simpa [hbq₁, hbq₂] using hLlin
    have hprod : ((a.1 : ZMod p) + β * a.2) * actualValue α β q = 0 := by
      have h := he.2.2
      dsimp [actualValue] at h ⊢
      rw [hbq₁, hbq₂] at h
      linear_combination h
    exact (mul_ne_zero haval hqval) hprod
  have hJ₁ : 0 ≤ J₁ := (abs_nonneg _).trans hqBound.1
  have hJ₂ : 0 ≤ J₂ := (abs_nonneg _).trans hqBound.2
  have h0Bound : CoordinateBound J₁ J₂ (0 : Coordinate) := by
    simpa [CoordinateBound] using And.intro hJ₁ hJ₂
  have h00Bound : CoordinateBound (2 * J₁) (2 * J₂) (0 : Coordinate) := by
    simpa [CoordinateBound] using
      (show 0 ≤ 2 * J₁ ∧ 0 ≤ 2 * J₂ from ⟨by positivity, by positivity⟩)
  have hlift (z : Coordinate) (hz : CoordinateBound J₁ J₂ z)
      (hm : (coordinateDet q z : ZMod p) = 0) : coordinateDet q z = 0 := by
    have hmLine : ModularLinePair p q q 0 (z, 0) := by
      exact ⟨hm, by simp [coordinateDet], by simp [coordinateDet]⟩
    exact (modular_line_pair_integer_lift q q 0 (z, 0) hqBound hqBound
      h00Bound hz h0Bound hsmall hmLine).1
  have hD : (coordinateDet b q : ZMod p) ≠ 0 := by
    intro hz
    simp only [coordinateDet, Int.cast_sub, Int.cast_mul] at hz
    rw [hline.1, hline.2] at hz
    have hab : (coordinateDet a b : ZMod p) = 0 := by
      have hprod : (1 - c) * (coordinateDet a b : ZMod p) = 0 := by
        simp only [coordinateDet, Int.cast_sub, Int.cast_mul]
        linear_combination -hz
      exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hcOne.symm)
    have hqa : (coordinateDet q a : ZMod p) = 0 := by
      simp only [coordinateDet, Int.cast_sub, Int.cast_mul] at hab ⊢
      rw [hline.1, hline.2]
      linear_combination -hab
    have hqb : (coordinateDet q b : ZMod p) = 0 := by
      simp only [coordinateDet, Int.cast_sub, Int.cast_mul] at hab ⊢
      rw [hline.1, hline.2]
      linear_combination (1 - c) * hab
    exact hnonaligned ⟨hlift a haBound hqa, hlift b hbBound hqb⟩
  have hab : (coordinateDet a b : ZMod p) ≠ 0 := by
    intro hz
    apply hD
    simp only [coordinateDet, Int.cast_sub, Int.cast_mul] at hz ⊢
    rw [hline.1, hline.2]
    linear_combination (c - 1) * hz
  have hΔmod : (coordinateDet b (a - q) : ZMod p) =
      -c * (coordinateDet a b : ZMod p) := by
    change ((b.1 * (a.2 - q.2) - b.2 * (a.1 - q.1) : ℤ) : ZMod p) =
      -c * ((a.1 * b.2 - a.2 * b.1 : ℤ) : ZMod p)
    push_cast
    rw [hline.1, hline.2]
    ring
  have hΔ : coordinateDet b (a - q) ≠ 0 := by
    intro hz
    have hm : (coordinateDet b (a - q) : ZMod p) = 0 := by rw [hz]; simp
    rw [hΔmod] at hm
    exact (mul_ne_zero (neg_ne_zero.mpr hc) hab) hm
  have hACmod : ((coordinateDet q (a - q) * coordinateDet q b : ℤ) : ZMod p) =
      (c - 1) * (coordinateDet a b : ZMod p)^2 := by
    change (((q.1 * (a.2 - q.2) - q.2 * (a.1 - q.1)) *
      (q.1 * b.2 - q.2 * b.1) : ℤ) : ZMod p) =
        (c - 1) * ((a.1 * b.2 - a.2 * b.1 : ℤ) : ZMod p)^2
    push_cast
    rw [hline.1, hline.2]
    ring
  have hAC : coordinateDet q (a - q) * coordinateDet q b ≠ 0 := by
    intro hz
    have hm : ((coordinateDet q (a - q) * coordinateDet q b : ℤ) : ZMod p) = 0 := by
      rw [hz]
      simp
    rw [hACmod] at hm
    exact (mul_ne_zero (sub_ne_zero.mpr hcOne) (pow_ne_zero 2 hab)) hm
  have hhBound : CoordinateBound (2 * J₁) (2 * J₂) (a - q) := by
    constructor
    · change |((a.1 - q.1 : ℤ) : ℝ)| ≤ _
      push_cast
      exact (abs_sub _ _).trans (by linarith [haBound.1, hqBound.1])
    · change |((a.2 - q.2 : ℤ) : ℝ)| ≤ _
      push_cast
      exact (abs_sub _ _).trans (by linarith [haBound.2, hqBound.2])
  exact hcount p hp J₁ J₂ E α β q a b c hqBound hbBound hhBound hE hsmall
    hc hD hline hΔ hAC

/-- Both dividing directions satisfy the same uniform subpower bound. Swapping
the base endpoints preserves the original pencil and the full partner set. -/
theorem actual_dividing_branches_modular_zero_partner_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ : ℝ)
      (E : Finset Coordinate) (α β : ZMod p) (q a b : Coordinate),
      ActualPair E α β q (a, b) → ¬ Aligned q (a, b) →
      (endpointL q (a, b)).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 →
      α ≠ 0 → α * (α + (q.1 : ZMod p) + β * q.2) ≠ 0 →
      CoordinateBound J₁ J₂ q →
      (∀ z ∈ E, CoordinateBound J₁ J₂ z) →
      8 * J₁ * J₂ < p →
      ((coordinateDet a (a + b - q) : ZMod p) = 0 ∨
        (coordinateDet (a + b - q) b : ZMod p) = 0) →
      ((modularZeroPartners E α β q (a, b)).card : ℝ) ≤ C * (p : ℝ)^ε := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_dividing_modular_zero_partner_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ E α β q a b he hnonaligned hL hα hκ hqBound hE hsmall hdivide
  rcases hdivide with hleft | hright
  · exact hcount p hp J₁ J₂ E α β q a b he hnonaligned hL hα hκ hqBound hE hsmall hleft
  · have hLswap : endpointL q (b, a) = endpointL q (a, b) := by
      simp [endpointL, coeffL, coeffM, add_comm]
    have hQswap : endpointQ (b, a) = endpointQ (a, b) := by
      simp [endpointQ, coeffQ, coeffR, coeffS, mul_comm, add_comm]
    have hpartners : modularZeroPartners E α β q (a, b) =
        modularZeroPartners E α β q (b, a) := by
      unfold modularZeroPartners
      apply Finset.filter_congr
      intro e _
      simp only [pencil, hLswap, hQswap]
    have heSwap : ActualPair E α β q (b, a) := by
      refine ⟨he.2.1, he.1, ?_⟩
      calc
        actualValue α β b * actualValue α β a =
            actualValue α β a * actualValue α β b := mul_comm _ _
        _ = _ := he.2.2
    have hnonalignedSwap : ¬ Aligned q (b, a) :=
      fun hz => hnonaligned ⟨hz.2, hz.1⟩
    have hLSwap : (endpointL q (b, a)).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 := by
      rw [hLswap]
      exact hL
    have hrightSwap : (coordinateDet b (b + a - q) : ZMod p) = 0 := by
      have hskew : coordinateDet b (b + a - q) = -coordinateDet (a + b - q) b := by
        dsimp [coordinateDet]
        ring
      rw [hskew]
      simpa only [Int.cast_neg, neg_eq_zero] using hright
    rw [hpartners]
    exact hcount p hp J₁ J₂ E α β q b a heSwap hnonalignedSwap hLSwap hα hκ
      hqBound hE hsmall hrightSwap

end
end D5.S3.Arith.CharacterSums.Original
