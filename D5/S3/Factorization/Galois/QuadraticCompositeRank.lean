/- GID: D5/S3/Factorization/Galois/QuadraticCompositeRank
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/QuadraticCompositeRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rank four and Klein group for Q(sqrt2,sqrt3), with zero and collapse audits. -/
/- Library-search audit trail (2026-08-25):
   * The original theorem gives no premises. This module supplies K = Q, r = 2, radicals
     2 and 3, and the concrete tower Q(sqrt 2, sqrt 3). The proof verifies that 2 is not
     a square in Q and that 3 is not a square in Q(sqrt 2), which is the needed concrete
     square-class independence condition. Without it, the degree conclusion is false.
   * Repository searches for `IsGalois|adjoin|Kummer|quadratic` covered D5/S1/Quad,
     D5/S0/Carrier/AlgebraicModel, and this directory. They contain one-quadratic-field
     models and general restriction maps, but no biquadratic rank theorem.
   * Pinned Mathlib searches covered `QuadraticAlgebra`, `KummerExtension`, `IsGalois`,
     `IntermediateField.adjoin`, `AlgEquiv.card_le`, and `IsKleinFour`. Exact reused hits
     are `QuadraticAlgebra.finrank_eq_two`, `AlgEquiv.card_le`,
     `Module.finrank_mul_finrank`, and `IsKleinFour.nonempty_mulEquiv`.
   * No theorem for an independent family in K^*/(K^*)^2 was found. The pinned Kummer
     file handles one cyclic radical and records a degree-two TODO. Thus general r is not
     claimed here; the required r = 2 concrete case is fully proved.
   * The r = 0 and r = 1 cases are named theorems below. A square radicand and the pair
     2, 8 audit the two collapse modes. Characteristic two is excluded by choosing Q;
     sign separation is used when proving the displayed automorphisms distinct. The
     characteristic-two theorem below shows that this step collapses in ZMod 2.
   * Primality of 2 and 3 is not a hypothesis and bears no formal weight. Only the
     explicit nonsquare calculations are used. There is no empty carrier or map input;
     the trivial extension and its identity automorphism are exactly the r = 0 audit. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped QuadraticAlgebra

noncomputable section

namespace D5.S3.Factorization.Galois.QuadraticCompositeRank

private theorem rat_two_not_square (x : ℚ) : x ^ 2 ≠ 2 := by
  intro hx
  have hs : IsSquare (2 : ℚ) := ⟨x, by simpa [pow_two] using hx.symm⟩
  norm_num [Rat.isSquare_ofNat_iff] at hs

private theorem rat_three_not_square (x : ℚ) : x ^ 2 ≠ 3 := by
  intro hx
  have hs : IsSquare (3 : ℚ) := ⟨x, by simpa [pow_two] using hx.symm⟩
  norm_num [Rat.isSquare_ofNat_iff] at hs

private theorem rat_three_halves_not_square (x : ℚ) : x ^ 2 ≠ 3 / 2 := by
  intro hx
  have hs : IsSquare (3 / 2 : ℚ) := ⟨x, by simpa [pow_two] using hx.symm⟩
  norm_num [Rat.isSquare_iff] at hs

local instance sqrtTwoFact : Fact (∀ x : ℚ, x ^ 2 ≠ 2 + 0 * x) :=
  ⟨by simpa using rat_two_not_square⟩

/-- The concrete field model for `Q(sqrt 2)`. -/
abbrev SqrtTwoField := QuadraticAlgebra ℚ 2 0

private theorem three_not_square_in_sqrtTwo (z : SqrtTwoField) :
    z ^ 2 ≠ algebraMap ℚ SqrtTwoField 3 := by
  intro hz
  have hre : z.re * z.re + 2 * z.im * z.im = 3 := by
    simpa [pow_two] using congrArg QuadraticAlgebra.re hz
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg QuadraticAlgebra.im hz
  have hxy : z.re = 0 ∨ z.im = 0 := by
    apply mul_eq_zero.mp
    nlinarith [him]
  rcases hxy with hre0 | him0
  · apply rat_three_halves_not_square z.im
    nlinarith
  · apply rat_three_not_square z.re
    nlinarith

local instance sqrtThreeFact :
    Fact (∀ z : SqrtTwoField, z ^ 2 ≠ algebraMap ℚ SqrtTwoField 3 + 0 * z) :=
  ⟨by simpa using three_not_square_in_sqrtTwo⟩

/-- The concrete two-step field model for `Q(sqrt 2, sqrt 3)`. -/
abbrev SqrtTwoSqrtThreeField :=
  QuadraticAlgebra SqrtTwoField (algebraMap ℚ SqrtTwoField 3) 0

/-- The multiplicative Klein four-group appearing as the Galois group. -/
abbrev KleinFourGroup := Multiplicative (ZMod 2 × ZMod 2)

/-- The chosen square root of two in the composite field. -/
def sqrtTwo : SqrtTwoSqrtThreeField :=
  algebraMap SqrtTwoField SqrtTwoSqrtThreeField QuadraticAlgebra.omega

/-- The chosen square root of three in the composite field. -/
def sqrtThree : SqrtTwoSqrtThreeField := QuadraticAlgebra.omega

/-- At rank zero, the extension and its Galois group are both trivial. -/
theorem rank_zero_case :
    Module.finrank ℚ ℚ = 1 ∧ Nat.card Gal(ℚ/ℚ) = 1 := by
  constructor
  · simp
  · rw [IsGalois.card_aut_eq_finrank]
    simp

#print axioms rank_zero_case

private def conjugateSqrtTwo : SqrtTwoField ≃ₐ[ℚ] SqrtTwoField where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> abel
  commutes' q := by ext <;> simp

private def twoAutomorphisms : Bool → Gal(SqrtTwoField/ℚ)
  | false => 1
  | true => conjugateSqrtTwo

private theorem twoAutomorphisms_injective : Function.Injective twoAutomorphisms := by
  intro i j hij
  have h := congrArg
    (fun sigma : Gal(SqrtTwoField/ℚ) => (sigma QuadraticAlgebra.omega).im) hij
  clear hij
  cases i <;> cases j <;>
    simp_all [twoAutomorphisms, conjugateSqrtTwo] <;> norm_num at h

private theorem sqrtTwo_galois_card : Nat.card Gal(SqrtTwoField/ℚ) = 2 := by
  letI := AlgEquiv.fintype ℚ SqrtTwoField
  rw [Nat.card_eq_fintype_card]
  apply le_antisymm
  · simpa only [QuadraticAlgebra.finrank_eq_two] using
      (AlgEquiv.card_le (F := ℚ) (K := SqrtTwoField))
  · simpa using
      Fintype.card_le_of_injective twoAutomorphisms twoAutomorphisms_injective

/-- At rank one, adjoining the nonsquare two has degree two and two automorphisms. -/
theorem rank_one_case :
    Module.finrank ℚ SqrtTwoField = 2 ∧ Nat.card Gal(SqrtTwoField/ℚ) = 2 := by
  exact ⟨QuadraticAlgebra.finrank_eq_two (2 : ℚ) 0, sqrtTwo_galois_card⟩

#print axioms rank_one_case

/-- The concrete independent two-radical composite has degree four over `Q`. -/
theorem sqrt_two_sqrt_three_rank :
    Module.finrank ℚ SqrtTwoSqrtThreeField = 4 := by
  rw [← Module.finrank_mul_finrank ℚ SqrtTwoField SqrtTwoSqrtThreeField]
  simp only [QuadraticAlgebra.finrank_eq_two]

#print axioms sqrt_two_sqrt_three_rank

private def flipSqrtTwo : Gal(SqrtTwoSqrtThreeField/ℚ) where
  toFun z := ⟨conjugateSqrtTwo z.re, conjugateSqrtTwo z.im⟩
  invFun z := ⟨conjugateSqrtTwo z.re, conjugateSqrtTwo z.im⟩
  left_inv z := by ext <;> simp [conjugateSqrtTwo]
  right_inv z := by ext <;> simp [conjugateSqrtTwo]
  map_mul' x y := by ext <;> simp [conjugateSqrtTwo] <;> ring
  map_add' x y := by ext <;> simp [conjugateSqrtTwo] <;> abel
  commutes' q := by ext <;> simp [conjugateSqrtTwo]

private def flipSqrtThree : Gal(SqrtTwoSqrtThreeField/ℚ) where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> abel
  commutes' q := by ext <;> simp

private theorem flipSqrtTwo_sqrtTwo : flipSqrtTwo sqrtTwo = -sqrtTwo := by
  ext <;> simp [flipSqrtTwo, conjugateSqrtTwo, sqrtTwo]

private theorem flipSqrtTwo_sqrtThree : flipSqrtTwo sqrtThree = sqrtThree := by
  ext <;> simp [flipSqrtTwo, conjugateSqrtTwo, sqrtThree]

private theorem flipSqrtThree_sqrtTwo : flipSqrtThree sqrtTwo = sqrtTwo := by
  ext <;> simp [flipSqrtThree, sqrtTwo]

private theorem flipSqrtThree_sqrtThree : flipSqrtThree sqrtThree = -sqrtThree := by
  ext <;> simp [flipSqrtThree, sqrtThree]

private theorem sqrtTwo_ne_neg : sqrtTwo ≠ -sqrtTwo := by
  intro h
  have hc := congrArg (fun z : SqrtTwoSqrtThreeField => z.re.im) h
  norm_num [sqrtTwo] at hc

private theorem sqrtThree_ne_neg : sqrtThree ≠ -sqrtThree := by
  intro h
  have hc := congrArg (fun z : SqrtTwoSqrtThreeField => z.im.re) h
  norm_num [sqrtThree] at hc

private theorem neg_sqrtTwo_ne : -sqrtTwo ≠ sqrtTwo := sqrtTwo_ne_neg.symm

private theorem neg_sqrtThree_ne : -sqrtThree ≠ sqrtThree := sqrtThree_ne_neg.symm

private def fourAutomorphisms : Bool × Bool → Gal(SqrtTwoSqrtThreeField/ℚ)
  | (false, false) => 1
  | (true, false) => flipSqrtTwo
  | (false, true) => flipSqrtThree
  | (true, true) => flipSqrtTwo * flipSqrtThree

private theorem fourAutomorphisms_injective : Function.Injective fourAutomorphisms := by
  intro i j hij
  have hs := congrArg
    (fun sigma : Gal(SqrtTwoSqrtThreeField/ℚ) => (sigma sqrtTwo, sigma sqrtThree)) hij
  clear hij
  rcases i with ⟨i, i'⟩
  rcases j with ⟨j, j'⟩
  cases i <;> cases i' <;> cases j <;> cases j' <;>
    simp_all [fourAutomorphisms, flipSqrtTwo_sqrtTwo, flipSqrtTwo_sqrtThree,
      flipSqrtThree_sqrtTwo, flipSqrtThree_sqrtThree, sqrtTwo_ne_neg,
      sqrtThree_ne_neg, neg_sqrtTwo_ne, neg_sqrtThree_ne]

local instance compositeFinite : Module.Finite ℚ SqrtTwoSqrtThreeField :=
  Module.Finite.trans SqrtTwoField SqrtTwoSqrtThreeField

private theorem composite_galois_card :
    Nat.card Gal(SqrtTwoSqrtThreeField/ℚ) = 4 := by
  letI := AlgEquiv.fintype ℚ SqrtTwoSqrtThreeField
  rw [Nat.card_eq_fintype_card]
  apply le_antisymm
  · simpa [sqrt_two_sqrt_three_rank] using
      (AlgEquiv.card_le (F := ℚ) (K := SqrtTwoSqrtThreeField))
  · simpa using
      Fintype.card_le_of_injective fourAutomorphisms fourAutomorphisms_injective

private theorem fourAutomorphisms_sq (i : Bool × Bool) :
    fourAutomorphisms i ^ 2 = 1 := by
  rcases i with ⟨i, j⟩
  cases i <;> cases j <;> ext z <;>
    simp [fourAutomorphisms, flipSqrtTwo, flipSqrtThree, conjugateSqrtTwo, pow_two]

private theorem fourAutomorphisms_surjective :
    Function.Surjective fourAutomorphisms := by
  letI := AlgEquiv.fintype ℚ SqrtTwoSqrtThreeField
  exact ((Fintype.bijective_iff_injective_and_card fourAutomorphisms).2
    ⟨fourAutomorphisms_injective, by
      simpa [Nat.card_eq_fintype_card] using composite_galois_card.symm⟩).2

/-- The concrete composite's Galois group is the Klein four-group. -/
theorem sqrt_two_sqrt_three_galois_group :
    Nonempty (Gal(SqrtTwoSqrtThreeField/ℚ) ≃* KleinFourGroup) := by
  letI : IsKleinFour Gal(SqrtTwoSqrtThreeField/ℚ) := by
    refine ⟨composite_galois_card, ?_⟩
    haveI : Nontrivial Gal(SqrtTwoSqrtThreeField/ℚ) :=
      Finite.one_lt_card_iff_nontrivial.mp (composite_galois_card ▸ by decide)
    apply (Monoid.exponent_eq_prime_iff Nat.prime_two).2
    intro sigma hsigma
    apply orderOf_eq_prime
    · obtain ⟨i, rfl⟩ := fourAutomorphisms_surjective sigma
      exact fourAutomorphisms_sq i
    · exact hsigma
  exact IsKleinFour.nonempty_mulEquiv

#print axioms sqrt_two_sqrt_three_galois_group

/-- The square root of eight used in the repeated-square-class counterexample. -/
def sqrtEight : SqrtTwoField := 2 * QuadraticAlgebra.omega

/-- A square radicand gives a trivial adjoining field, not a quadratic extension. -/
theorem square_radicand_independence_is_necessary :
    (2 : ℚ) ^ 2 = 4 ∧
      IntermediateField.adjoin ℚ ({(2 : ℚ)} : Set ℚ) = ⊥ ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ ({(2 : ℚ)} : Set ℚ)) = 1 ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ ({(2 : ℚ)} : Set ℚ)) ≠ 2 := by
  have hadjoin : IntermediateField.adjoin ℚ ({(2 : ℚ)} : Set ℚ) = ⊥ := by
    rw [IntermediateField.adjoin_eq_bot_iff]
    simp
  have hrank :
      Module.finrank ℚ (IntermediateField.adjoin ℚ ({(2 : ℚ)} : Set ℚ)) = 1 := by
    rw [hadjoin]
    simp
  exact ⟨by norm_num, hadjoin, hrank, by omega⟩

#print axioms square_radicand_independence_is_necessary

/-- Since `sqrt 8 = 2 * sqrt 2`, adjoining both stays degree two, not degree four. -/
theorem square_class_independence_is_necessary :
    sqrtEight ^ 2 = algebraMap ℚ SqrtTwoField 8 ∧
      IntermediateField.adjoin ℚ
        ({QuadraticAlgebra.omega, sqrtEight} : Set SqrtTwoField) = ⊤ ∧
      Module.finrank ℚ
        (IntermediateField.adjoin ℚ
          ({QuadraticAlgebra.omega, sqrtEight} : Set SqrtTwoField)) = 2 ∧
      Module.finrank ℚ
        (IntermediateField.adjoin ℚ
          ({QuadraticAlgebra.omega, sqrtEight} : Set SqrtTwoField)) ≠ 4 := by
  have hsquare : sqrtEight ^ 2 = algebraMap ℚ SqrtTwoField 8 := by
    ext <;> norm_num [sqrtEight, pow_two]
  have htop :
      IntermediateField.adjoin ℚ
        ({QuadraticAlgebra.omega, sqrtEight} : Set SqrtTwoField) = ⊤ := by
    apply top_unique
    rintro ⟨x, y⟩ _
    rw [QuadraticAlgebra.mk_eq_add_smul_omega]
    apply (IntermediateField.adjoin ℚ
      ({QuadraticAlgebra.omega, sqrtEight} : Set SqrtTwoField)).add_mem
    · exact IntermediateField.algebraMap_mem _ x
    · apply IntermediateField.smul_mem
      exact IntermediateField.subset_adjoin ℚ _ (by simp)
  refine ⟨hsquare, htop, ?_, ?_⟩
  · rw [htop]
    rw [IntermediateField.finrank_top']
    exact QuadraticAlgebra.finrank_eq_two (2 : ℚ) 0
  · have hrank :
        Module.finrank ℚ
          (IntermediateField.adjoin ℚ
            ({QuadraticAlgebra.omega, sqrtEight} : Set SqrtTwoField)) = 2 := by
      rw [htop]
      rw [IntermediateField.finrank_top']
      exact QuadraticAlgebra.finrank_eq_two (2 : ℚ) 0
    omega

#print axioms square_class_independence_is_necessary

/-- The concrete characteristic-two collapse of sign separation. -/
def CharacteristicTwoSignCollapse : Prop :=
  (1 : ZMod 2) = -1 ∧ (fun x : ZMod 2 => x) = fun x => -x

/-- In characteristic two, the two sign choices coincide, so the sign argument is invalid. -/
theorem characteristic_two_sign_separation_is_necessary : CharacteristicTwoSignCollapse := by
  rw [CharacteristicTwoSignCollapse]
  constructor
  · decide
  · funext x
    apply eq_neg_of_add_eq_zero_left
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

#print axioms characteristic_two_sign_separation_is_necessary

end D5.S3.Factorization.Galois.QuadraticCompositeRank
