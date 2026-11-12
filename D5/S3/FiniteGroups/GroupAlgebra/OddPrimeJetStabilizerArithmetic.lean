/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetStabilizerArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/group_theory/index]
   utility: none
   digest: The actual odd-prime jet label stabilizer has order dividing the weighted semilinear ambient order.
-/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup

/-! The label stabilizer contributes a genuine finite-field divisor constraint
to the full odd-prime jet automorphism group. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
open Polynomial Module OddPrimeJetDeformation OddPrimeJetDerivationRigidity
open OddPrimeJetPairClassification OddPrimeJetCommutant FiniteJetClassification
  FiniteJetCoefficients
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "𝔽" => ZMod p
variable [Fintype K] {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n)
variable (A : Fin (n - 1) → K)
local notation "q" => Q (p := p) n A
local notation "𝒮" => labelGroup q

include hn hK in
/-- The actual coefficient-label stabilizer is arithmetically constrained by the
weighted semilinear group of the finite field.  Thus the stabilizer factor in
the full jet-group order can only use divisors of `(p^n-1)n`. -/
theorem labelGroup_card_dvd_weighted_ambient :
    Nat.card 𝒮 ∣ (p ^ n - 1) * n := by
  let L := Shrink.{0} K
  let e : K ≃ₐ[𝔽] L :=
    (@Shrink.algEquiv 𝔽 K (inferInstance : Small.{0} K) _ _ _).symm
  have hL : Fintype.card L = p ^ n := by
    simpa [L] using hK
  have hdim : Module.finrank 𝔽 L = n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    exact (FiniteField.pow_finrank_eq_card p L).trans hL
  have hambient : Nat.card (WeightedSemilinear.Group 𝔽 L) = (p ^ n - 1) * n := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      Nat.card_units, Nat.card_eq_fintype_card (α := L), hL,
      IsGalois.card_aut_eq_finrank, hdim]
  have hsub : Nat.card (weightedStabilizer (p := p) A e) ∣
      Nat.card (WeightedSemilinear.Group 𝔽 L) :=
    (weightedStabilizer (p := p) A e).card_subgroup_dvd_card
  rw [Nat.card_congr (weightedStabilizerEquiv (p := p) hn hK A e).toEquiv,
    hambient] at hsub
  exact hsub

include hn hK in
/-- Consequently the entire full original-label jet group has order dividing
the explicit commutant factor times the weighted semilinear ambient order. -/
theorem full_cardinality_dvd_weighted_ambient :
    Nat.card (originalGroup (p := p) q) ∣
      ((p ^ n - 1) * p ^ (n * (p - 2) + n * n)) * ((p ^ n - 1) * n) := by
  rw [full_cardinality hn hK A]
  exact Nat.mul_dvd_mul_left _ (labelGroup_card_dvd_weighted_ambient hn hK A)

include hn hK in
/-- A primitive second coordinate collapses the label stabilizer to the identity.
The first coordinate is normalized to one, while the second generates all field
units, so the weighted action fixes no nontrivial scalar or field automorphism. -/
theorem labelGroup_cardinality_of_primitive_coordinates
    (hn3 : 3 ≤ n)
    (hA0 : A (⟨0, by omega⟩ : Fin (n - 1)) = 1)
    (hprimitive : ∀ x : Kˣ, ∃ m : ℕ,
      A (⟨1, by omega⟩ : Fin (n - 1)) ^ m = (x : K)) :
    Nat.card 𝒮 = 1 := by
  letI : Subsingleton 𝒮 :=
    labelGroup_subsingleton_of_primitive_coordinates hn hK A hn3 hA0 hprimitive
  exact Nat.card_of_subsingleton (1 : 𝒮)

include hn hK in
/-- Under the same primitive-coordinate hypothesis, the full jet group has the
exact commutant order; no label-stabilizer factor remains. -/
theorem full_cardinality_of_primitive_coordinates
    (hn3 : 3 ≤ n)
    (hA0 : A (⟨0, by omega⟩ : Fin (n - 1)) = 1)
    (hprimitive : ∀ x : Kˣ, ∃ m : ℕ,
      A (⟨1, by omega⟩ : Fin (n - 1)) ^ m = (x : K)) :
    Nat.card (originalGroup (p := p) q) =
      (p ^ n - 1) * p ^ (n * (p - 2) + n * n) := by
  rw [full_cardinality hn hK A,
    labelGroup_cardinality_of_primitive_coordinates hn hK A hn3 hA0 hprimitive,
    mul_one]

#print axioms labelGroup_card_dvd_weighted_ambient
#print axioms full_cardinality_dvd_weighted_ambient
#print axioms labelGroup_cardinality_of_primitive_coordinates
#print axioms full_cardinality_of_primitive_coordinates
end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGroup
