/- GID: D5/S3/FiniteGroups/Semilinear/WeightedOrbits
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Semilinear/WeightedOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual weighted semilinear finite-field actions and their orbit divisor formula. -/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import D5.S3.FiniteGroups.Semilinear.WeightedArithmetic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! Weighted scalar powers and finite-field automorphisms act on the entire coefficient space. -/

set_option autoImplicit false

open scoped Classical

namespace WeightedSemilinear

universe u v

variable (F K : Type) [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]

/-- The actual action of field automorphisms on the multiplicative group. -/
def unitsAut : Gal(K/F) →* MulAut Kˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- Scalars and field automorphisms, with the genuine semidirect product law. -/
abbrev Group := Kˣ ⋊[unitsAut F K] Gal(K/F)

variable {F K}
variable {I : Type u} (w : I → ℕ)

/-- The inverse scalar powers use the original weights at every coordinate. -/
def act (g : Group F K) (A : I → K) : I → K :=
  fun i => ((g.left⁻¹ : Kˣ) : K) ^ w i * g.right (A i)

def weightedAction : MulAction (Group F K) (I → K) where
  smul := act w
  one_smul A := by
    funext i
    change act w 1 A i = A i
    simp [act]
  mul_smul g h A := by
    funext i
    change act w (g * h) A i = act w g (act w h A) i
    simp [act, SemidirectProduct.mul_left, SemidirectProduct.mul_right, unitsAut,
      mul_pow, map_mul, map_pow, map_inv, mul_assoc, mul_left_comm, mul_comm]

/-- This is the actual orbit relation of the weighted semilinear action. -/
def Orbits :=
  letI := weightedAction (F := F) (K := K) w
  MulAction.orbitRel.Quotient (Group F K) (I → K)

noncomputable instance : Fintype (Group F K) :=
  Fintype.ofEquiv (Kˣ × Gal(K/F)) SemidirectProduct.equivProd.symm

private theorem fixed_card_eq [Fintype I] (g : Group F K) :
    letI := weightedAction (F := F) (K := K) w
    Nat.card (MulAction.fixedBy (I → K) g) =
      Nat.card {A : I → K // ∀ i, g.right (A i) = (g.left : K) ^ w i * A i} := by
  letI := weightedAction (F := F) (K := K) w
  change Nat.card {A : I → K // act w g A = A} = _
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro A
  constructor
  · intro h i
    have hi := congrFun h i
    change ((g.left⁻¹ : Kˣ) : K) ^ w i * g.right (A i) = A i at hi
    calc
      g.right (A i) = (g.left : K) ^ w i *
          (((g.left⁻¹ : Kˣ) : K) ^ w i * g.right (A i)) := by
        rw [← mul_assoc, ← mul_pow, ← Units.val_mul]
        simp
      _ = (g.left : K) ^ w i * A i := by rw [hi]
  · intro h
    funext i
    change ((g.left⁻¹ : Kˣ) : K) ^ w i * g.right (A i) = A i
    rw [h i, ← mul_assoc, ← mul_pow, ← Units.val_mul]
    simp

private theorem orbit_average [Fintype I] :
    (Nat.card (Orbits (F := F) (K := K) w) : ℚ) =
      (1 / (Module.finrank F K : ℚ)) *
        ∑ σ : Gal(K/F),
          (∑ c : Kˣ,
            (Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} : ℚ)) /
              (Fintype.card K - 1 : ℕ) := by
  classical
  letI := weightedAction (F := F) (K := K) w
  have hg : Fintype.card (Group F K) = (Fintype.card K - 1) * Module.finrank F K := by
    rw [← Nat.card_eq_fintype_card, SemidirectProduct.card,
      Nat.card_units, IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hsum : (∑ g : Group F K, Nat.card (MulAction.fixedBy (I → K) g)) =
      ∑ σ : Gal(K/F), ∑ c : Kˣ,
        Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} := by
    simp_rw [fixed_card_eq w]
    rw [Fintype.sum_equiv SemidirectProduct.equivProd
      (fun g : Group F K => Nat.card {A : I → K //
        ∀ i, g.right (A i) = (g.left : K) ^ w i * A i})
      (fun z : Kˣ × Gal(K/F) => Nat.card {A : I → K //
        ∀ i, z.2 (A i) = (z.1 : K) ^ w i * A i}) (fun _ => rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Group F K) (I → K)
  have hbn : (∑ g : Group F K, Nat.card (MulAction.fixedBy (I → K) g)) =
      Nat.card (MulAction.orbitRel.Quotient (Group F K) (I → K)) *
        Fintype.card (Group F K) := by
    simpa only [Nat.card_eq_fintype_card] using hb
  rw [hsum, hg] at hbn
  have hb' :
      (∑ σ : Gal(K/F), ∑ c : Kˣ,
        (Nat.card {A : I → K // ∀ i, σ (A i) = (c : K) ^ w i * A i} : ℚ)) =
      (Nat.card (Orbits (F := F) (K := K) w) : ℚ) *
        ((Fintype.card K - 1 : ℕ) * (Module.finrank F K : ℚ)) := by
    exact_mod_cast hbn
  have hn : (Module.finrank F K : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos.ne' : Module.finrank F K ≠ 0)
  have hQ : ((Fintype.card K - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt Fintype.one_lt_card : Fintype.card K - 1 ≠ 0)
  rw [← Finset.sum_div, one_div, inv_mul_eq_div]
  apply (eq_div_iff hn).mpr
  apply (eq_div_iff hQ).mpr
  linear_combination -hb'

/-- The cardinality of the actual weighted semilinear orbit quotient, uniformly in the field. -/
theorem orbit_cardinality (p n : ℕ) [Fact p.Prime]
    {L : Type} [Field L] [Fintype L] [Algebra (ZMod p) L]
    {J : Type u} [Fintype J] (weights : J → ℕ)
    (hL : Fintype.card L = p ^ n) :
    (Nat.card (Orbits (F := ZMod p) (K := L) weights) : ℚ) =
      (1 / (n : ℚ)) *
        ∑ d ∈ n.divisors, (Nat.totient (n / d) : ℚ) / (p ^ d - 1 : ℕ) *
          ∑ m ∈ (p ^ d - 1).divisors, (Nat.totient m : ℚ) *
            (p : ℚ) ^ (d * (Finset.univ.filter (fun i => m ∣ weights i)).card) := by
  classical
  have hrank : Module.finrank (ZMod p) L = n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    exact (FiniteField.pow_finrank_eq_card p L).trans hL
  rw [orbit_average weights, fixed_average weights, hrank, ZMod.card]

#print axioms orbit_cardinality

end WeightedSemilinear
