/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadicalUnits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas]
   utility: none
   digest: Actual radical principal units, exponent and exact cardinality. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
open Polynomial Module OddPrimeJetDeformation OddPrimeJetCommutant
open scoped BigOperators
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
/-- Principal units inside the units of the actual commutant algebra. -/
def principalUnits (q : K →ₗ[F] K) (hq : q 1 = 0) : Subgroup (commutantAlgebra (p := p) (K := K) q)ˣ :=
  (Units.map (leadingHom (p := p) (K := K) q hq).toMonoidHom).ker

private theorem principalUnits_sub_one (q : K →ₗ[F] K) (hq : q 1 = 0) (x : principalUnits (p := p) (K := K) q hq) :
    (x.val : (commutantAlgebra (p := p) (K := K) q)) - 1 ∈ radical (p := p) (K := K) q hq := by
  change leadingHom (p := p) (K := K) q hq ((x.val : (commutantAlgebra (p := p) (K := K) q)) - 1) = 0
  have h : leadingHom (p := p) (K := K) q hq (x.val : (commutantAlgebra (p := p) (K := K) q)) = 1 :=
    congrArg (fun z : Kˣ => (z : K)) x.property
  rw [RingHom.map_sub, RingHom.map_one, h, sub_self]

/-- All principal units commute as actual invertible endomorphisms. -/
theorem principalUnits_commute (q : K →ₗ[F] K) (hq : q 1 = 0) (x y : principalUnits (p := p) (K := K) q hq) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  have h := radical_commute (p := p) q hq ((x.val : (commutantAlgebra (p := p) (K := K) q)) - 1) ((y.val : (commutantAlgebra (p := p) (K := K) q)) - 1)
    (principalUnits_sub_one (p := p) q hq x) (principalUnits_sub_one (p := p) q hq y)
  have he := h.eq
  simp only [sub_mul, mul_sub, one_mul, mul_one] at he
  change (x.val : (commutantAlgebra (p := p) (K := K) q)) * (y.val : (commutantAlgebra (p := p) (K := K) q)) = (y.val : (commutantAlgebra (p := p) (K := K) q)) * (x.val : (commutantAlgebra (p := p) (K := K) q))
  have he' : (x.val : (commutantAlgebra (p := p) (K := K) q)) * (y.val : (commutantAlgebra (p := p) (K := K) q)) + (-(x.val : (commutantAlgebra (p := p) (K := K) q)) - (y.val : (commutantAlgebra (p := p) (K := K) q)) + 1) =
      (y.val : (commutantAlgebra (p := p) (K := K) q)) * (x.val : (commutantAlgebra (p := p) (K := K) q)) + (-(x.val : (commutantAlgebra (p := p) (K := K) q)) - (y.val : (commutantAlgebra (p := p) (K := K) q)) + 1) := by
    convert he using 1 <;> abel
  exact add_right_cancel he'

/-- The principal units have exponent dividing p, for every odd prime including three. -/
theorem principalUnits_pow (q : K →ₗ[F] K) (hq : q 1 = 0) (x : principalUnits (p := p) (K := K) q hq) : x ^ p = 1 := by
  letI : Nontrivial V := ⟨⟨constantLinear (p := p) (K := K) 1, 0, by
    intro h
    have he := congrArg (fun v : V => (v : K[X]).coeff 0) h
    simpa [constantLinear] using he⟩⟩
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  letI : CharP (commutantAlgebra (p := p) (K := K) q) p :=
    charP_of_injective_algebraMap (algebraMap F (commutantAlgebra (p := p) (K := K) q)).injective p
  apply Subtype.ext
  apply Units.ext
  change (x.val : (commutantAlgebra (p := p) (K := K) q)) ^ p = 1
  have hn := radical_element_pow (p := p) q hq ((x.val : (commutantAlgebra (p := p) (K := K) q)) - 1) (principalUnits_sub_one (p := p) q hq x)
  have he := add_pow_char_of_commute p (Commute.one_left ((x.val : (commutantAlgebra (p := p) (K := K) q)) - 1))
  have hs : 1 + ((x.val : commutantAlgebra (p := p) q) - 1) = x.val := by abel
  simpa only [hs, one_pow, hn, add_zero] using he

private def principalOfRadical (q : K →ₗ[F] K) (hq : q 1 = 0) (j : radical (p := p) (K := K) q hq) : principalUnits (p := p) (K := K) q hq := by
  have hn : IsNilpotent (j.val : (commutantAlgebra (p := p) (K := K) q)) := ⟨p, radical_element_pow (p := p) q hq j.val j.property⟩
  let h := hn.isUnit_one_add
  refine ⟨h.unit, ?_⟩
  apply Units.ext
  change leadingHom (p := p) (K := K) q hq (h.unit : (commutantAlgebra (p := p) (K := K) q)) = 1
  rw [h.unit_spec, RingHom.map_add, RingHom.map_one]
  have hj : leadingHom (p := p) (K := K) q hq j.val = 0 := j.property
  rw [hj, add_zero]

private def principalRadicalEquiv (q : K →ₗ[F] K) (hq : q 1 = 0) : principalUnits (p := p) (K := K) q hq ≃ radical (p := p) (K := K) q hq where
  toFun x := ⟨(x.val : (commutantAlgebra (p := p) (K := K) q)) - 1, principalUnits_sub_one (p := p) q hq x⟩
  invFun := principalOfRadical (p := p) q hq
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    change ((principalOfRadical (p := p) q hq ⟨(x.val : (commutantAlgebra (p := p) (K := K) q)) - 1, _⟩).val : (commutantAlgebra (p := p) (K := K) q)) = (x.val : (commutantAlgebra (p := p) (K := K) q))
    simp only [principalOfRadical, IsUnit.unit_spec] <;> abel
  right_inv j := by
    apply Subtype.ext
    change ((principalOfRadical (p := p) q hq j).val : (commutantAlgebra (p := p) (K := K) q)) - 1 = j.val
    simp only [principalOfRadical, IsUnit.unit_spec] <;> abel

private theorem leading_coordinates (q : K →ₗ[F] K) (hq : q 1 = 0) (X : (commutantAlgebra (p := p) (K := K) q)) :
    leadingScalar (p := p) (K := K) q X = ((coordinatesEquiv (p := p) (K := K) q hq) ⟨X.val, X.property⟩).1.val
      (leadingIndex (p := p)) := by
  let z := (coordinatesEquiv (p := p) (K := K) q hq) ⟨X.val, X.property⟩
  have he := congrArg Subtype.val ((coordinatesEquiv (p := p) (K := K) q hq).symm_apply_apply
    (⟨X.val, X.property⟩ : {Y : Module.End F V // commutesOriginal q Y}))
  change toeplitzDegree (p := p) (K := K) z.1.val z.2 = X.val at he
  change leadingScalar (p := p) (K := K) q X = z.1.val (leadingIndex (p := p))
  unfold leadingScalar
  rw [← he, toeplitzDegree_constant]
  simp [coefficientZero, constantLinear]

private def radicalCoordinatesEquiv (q : K →ₗ[F] K) (hq : q 1 = 0) : radical (p := p) (K := K) q hq ≃
    {z : {c : Fin p → K // c 0 = 0} × (K →ₗ[F] K) //
      z.1.val (leadingIndex (p := p)) = 0} :=
  (coordinatesEquiv (p := p) (K := K) q hq).subtypeEquiv (by
    intro X
    change leadingScalar (p := p) (K := K) q (⟨X.val,X.property⟩ : (commutantAlgebra (p := p) (K := K) q)) = 0 ↔ _
    rw [leading_coordinates (p := p) q hq])

private def freeCoordinatesEquiv :
    {z : {c : Fin p → K // c 0 = 0} × (K →ₗ[F] K) //
      z.1.val (leadingIndex (p := p)) = 0} ≃
    (Fin (p-2) → K) × (K →ₗ[F] K) where
  toFun z := (fun i => z.val.1.val ⟨i.val+1, by have hp : 2 < p := Fact.out; omega⟩,
    z.val.2)
  invFun z := ⟨(⟨fun j => if h0 : j = 0 then 0
      else if ht : j = leadingIndex (p := p) then 0
      else z.1 ⟨j.val-1, by
        have hp : 2 < p := Fact.out
        have hj := j.isLt
        have h0' : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        have ht' : j.val ≠ p-1 := fun h => ht (Fin.ext h)
        omega⟩, by simp⟩, z.2), by
    have ht : leadingIndex (p := p) ≠ (0 : Fin p) := by
      intro h
      have hp : 2 < p := Fact.out
      have he := congrArg Fin.val h
      dsimp [leadingIndex] at he
      omega
    simp [ht]⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      funext j
      dsimp
      split_ifs with h0 ht
      · simpa only [h0] using z.val.1.property.symm
      · simpa only [ht] using z.property.symm
      · apply congrArg z.val.1.val
        apply Fin.ext
        have hj : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        simp only [Fin.val_mk]
        omega
    · rfl
  right_inv z := by
    apply Prod.ext
    · funext i
      have h0 : (⟨i.val+1, by have hp : 2 < p := Fact.out; omega⟩ : Fin p) ≠ 0 := by
        intro h
        have he := congrArg Fin.val h
        simp at he
      have ht : (⟨i.val+1, by have hp : 2 < p := Fact.out; omega⟩ : Fin p) ≠
          leadingIndex (p := p) := by
        intro h
        have hi := i.isLt
        have he := congrArg Fin.val h
        dsimp [leadingIndex] at he
        omega
      dsimp
      simp [h0, ht]
    · rfl

/-- The exact order counts all unrestricted prime-field-linear top maps. -/
theorem principalUnits_cardinality (q : K →ₗ[F] K) (hq : q 1 = 0) [Fintype K] {n : ℕ}
    (hK : Fintype.card K = p ^ n) :
    Nat.card (principalUnits (p := p) (K := K) q hq) = p ^ (n * (p-2) + n*n) := by
  have hdim : Module.finrank F K = n :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt
      ((FiniteField.pow_finrank_eq_card p K).trans hK)
  have htop : Nat.card (K →ₗ[F] K) = p^(n*n) := by
    rw [Module.natCard_eq_pow_finrank (K := F),
      Module.finrank_linearMap (R := F) (S := F), hdim,
      Nat.card_eq_fintype_card (α := F), ZMod.card]
  rw [Nat.card_congr (principalRadicalEquiv (p := p) q hq),
    Nat.card_congr (radicalCoordinatesEquiv (p := p) q hq),
    Nat.card_congr (freeCoordinatesEquiv (p := p) (K := K)),
    Nat.card_prod, Nat.card_fun, Nat.card_fin,
    Nat.card_eq_fintype_card (α := K), hK, htop, ← Nat.pow_mul, ← Nat.pow_add]

#print axioms principalUnits_commute
#print axioms principalUnits_pow
#print axioms principalUnits_cardinality

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadical
