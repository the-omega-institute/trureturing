/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnUnipotentSylow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnitriangularCard
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.BigOperators.Associated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The accepted actual SLn upper-unitriangular subgroup is Sylow in every
finite field of defining characteristic. Native GL cardinality and native
Sylow pullback avoid a redundant SL group-order computation. -/
namespace NikolovSegal.SLnSylow
open Matrix
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F]

/-- The genuine GL order split into its upper-entry power and remaining factors. -/
theorem card_GL_factor (n : ℕ) :
    Nat.card (GeneralLinearGroup (Fin n) F) =
      (Fintype.card F)^(∑ i : Fin n, i.val) *
        ∏ i : Fin n, ((Fintype.card F)^(n-i.val)-1) := by
  rw [Matrix.card_GL_field]
  have hf : ∀ i : Fin n,
      (Fintype.card F)^n - (Fintype.card F)^i.val =
        (Fintype.card F)^i.val * ((Fintype.card F)^(n-i.val)-1) := by
    intro i
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add]
    have he : i.val+(n-i.val) = n := by omega
    rw [he]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The actual image of the accepted literal Uplus in GL. -/
abbrev GLupper (n : ℕ) (F : Type u) [Field F] :
    Subgroup (GeneralLinearGroup (Fin n) F) :=
  (Uplus n F).map SpecialLinearGroup.toGL

/-- Actual GL index of Uplus, derived from native GL order and proved entry bijection. -/
theorem GLupper_index (n : ℕ) :
    (GLupper n F).index = ∏ i : Fin n, ((Fintype.card F)^(n-i.val)-1) := by
  have h := (GLupper n F).card_mul_index
  rw [Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective,
    card_Uplus_sum, card_GL_factor] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Fintype.card_pos _) h

variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Defining-characteristic p-group recognition from the actual cardinality. -/
theorem Uplus_isPGroup (n : ℕ) : IsPGroup p (Uplus n F) := by
  obtain ⟨e,_,he⟩ := FiniteField.card F p
  apply IsPGroup.of_card (n := (e:ℕ)*(∑ i : Fin n, i.val))
  rw [card_Uplus_sum, he, ← pow_mul]

/-- Every remaining GL index factor is prime to the actual field characteristic. -/
theorem GLupper_index_not_dvd (n : ℕ) : ¬ p ∣ (GLupper n F).index := by
  rw [GLupper_index]
  apply (Fact.out : p.Prime).prime.not_dvd_finsetProd
  intro i _ h
  obtain ⟨e,_,he⟩ := FiniteField.card F p
  have hpq : p ∣ Fintype.card F := by
    rw [he]
    exact dvd_pow_self p e.ne_zero
  have hd : p ∣ (Fintype.card F)^(n-i.val) :=
    hpq.trans (dvd_pow_self (Fintype.card F) (by omega))
  have hd1 := Nat.dvd_sub hd h
  have hpos : 0 < (Fintype.card F)^(n-i.val) := pow_pos Fintype.card_pos _
  have he1 : (Fintype.card F)^(n-i.val) - ((Fintype.card F)^(n-i.val)-1) = 1 := by omega
  rw [he1] at hd1
  exact (Fact.out : p.Prime).not_dvd_one hd1

/-- A genuine Sylow with exactly the accepted literal SLn unitriangular carrier.
It is the native injective pullback of the actual GL-image Sylow. -/
def UplusSylow (n : ℕ) : Sylow p (SpecialLinearGroup (Fin n) F) :=
  let P := ((Uplus_isPGroup (F := F) p n).map SpecialLinearGroup.toGL).toSylow
    (GLupper_index_not_dvd (F := F) p n)
  P.comapOfInjective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
    ((Uplus n F).map_le_range SpecialLinearGroup.toGL)

/-- Literal underlying-subgroup equality, not an assumed Sylow recognition premise. -/
theorem UplusSylow_toSubgroup (n : ℕ) :
    (UplusSylow (F := F) p n).toSubgroup = Uplus n F := by
  change ((Uplus n F).map SpecialLinearGroup.toGL).comap SpecialLinearGroup.toGL = Uplus n F
  exact Subgroup.comap_map_eq_self_of_injective SpecialLinearGroup.toGL_injective _

/-- Every prime, every finite field of characteristic p and every rank, including0/1. -/
theorem exists_Uplus_sylow (n : ℕ) :
    ∃ P : Sylow p (SpecialLinearGroup (Fin n) F), P.toSubgroup = Uplus n F :=
  ⟨UplusSylow p n, UplusSylow_toSubgroup p n⟩

end NikolovSegal.SLnSylow
