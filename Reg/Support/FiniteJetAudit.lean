import D5.S3.FiniteGroups.GroupAlgebra.FiniteJetOrbits
import Reg.Support.UniverseSingleReadout
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Field.ULift

/-! Source-faithful dependent-family audit evidence for finite original jets. -/

set_option autoImplicit false
noncomputable section
open _root_.D5.S3.FiniteGroups.GroupAlgebra
open FiniteJetCoefficients FiniteJetClassification FiniteJetOrbits
namespace Reg.Support.FiniteJetAudit
universe u

structure Data where
  p : ℕ
  [prime : Fact p.Prime]
  K : Type u
  [field : Field K]
  [finite : Fintype K]
  [algebra : Algebra (ZMod p) K]
  n : ℕ
attribute [instance] Data.prime Data.field Data.finite Data.algebra

structure SizedData extends Data.{u} where
  hn : 1 ≤ n
  hK : Fintype.card K = p ^ n

structure OddData extends Data.{u} where
  [odd : Fact (2 < p)]
attribute [instance] OddData.odd

structure CountData extends SizedData.{u} where
  [odd : Fact (2 < p)]
attribute [instance] CountData.odd

instance testPrime : Fact (Nat.Prime 3) := ⟨by decide⟩
instance testOdd : Fact (2 < 3) := ⟨by decide⟩
abbrev Nine := ULift.{u} (GaloisField 3 2)
instance : Fintype Nine.{u} := Fintype.ofFinite _
theorem nine_card : Fintype.card Nine.{u} = 3 ^ 2 := by
  rw [← Nat.card_eq_fintype_card]
  simpa only [Nine, Nat.card_ulift] using GaloisField.card 3 2 (by decide)

abbrev nine : Data.{u} := ⟨3, Nine, 2⟩
abbrev nineSized : SizedData.{u} := ⟨nine, by decide, nine_card⟩
abbrev nineOdd : OddData.{u} where
  toData := nine
  odd := ⟨by decide⟩
abbrev nineCount : CountData.{u} where
  toSizedData := nineSized
  odd := ⟨by decide⟩
abbrev threeCount : CountData.{u} :=
  ⟨⟨⟨3, ULift.{u} (ZMod 3), 1⟩, by decide, by simp⟩⟩

theorem tuples_ne : (0 : Fin (2 - 1) → Nine.{u}) ≠ 1 := by
  intro h
  exact zero_ne_one (congrFun h 0)

theorem coefficient_values_ne :
    ∃ x : Nine.{u}, (coefficientMap (p := 3) 2 (1 : Fin (2-1) → Nine)).val x ≠
      (coefficientMap (p := 3) 2 (0 : Fin (2-1) → Nine)).val x := by
  by_contra h
  push Not at h
  have he : coefficientMap (p := 3) 2 (1 : Fin (2-1) → Nine.{u}) = coefficientMap 2 0 := by
    apply Subtype.ext
    exact LinearMap.ext h
  exact tuples_ne ((coefficientMap_bijective (by decide) nine_card).injective he).symm
end Reg.Support.FiniteJetAudit
