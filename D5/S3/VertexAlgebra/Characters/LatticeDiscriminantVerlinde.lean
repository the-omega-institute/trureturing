/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite discriminant fusion convolution for the Weil S-kernel. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil

/-! # A finite discriminant Verlinde convolution

The lattice pairing identifies the discriminant group with its finite
character group.  Consequently the normalized triple product of the Weil
`S`-kernel is the addition law on discriminant labels.  This is the finite
modular-data identity; it does not assert a tensor-category construction.
-/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.VertexAlgebra.LatticeDiscriminantVerlinde
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open D5.S3.VertexAlgebra.LatticeDiscriminantWeil
open private pairing_add pairing_neg pairing_symm character_symm from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private pairing_neg_right orthogonality rho_mul_self rho_ne_zero from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil

noncomputable section

variable (D : LatticeData) [hD : Fact (gramReal D).PosDef]
local instance : Fintype (Discriminant D) := Fintype.ofFinite _
local instance : DecidableEq (Discriminant D) := Classical.decEq _

/-- The normalized finite triple convolution of the discriminant characters.

This is the pointed finite modular-data analogue of a Verlinde coefficient.
-/
def fusionCoefficient (a b c : Discriminant D) : ℂ :=
  (rho D)⁻¹ * (rho D)⁻¹ *
    ∑ x : Discriminant D,
      pairingCharacter D hD.out a x * pairingCharacter D hD.out b x *
        pairingCharacter D hD.out c (-x)

private lemma character_product (a b c x : Discriminant D) :
    pairingCharacter D hD.out a x * pairingCharacter D hD.out b x *
        pairingCharacter D hD.out c (-x) =
      pairingCharacter D hD.out (a + b - c) x := by
  change phase (pairing D a x) * phase (pairing D b x) *
    phase (pairing D c (-x)) = phase (pairing D (a + b - c) x)
  rw [pairing_neg_right D, ← phase.map_add_eq_mul, ← phase.map_add_eq_mul,
    sub_eq_add_neg, pairing_add D hD.out, pairing_add D hD.out,
    pairing_neg D hD.out]

private lemma character_sum (a b c : Discriminant D) :
    ∑ x : Discriminant D,
      pairingCharacter D hD.out a x * pairingCharacter D hD.out b x *
        pairingCharacter D hD.out c (-x) =
      if a + b = c then (Nat.card (Discriminant D) : ℂ) else 0 := by
  classical
  simp_rw [character_product D]
  have hs (d : Discriminant D) :
      (∑ x : Discriminant D, pairingCharacter D hD.out d x) =
        if d = 0 then (Nat.card (Discriminant D) : ℂ) else 0 := by
    calc
      (∑ x : Discriminant D, pairingCharacter D hD.out d x) =
          ∑ x : Discriminant D, pairingCharacter D hD.out x d := by
        apply Finset.sum_congr rfl
        intro x hx
        exact character_symm D hD.out d x
      _ = if d = 0 then (Nat.card (Discriminant D) : ℂ) else 0 :=
        orthogonality D d
  by_cases h : a + b = c
  · have hd : a + b - c = 0 := sub_eq_zero.mpr h
    rw [hs, if_pos hd, if_pos h]
  · have hd : a + b - c ≠ 0 := by
      intro hz
      apply h
      exact sub_eq_zero.mp hz
    rw [hs, if_neg hd, if_neg h]

/-- The normalized Weil `S` convolution is exactly the discriminant addition law. -/
theorem fusionCoefficient_eq_indicator (a b c : Discriminant D) :
    fusionCoefficient D a b c = if a + b = c then 1 else 0 := by
  classical
  unfold fusionCoefficient
  rw [character_sum D]
  by_cases h : a + b = c
  · simp only [if_pos h]
    have hr := rho_mul_self D
    rw [← hr]
    field_simp [rho_ne_zero D]
  · simp only [if_neg h]
    simp

end
end D5.S3.VertexAlgebra.LatticeDiscriminantVerlinde
