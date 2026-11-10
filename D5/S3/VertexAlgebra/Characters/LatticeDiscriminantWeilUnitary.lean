/- GID: D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeilUnitary
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeDiscriminantWeilUnitary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian unitarity of the finite discriminant Weil operators. -/

import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil

/-! Hermitian unitarity of the finite discriminant Weil operators. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.VertexAlgebra.LatticeDiscriminantWeil
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeDiscriminantTheta
open private qmodToReal from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private rho_mul_self rho_ne_zero orthogonality from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil

noncomputable section

section FiniteOperators
variable (D : LatticeData) [hD : Fact (gramReal D).PosDef]
local instance : Fintype (Discriminant D) := Fintype.ofFinite _
local instance : DecidableEq (Discriminant D) := Classical.decEq _

private lemma pairingCharacter_star (a b : Discriminant D) :
    starRingEnd ℂ (pairingCharacter D hD.out a (-b)) =
      pairingCharacter D hD.out a b := by
  rw [starRingEnd_apply, RCLike.star_def]
  rw [← (AddChar.map_neg_eq_conj (pairingCharacter D hD.out a) (-b))]
  simp

private lemma kernel_sum (b c : Discriminant D) :
    ∑ a : Discriminant D,
      pairingCharacter D hD.out a b * pairingCharacter D hD.out a (-c) =
      if b = c then (Nat.card (Discriminant D) : ℂ) else 0 := by
  classical
  have hsum :
      (∑ a : Discriminant D,
        pairingCharacter D hD.out a b * pairingCharacter D hD.out a (-c)) =
        ∑ a : Discriminant D, pairingCharacter D hD.out a (b - c) := by
    apply Finset.sum_congr rfl
    intro a ha
    simpa [sub_eq_add_neg] using
      (AddChar.map_add_eq_mul (pairingCharacter D hD.out a) b (-c)).symm
  rw [hsum, orthogonality D (b - c)]
  simp only [sub_eq_zero]

private lemma phase_star_mul (x : QmodZ) :
    starRingEnd ℂ (phase x) * phase x = 1 := by
  have hp : ‖phase x‖ = 1 := by
    unfold phase
    change ‖((AddCircle.toCircle_addChar (qmodToReal x) : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _
  rw [starRingEnd_apply, RCLike.star_def, RCLike.conj_mul, hp]
  norm_num

theorem weilS_preserves_inner (f g : Discriminant D → ℂ) :
    (∑ a : Discriminant D,
      starRingEnd ℂ (weilS D f a) * weilS D g a) =
      ∑ a : Discriminant D, starRingEnd ℂ (f a) * g a := by
  change (∑ a : Discriminant D,
      starRingEnd ℂ ((rho D)⁻¹ * ∑ b, pairingCharacter D hD.out a (-b) * f b) *
        ((rho D)⁻¹ * ∑ c, pairingCharacter D hD.out a (-c) * g c)) = _
  simp only [map_mul, map_sum]
  simp_rw [pairingCharacter_star]
  have hrstar : starRingEnd ℂ ((rho D)⁻¹) = (rho D)⁻¹ := by
    simp [rho]
  simp_rw [hrstar]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hfactor (b c : Discriminant D) :
      (∑ a : Discriminant D,
        ((rho D)⁻¹ * (pairingCharacter D hD.out a b * starRingEnd ℂ (f b))) *
          ((rho D)⁻¹ * (pairingCharacter D hD.out a (-c) * g c))) =
        (rho D)⁻¹ * (rho D)⁻¹ * (starRingEnd ℂ (f b) * g c) *
          ∑ a : Discriminant D,
            pairingCharacter D hD.out a b * pairingCharacter D hD.out a (-c) := by
    calc
      _ = ∑ a : Discriminant D,
          ((rho D)⁻¹ * (rho D)⁻¹ * (starRingEnd ℂ (f b) * g c)) *
            (pairingCharacter D hD.out a b * pairingCharacter D hD.out a (-c)) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  simp_rw [hfactor _ b]
  simp_rw [kernel_sum]
  simp [Finset.sum_ite_eq']
  rw [← Nat.card_eq_fintype_card, ← rho_mul_self D]
  field_simp [rho_ne_zero D]

theorem weilT_preserves_inner (f g : Discriminant D → ℂ) :
    (∑ a : Discriminant D,
      starRingEnd ℂ (weilT D f a) * weilT D g a) =
      ∑ a : Discriminant D, starRingEnd ℂ (f a) * g a := by
  change (∑ a : Discriminant D,
      starRingEnd ℂ (phase (quadraticClass D a) * f a) *
        (phase (quadraticClass D a) * g a)) = _
  simp only [map_mul]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (starRingEnd ℂ (phase (quadraticClass D a)) * starRingEnd ℂ (f a)) *
        (phase (quadraticClass D a) * g a) =
      (starRingEnd ℂ (phase (quadraticClass D a)) * phase (quadraticClass D a)) *
        (starRingEnd ℂ (f a) * g a) := by ring
    _ = _ := by rw [phase_star_mul]; simp

theorem weilST_preserves_inner (f g : Discriminant D → ℂ) :
    (∑ a : Discriminant D,
      starRingEnd ℂ ((weilS D) ((weilT D) f) a) *
        (weilS D) ((weilT D) g) a) =
      ∑ a : Discriminant D, starRingEnd ℂ (f a) * g a := by
  rw [weilS_preserves_inner]
  exact weilT_preserves_inner D f g

end FiniteOperators
end
end D5.S3.VertexAlgebra.LatticeDiscriminantWeil
