/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Binary matrix units act equivariantly on the Fano flag gain. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodLift

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodMatrixAction

open HeawoodSwitching HeawoodLift Matrix
open scoped BigOperators
noncomputable section

private abbrev Vector := Fin 3 → F2
private abbrev NonzeroVector := {v : Vector // v ≠ 0}

private theorem coordinate_nonzero : ∀ p : Fin 7, coordinate p ≠ 0 := by decide +kernel

private def coordinates : Fin 7 ≃ NonzeroVector :=
  Equiv.ofBijective (fun p => ⟨coordinate p, coordinate_nonzero p⟩) (by
    constructor
    · intro p q h
      have hinj : Function.Injective coordinate := by decide +kernel
      exact hinj (congrArg Subtype.val h)
    · intro v
      have hall : ∀ x : Vector, x ≠ 0 → ∃ p : Fin 7, coordinate p = x := by decide +kernel
      obtain ⟨p, hp⟩ := hall v.val v.property
      exact ⟨p, Subtype.ext hp⟩)

private def pointAction (g : Matˣ) : NonzeroVector ≃ NonzeroVector where
  toFun v := ⟨(g : Mat) *ᵥ v.val, by
    intro h
    have hg := congrArg (fun x : Vector => (↑g⁻¹ : Mat) *ᵥ x) h
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at hg
    exact v.property hg⟩
  invFun v := ⟨(↑g⁻¹ : Mat) *ᵥ v.val, by
    intro h
    have hg := congrArg (fun x : Vector => (g : Mat) *ᵥ x) h
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec, mulVec_zero] at hg
    exact v.property hg⟩
  left_inv v := Subtype.ext (by
    change (↑g⁻¹ : Mat) *ᵥ ((g : Mat) *ᵥ v.val) = v.val
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec])
  right_inv v := Subtype.ext (by
    change (g : Mat) *ᵥ ((↑g⁻¹ : Mat) *ᵥ v.val) = v.val
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec])

private def lineAction (g : Matˣ) : NonzeroVector ≃ NonzeroVector where
  toFun v := ⟨v.val ᵥ* (↑g⁻¹ : Mat), by
    intro h
    have hg := congrArg (fun x : Vector => x ᵥ* (g : Mat)) h
    rw [vecMul_vecMul, Units.inv_mul, vecMul_one, zero_vecMul] at hg
    exact v.property hg⟩
  invFun v := ⟨v.val ᵥ* (g : Mat), by
    intro h
    have hg := congrArg (fun x : Vector => x ᵥ* (↑g⁻¹ : Mat)) h
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one, zero_vecMul] at hg
    exact v.property hg⟩
  left_inv v := Subtype.ext (by
    change (v.val ᵥ* (↑g⁻¹ : Mat)) ᵥ* (g : Mat) = v.val
    rw [vecMul_vecMul, Units.inv_mul, vecMul_one])
  right_inv v := Subtype.ext (by
    change (v.val ᵥ* (g : Mat)) ᵥ* (↑g⁻¹ : Mat) = v.val
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one])

private def onPoint (g : Matˣ) : Fin 7 ≃ Fin 7 :=
  (coordinates.trans (pointAction g)).trans coordinates.symm

private def onLine (g : Matˣ) : Fin 7 ≃ Fin 7 :=
  (coordinates.trans (lineAction g)).trans coordinates.symm

private theorem point_coordinates (g : Matˣ) (p : Fin 7) :
    coordinate (onPoint g p) = (g : Mat) *ᵥ coordinate p :=
  congrArg Subtype.val (coordinates.apply_symm_apply (pointAction g (coordinates p)))

private theorem line_coordinates (g : Matˣ) (l : Fin 7) :
    coordinate (onLine g l) = coordinate l ᵥ* (↑g⁻¹ : Mat) :=
  congrArg Subtype.val (coordinates.apply_symm_apply (lineAction g (coordinates l)))

private theorem pairing_preserved (g : Matˣ) (p l : Fin 7) :
    coordinate (onPoint g p) ⬝ᵥ coordinate (onLine g l) = coordinate p ⬝ᵥ coordinate l := by
  rw [point_coordinates, line_coordinates, dotProduct_comm,
    dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one, dotProduct_comm]

end
end D5.S3.Combinatorics.Graph.StarForming.HeawoodMatrixAction
