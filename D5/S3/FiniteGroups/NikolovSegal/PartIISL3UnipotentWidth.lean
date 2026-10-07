/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentWidthGeometry

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! The actual all-field alternating upper/lower 25-factor SL3 decomposition,
a concrete rank-two version of Part II Theorem 6.1. Native SL2 diagonal
decomposition is embedded twice; actual pivot elimination supplies the rest. -/
namespace NikolovSegal.PartIISL3UnipotentWidth
open NikolovSegal.PartIIA2Orbital NikolovSegal.PartIISL3UnipotentSylow
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

/-- The two native SL2 diagonal blocks and one actual upper chart account
for every upper-triangular SL3 matrix. -/
theorem triangular_factor (A : SL(3,F))
    (ht : ∀ i j : Fin 3, j < i → A i j = 0) :
    ∃ (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) (v : SL(3,F)),
      v ∈ upperUnipotent ∧ block01 (diag2 a ha) * block12 (diag2 b hb) * v = A := by
  have h10 := ht 1 0 (by decide)
  have h20 := ht 2 0 (by decide)
  have h21 := ht 2 1 (by decide)
  have hp : A 0 0 * A 1 1 * A 2 2 = 1 := by
    have hd := A.property
    rw [Matrix.det_fin_three] at hd
    simpa [h10,h20,h21] using hd
  have ha : A 0 0 ≠ 0 := by
    intro h
    rw [h,zero_mul,zero_mul] at hp
    exact zero_ne_one hp
  have h11 : A 1 1 ≠ 0 := by
    intro h
    rw [h,mul_zero,zero_mul] at hp
    exact zero_ne_one hp
  have hb : A 0 0 * A 1 1 ≠ 0 := mul_ne_zero ha h11
  let v := upper3 (A 0 1/A 0 0) (A 1 2/A 1 1) (A 0 2/A 0 0)
  refine ⟨A 0 0,A 0 0*A 1 1,ha,hb,v,⟨_,_,_,rfl⟩,?_⟩
  apply Subtype.ext
  change (!![A 0 0,0,0;0,(A 0 0)⁻¹,0;0,0,1] : Matrix (Fin 3) (Fin 3) F) *
      !![1,0,0;0,A 0 0*A 1 1,0;0,0,(A 0 0*A 1 1)⁻¹] *
      (upper3 (A 0 1/A 0 0) (A 1 2/A 1 1) (A 0 2/A 0 0)).val = A.val
  have hlast : (A 0 0*A 1 1)⁻¹ = A 2 2 := (inv_eq_of_mul_eq_one_right hp)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply,Fin.sum_univ_succ,upper3,h10,h20,h21,
    hlast,ha]
  all_goals field_simp

/-- Direct consumption of Mathlib's diagonal decomposition through the
genuine upper-left SL2 monoid embedding. -/
theorem diagonal01_factor (a : F) (ha : a ≠ 0) :
    block01 (diag2 a ha) = upper3 a 0 0 * lower3 (-a⁻¹) 0 0 *
      upper3 a 0 0 * upper3 (-1) 0 0 * lower3 1 0 0 * upper3 (-1) 0 0 := by
  have h := congrArg (block01 (F := F)) (Matrix.diag2_decompose a ha)
  simpa only [map_mul,block01_upper,block01_lower] using h

/-- The same existing native identity through the genuine lower-right block. -/
theorem diagonal12_factor (b : F) (hb : b ≠ 0) :
    block12 (diag2 b hb) = upper3 0 b 0 * lower3 0 (-b⁻¹) 0 *
      upper3 0 b 0 * upper3 0 (-1) 0 * lower3 0 1 0 * upper3 0 (-1) 0 := by
  have h := congrArg (block12 (F := F)) (Matrix.diag2_decompose b hb)
  simpa only [map_mul,block12_upper,block12_lower] using h

/-- Concrete rank-two Part II Theorem 6.1: all fields, with exactly 25
ordered alternating factors and literal actual upper/lower subgroups. -/
theorem alternating_unipotent_25 (g : SL(3,F)) :
    ∃ u : Fin 25 → SL(3,F),
      (∀ j, if Even j.val then u j ∈ upperUnipotent else u j ∈ lowerUnipotent) ∧
      orderedProduct u = g := by
  classical
  obtain ⟨v₀,v₁,v₂,v₃,h₀,h₁,h₂,h₃,ht⟩ := eliminate_to_upper g
  obtain ⟨a,b,ha,hb,v,hv,heq⟩ := triangular_factor _ ht
  have hback : v₀⁻¹*v₁⁻¹*v₂⁻¹*v₃⁻¹ *
      (block01 (diag2 a ha)*block12 (diag2 b hb)*v) = g := by
    rw [heq]
    simp [mul_assoc]
  let u : Fin 25 → SL(3,F) := ![
    v₀⁻¹,v₁⁻¹,v₂⁻¹,v₃⁻¹,
    upper3 a 0 0,lower3 (-a⁻¹) 0 0,upper3 a 0 0,1,
    upper3 (-1) 0 0,lower3 1 0 0,upper3 (-1) 0 0,1,
    upper3 0 b 0,lower3 0 (-b⁻¹) 0,upper3 0 b 0,1,
    upper3 0 (-1) 0,lower3 0 1 0,upper3 0 (-1) 0,1,
    v,1,1,1,1]
  refine ⟨u,?_,?_⟩
  · intro j
    fin_cases j
    all_goals norm_num [u,Nat.even_iff]
    all_goals first
      | exact h₀
      | exact h₁
      | exact h₂
      | exact h₃
      | exact upperUnipotent.inv_mem h₀
      | exact lowerUnipotent.inv_mem h₁
      | exact upperUnipotent.inv_mem h₂
      | exact lowerUnipotent.inv_mem h₃
      | exact lower3_mem _ _ _
      | exact upperUnipotent.one_mem
      | exact lowerUnipotent.one_mem
      | exact hv
  · have hf := hback
    rw [diagonal01_factor,diagonal12_factor] at hf
    simpa [u,orderedProduct,List.ofFn_succ,mul_assoc] using hf

end NikolovSegal.PartIISL3UnipotentWidth
