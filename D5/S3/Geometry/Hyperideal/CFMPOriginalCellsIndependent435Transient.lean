import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-! Exact affine independence check for the original twenty cells. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace

namespace CFMPOriginalCellsIndependent435Transient

theorem separated_flag {W : Type*} [AddCommGroup W] [Module ℝ W]
    (p₀ p₁ p₂ p₃ : W) (L R : W →ₗ[ℝ] ℝ)
    (hL₀ : L p₀ ≠ 0) (hL₁ : L p₁ = 0) (hL₂ : L p₂ = 0) (hL₃ : L p₃ = 0)
    (hR₁ : R p₁ ≠ 0) (hR₂ : R p₂ = 0) (hR₃ : R p₃ = 0) (h₂₃ : p₂ ≠ p₃) :
    AffineIndependent ℝ ![p₀,p₁,p₂,p₃] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have hv' : w 0 • p₀ + w 1 • p₁ + w 2 • p₂ + w 3 • p₃ = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hv
  have hl : w 0 * L p₀ = 0 := by
    simpa [map_add,map_smul,hL₁,hL₂,hL₃] using congrArg L hv'
  have h₀ : w 0 = 0 := (mul_eq_zero.mp hl).resolve_right hL₀
  have hr : w 1 * R p₁ = 0 := by
    simpa [map_add,map_smul,h₀,hR₂,hR₃] using congrArg R hv'
  have h₁ : w 1 = 0 := (mul_eq_zero.mp hr).resolve_right hR₁
  have hsum : w 2 + w 3 = 0 := by simpa [Fin.sum_univ_succ,h₀,h₁] using hw
  have h₃ : w 3 = -w 2 := by linarith
  have hs : w 2 • (p₂-p₃) = 0 := by simpa [h₀,h₁,h₃,smul_sub,sub_eq_add_neg] using hv'
  have h₂ : w 2 = 0 := (smul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr h₂₃)
  fin_cases i <;> simp [h₀,h₁,h₂,h₃]

theorem original_cells_independent (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (n : Fin 20) : AffineIndependent ℝ (vertices l n) := by
  fin_cases n
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 0 2,endpoint l 0 3]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 0 2) (endpoint l 0 3) (support l (Sum.inr 0)) (support l (Sum.inl 1))
    · exact (show (support l (Sum.inr 0)) barycenter < 0 by simpa [support,barycenter] using (shared_radial_body l hl).2.2.1 0).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.2.1
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.1; exact (show (support l (Sum.inl 1)) (endpoint l 0 1) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · intro he
      have hi : (⟨(0,2),by decide⟩ : EndpointLabel) = ⟨(0,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 1 0,endpoint l 1 2,endpoint l 1 3]
    apply separated_flag barycenter (endpoint l 1 0) (endpoint l 1 2) (endpoint l 1 3) (support l (Sum.inr 1)) (support l (Sum.inl 0))
    · exact (show (support l (Sum.inr 1)) barycenter < 0 by simpa [support,barycenter] using (shared_radial_body l hl).2.2.1 1).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.2.1
    · exact by have h := ((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.1; exact (show (support l (Sum.inl 0)) (endpoint l 1 0) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · intro he
      have hi : (⟨(1,2),by decide⟩ : EndpointLabel) = ⟨(1,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 2 0,endpoint l 2 1,endpoint l 2 3]
    apply separated_flag barycenter (endpoint l 2 0) (endpoint l 2 1) (endpoint l 2 3) (support l (Sum.inr 2)) (support l (Sum.inl 0))
    · exact (show (support l (Sum.inr 2)) barycenter < 0 by simpa [support,barycenter] using (shared_radial_body l hl).2.2.1 2).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.2.1
    · exact by have h := ((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.1; exact (show (support l (Sum.inl 0)) (endpoint l 2 0) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · intro he
      have hi : (⟨(2,1),by decide⟩ : EndpointLabel) = ⟨(2,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 3 0,endpoint l 3 1,endpoint l 3 2]
    apply separated_flag barycenter (endpoint l 3 0) (endpoint l 3 1) (endpoint l 3 2) (support l (Sum.inr 3)) (support l (Sum.inl 0))
    · exact (show (support l (Sum.inr 3)) barycenter < 0 by simpa [support,barycenter] using (shared_radial_body l hl).2.2.1 3).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.2.1
    · exact by have h := ((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.1; exact (show (support l (Sum.inl 0)) (endpoint l 3 0) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · intro he
      have hi : (⟨(3,1),by decide⟩ : EndpointLabel) = ⟨(3,2),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 1 2,endpoint l 2 1,endpoint l 2 3]
    apply separated_flag barycenter (endpoint l 1 2) (endpoint l 2 1) (endpoint l 2 3) (support l (Sum.inl 0)) (support l (Sum.inr 2))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.2.2 2 (by decide); exact (show (support l (Sum.inr 2)) (endpoint l 1 2) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(2,1),by decide⟩ : EndpointLabel) = ⟨(2,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 1 2,endpoint l 2 3,endpoint l 3 2]
    apply separated_flag barycenter (endpoint l 1 2) (endpoint l 2 3) (endpoint l 3 2) (support l (Sum.inl 0)) (support l (Sum.inl 1))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.1; exact (show (support l (Sum.inl 1)) (endpoint l 1 2) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · intro he
      have hi : (⟨(2,3),by decide⟩ : EndpointLabel) = ⟨(3,2),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 1 2,endpoint l 3 2,endpoint l 3 1]
    apply separated_flag barycenter (endpoint l 1 2) (endpoint l 3 2) (endpoint l 3 1) (support l (Sum.inl 0)) (support l (Sum.inr 3))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.2.2 3 (by decide); exact (show (support l (Sum.inr 3)) (endpoint l 1 2) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(3,2),by decide⟩ : EndpointLabel) = ⟨(3,1),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 1 2,endpoint l 3 1,endpoint l 1 3]
    apply separated_flag barycenter (endpoint l 1 2) (endpoint l 3 1) (endpoint l 1 3) (support l (Sum.inl 0)) (support l (Sum.inl 2))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.1; exact (show (support l (Sum.inl 2)) (endpoint l 1 2) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · intro he
      have hi : (⟨(3,1),by decide⟩ : EndpointLabel) = ⟨(1,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 2,endpoint l 2 0,endpoint l 2 3]
    apply separated_flag barycenter (endpoint l 0 2) (endpoint l 2 0) (endpoint l 2 3) (support l (Sum.inl 1)) (support l (Sum.inr 2))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.2.2 2 (by decide); exact (show (support l (Sum.inr 2)) (endpoint l 0 2) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(2,0),by decide⟩ : EndpointLabel) = ⟨(2,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 2,endpoint l 2 3,endpoint l 3 2]
    apply separated_flag barycenter (endpoint l 0 2) (endpoint l 2 3) (endpoint l 3 2) (support l (Sum.inl 1)) (support l (Sum.inl 0))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.1; exact (show (support l (Sum.inl 0)) (endpoint l 0 2) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · intro he
      have hi : (⟨(2,3),by decide⟩ : EndpointLabel) = ⟨(3,2),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 2,endpoint l 3 2,endpoint l 3 0]
    apply separated_flag barycenter (endpoint l 0 2) (endpoint l 3 2) (endpoint l 3 0) (support l (Sum.inl 1)) (support l (Sum.inr 3))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.2.2 3 (by decide); exact (show (support l (Sum.inr 3)) (endpoint l 0 2) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(3,2),by decide⟩ : EndpointLabel) = ⟨(3,0),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 2,endpoint l 3 0,endpoint l 0 3]
    apply separated_flag barycenter (endpoint l 0 2) (endpoint l 3 0) (endpoint l 0 3) (support l (Sum.inl 1)) (support l (Sum.inl 2))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.1; exact (show (support l (Sum.inl 2)) (endpoint l 0 2) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · intro he
      have hi : (⟨(3,0),by decide⟩ : EndpointLabel) = ⟨(0,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 1 0,endpoint l 1 3]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 1 0) (endpoint l 1 3) (support l (Sum.inl 2)) (support l (Sum.inr 1))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.2.2 1 (by decide); exact (show (support l (Sum.inr 1)) (endpoint l 0 1) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(1,0),by decide⟩ : EndpointLabel) = ⟨(1,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 1 3,endpoint l 3 1]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 1 3) (endpoint l 3 1) (support l (Sum.inl 2)) (support l (Sum.inl 0))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.1; exact (show (support l (Sum.inl 0)) (endpoint l 0 1) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · intro he
      have hi : (⟨(1,3),by decide⟩ : EndpointLabel) = ⟨(3,1),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 3 1,endpoint l 3 0]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 3 1) (endpoint l 3 0) (support l (Sum.inl 2)) (support l (Sum.inr 3))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.2.2 3 (by decide); exact (show (support l (Sum.inr 3)) (endpoint l 0 1) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(3,1),by decide⟩ : EndpointLabel) = ⟨(3,0),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 3 0,endpoint l 0 3]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 3 0) (endpoint l 0 3) (support l (Sum.inl 2)) (support l (Sum.inl 1))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.1; exact (show (support l (Sum.inl 1)) (endpoint l 0 1) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · intro he
      have hi : (⟨(3,0),by decide⟩ : EndpointLabel) = ⟨(0,3),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 1 0,endpoint l 1 2]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 1 0) (endpoint l 1 2) (support l (Sum.inl 3)) (support l (Sum.inr 1))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.2.2 1 (by decide); exact (show (support l (Sum.inr 1)) (endpoint l 0 1) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(1,0),by decide⟩ : EndpointLabel) = ⟨(1,2),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 1 2,endpoint l 2 1]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 1 2) (endpoint l 2 1) (support l (Sum.inl 3)) (support l (Sum.inl 0))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.1; exact (show (support l (Sum.inl 0)) (endpoint l 0 1) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
    · intro he
      have hi : (⟨(1,2),by decide⟩ : EndpointLabel) = ⟨(2,1),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 2 1,endpoint l 2 0]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 2 1) (endpoint l 2 0) (support l (Sum.inl 3)) (support l (Sum.inr 2))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.2.2 2 (by decide); exact (show (support l (Sum.inr 2)) (endpoint l 0 1) < 0 by simpa [support] using h).ne
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.2.1
    · exact by simpa [support] using ((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.2.1
    · intro he
      have hi : (⟨(2,1),by decide⟩ : EndpointLabel) = ⟨(2,0),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp
  · change AffineIndependent ℝ ![barycenter,endpoint l 0 1,endpoint l 2 0,endpoint l 0 2]
    apply separated_flag barycenter (endpoint l 0 1) (endpoint l 2 0) (endpoint l 0 2) (support l (Sum.inl 3)) (support l (Sum.inl 1))
    · norm_num [support,barycenter]
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 3 (by decide) (by decide))
    · exact by have h := ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.1; exact (show (support l (Sum.inl 1)) (endpoint l 0 1) < 0 by simpa [support] using neg_neg_of_pos h).ne
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · exact by simpa [support] using congrArg Neg.neg (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
    · intro he
      have hi : (⟨(2,0),by decide⟩ : EndpointLabel) = ⟨(0,2),by decide⟩ := (cut_body_polytope l hl).2.2.1 he
      have hp := congrArg Subtype.val hi
      norm_num at hp


def drop : V →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liftLinear : (Fin 3 → ℝ) →ₗ[ℝ] V where
  toFun u := ![u 0,u 1,u 2,-u 0-u 1-u 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

def liftAffine : (Fin 3 → ℝ) →ᵃ[ℝ] V where
  toFun u := ![u 0,u 1,u 2,1-u 0-u 1-u 2]
  linear := liftLinear
  map_vadd' u v := by
    ext i; fin_cases i <;> simp [liftLinear,vadd_eq_add] <;> ring

theorem lift_drop (x : V) (h : ∑ i, x i = 1) : liftAffine (drop x) = x := by
  have hs : x 0+x 1+x 2+x 3=1 := by simpa [Fin.sum_univ_four] using h
  ext i
  fin_cases i <;> simp [liftAffine,drop]
  linarith

theorem vertex_sum_one (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (j : Fin 4) : ∑ i, vertices l n j i = 1 := by
  fin_cases n <;> fin_cases j
  all_goals first
    | exact (shared_radial_body l hl).2.1.1.2
    | exact ((cut_body_polytope l hl).2.2.2 _ _ (by decide)).1.1.2

theorem chart_cells_independent (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) : AffineIndependent ℝ (fun j => drop (vertices l n j)) := by
  apply AffineIndependent.of_comp liftAffine
  have he : liftAffine ∘ (fun j => drop (vertices l n j)) = vertices l n := by
    funext j
    exact lift_drop _ (vertex_sum_one l hl n j)
  rw [he]
  exact original_cells_independent l hl n

def edgeMatrix (l : Fin 6 → ℝ) (n : Fin 20) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => drop (vertices l n j.succ) i - drop (vertices l n 0) i

theorem edgeMatrix_det_ne_zero (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) : (edgeMatrix l n).det ≠ 0 := by
  have hi := (affineIndependent_iff_linearIndependent_vsub ℝ
    (fun j => drop (vertices l n j)) (0 : Fin 4)).mp (chart_cells_independent l hl n)
  let e : Fin 3 ↪ {j : Fin 4 // j ≠ 0} :=
    ⟨fun j => ⟨j.succ,Fin.succ_ne_zero j⟩,
      fun i j h => Fin.succ_injective 3 (congrArg Subtype.val h)⟩
  have hc : LinearIndependent ℝ (edgeMatrix l n).col := by
    change LinearIndependent ℝ (fun j : Fin 3 =>
      drop (vertices l n j.succ) - drop (vertices l n 0))
    exact hi.comp e e.injective
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_col_iff.mp hc)

end CFMPOriginalCellsIndependent435Transient
