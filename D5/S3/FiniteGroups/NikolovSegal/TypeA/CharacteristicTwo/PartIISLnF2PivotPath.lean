/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2PivotPath
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2PivotPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2SimplePivots
import Mathlib.Algebra.Ring.Commute
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.SLnF2Residual
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- The actual second superdiagonal of a product of strict upper matrices. -/
theorem strict_mul_second (N M : Matrix (Fin n) (Fin n) F)
    (hN : ∀ a b, b.val ≤ a.val → N a b=0)
    (hM : ∀ a b, b.val ≤ a.val → M a b=0)
    (i : ℕ) (hi : i+2<n) :
    (N*M) ⟨i,by omega⟩ ⟨i+2,hi⟩ =
      N ⟨i,by omega⟩ ⟨i+1,by omega⟩ * M ⟨i+1,by omega⟩ ⟨i+2,hi⟩ := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single (⟨i+1,by omega⟩ : Fin n)
  · intro k _ hk
    by_cases hle : k.val ≤ i
    · rw [hN _ _ hle,zero_mul]
    · have hge : i+2 ≤ k.val := by
        have hne : k.val ≠ i+1 := fun h => hk (Fin.ext h)
        omega
      rw [hM _ _ hge,mul_zero]
  · simp

/-- Genuine commutation forces the two adjacent simple coordinates to have
zero wedge; this is a literal matrix-entry computation. -/
theorem commuting_simple_wedge (g h : G) (hg : g ∈ Uplus n F)
    (hh : h ∈ Uplus n F) (hc : g*h=h*g) (i : ℕ) (hi : i+1<n-1) :
    simpleEntry g ⟨i,by omega⟩ * simpleEntry h ⟨i+1,hi⟩ =
      simpleEntry h ⟨i,by omega⟩ * simpleEntry g ⟨i+1,hi⟩ := by
  have hv : Commute g.val h.val := congrArg Subtype.val hc
  have hd : Commute (deviation g) (deviation h) :=
    (hv.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) F =>
    M ⟨i,by omega⟩ ⟨i+2,by omega⟩) hd.eq
  rw [strict_mul_second _ _ (deviation_zero_le g hg) (deviation_zero_le h hh),
    strict_mul_second _ _ (deviation_zero_le h hh) (deviation_zero_le g hg)] at he
  simpa [deviation,Matrix.sub_apply,Matrix.one_apply,simpleEntry,simpleRoot,
    Nat.add_assoc,show i ≠ i+1 by omega,show i+1 ≠ i+2 by omega] using he

/-- Nonadjacent actual simple root elements commute. -/
theorem simple_roots_commute (i j : Fin (n-1))
    (hij : i.val+1 ≠ j.val) (hji : j.val+1 ≠ i.val) :
    root (simpleRoot i) (1:F)*root (simpleRoot j) 1 =
      root (simpleRoot j) 1*root (simpleRoot i) 1 := by
  apply transvections_commute
  · intro he; apply hij; exact congrArg Fin.val he
  · intro he; apply hji; exact congrArg Fin.val he

/-- The pivot permutation derived from a bare U-normalized automorphism is
identity or reflection. No root-image or path-preservation premise is used. -/
theorem normalized_pivots_identity_or_reflection (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F) :
    ∃ sigma : Equiv.Perm (Fin (n-1)),
      ((∀ i, sigma i=i) ∨ (∀ i, sigma i=i.rev)) ∧ ∀ i,
      simpleEntry (alpha (root (simpleRoot i) 1)) (sigma i)=1 ∧
      ∀ j, j ≠ sigma i → simpleEntry (alpha (root (simpleRoot i) 1)) j=0 := by
  obtain ⟨sigma,hp⟩ := normalized_simple_pivot_permutation hF hn alpha hU
  have hm : ∀ i, alpha (root (simpleRoot i) (1:F)) ∈ Uplus n F := by
    intro i; rw [← hU]; exact Subgroup.mem_map_of_mem _ (root_mem_Uplus _ _)
  have hstep : ∀ (i : ℕ) (hi : i+1<n-1),
      (sigma.symm ⟨i+1,hi⟩).val=(sigma.symm ⟨i,by omega⟩).val+1 ∨
      (sigma.symm ⟨i,by omega⟩).val=(sigma.symm ⟨i+1,hi⟩).val+1 := by
    intro i hi
    by_contra hno
    have h1 : (sigma.symm ⟨i,by omega⟩).val+1 ≠ (sigma.symm ⟨i+1,hi⟩).val := by
      intro h; exact hno (Or.inl h.symm)
    have h2 : (sigma.symm ⟨i+1,hi⟩).val+1 ≠ (sigma.symm ⟨i,by omega⟩).val := by
      intro h; exact hno (Or.inr h.symm)
    have hc := congrArg alpha (simple_roots_commute (F := F) _ _ h1 h2)
    simp only [map_mul] at hc
    have he := commuting_simple_wedge _ _ (hm _) (hm _) hc i hi
    have ha := hp (sigma.symm ⟨i,by omega⟩)
    have hb := hp (sigma.symm ⟨i+1,hi⟩)
    simp only [sigma.apply_symm_apply] at ha hb
    have hn01 : (⟨i,by omega⟩ : Fin (n-1)) ≠ ⟨i+1,hi⟩ := by
      intro h; have hv:=congrArg Fin.val h; change i=i+1 at hv; omega
    rw [ha.1,hb.1,hb.2 _ hn01,ha.2 _ hn01.symm] at he
    simp at he
  rcases path_embedding_identity_or_rev (by omega : 2 ≤ n-1) sigma.symm sigma.symm.injective hstep with hid|hrev
  · refine ⟨sigma,Or.inl ?_,hp⟩
    intro i
    have h := hid (sigma i)
    simpa only [sigma.symm_apply_apply] using h.symm
  · refine ⟨sigma,Or.inr ?_,hp⟩
    intro i
    have h := hrev (sigma i)
    simp only [sigma.symm_apply_apply] at h
    simpa only [Fin.rev_rev] using (congrArg Fin.rev h).symm

end NikolovSegal.SLnF2Bare
