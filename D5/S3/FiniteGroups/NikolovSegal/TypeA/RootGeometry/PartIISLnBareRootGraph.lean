/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareRootGraph
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareRootGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnBareRootField
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootGraph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- A nontrivial actual root commutator detects endpoint composition. -/
theorem root_commutator_compose (a b c : PositiveIndex n) (t u w : F)
    (ht : t ≠ 0) (hu : u ≠ 0) (hw : w ≠ 0)
    (hc : root a t*root b u*(root a t)⁻¹*(root b u)⁻¹ = root c w) :
    RootCompose a b c := by
  classical
  by_cases h1 : a.val.2=b.val.1
  · let d : PositiveIndex n := ⟨(a.val.1,b.val.2),a.property.trans (h1.symm ▸ b.property)⟩
    have he : root a t*root b u*(root a t)⁻¹*(root b u)⁻¹ = root d (t*u) := by
      cases a with
      | mk ap ha =>
        rcases ap with ⟨i,j⟩
        cases b with
        | mk bp hb =>
          rcases bp with ⟨k,l⟩
          change j=k at h1
          subst k
          exact transvection_commutator_chain ha hb t u
    have hd : d=c := root_nonzero_eq_index d c _ _ (mul_ne_zero ht hu) (he.symm.trans hc)
    exact Or.inl ⟨h1,congrArg (fun r => r.val.1) hd.symm,congrArg (fun r => r.val.2) hd.symm⟩
  · by_cases h2 : b.val.2=a.val.1
    · let d : PositiveIndex n := ⟨(b.val.1,a.val.2),b.property.trans (h2.symm ▸ a.property)⟩
      have he : root b u*root a t*(root b u)⁻¹*(root a t)⁻¹ = root d (u*t) := by
        cases b with
        | mk bp hb =>
          rcases bp with ⟨i,j⟩
          cases a with
          | mk ap ha =>
            rcases ap with ⟨k,l⟩
            change j=k at h2
            subst k
            exact transvection_commutator_chain hb ha u t
      have hi : root a t*root b u*(root a t)⁻¹*(root b u)⁻¹ =
          (root b u*root a t*(root b u)⁻¹*(root a t)⁻¹)⁻¹ := by
        simp only [_root_.mul_inv_rev,inv_inv,mul_assoc]
      have he' : root d (-(u*t))=root c w := by
        rw [hi,he] at hc
        change (SpecialLinearGroup.transvection (ne_of_lt d.property) (u*t))⁻¹=root c w at hc
        rw [SpecialLinearGroup.transvection_inv] at hc
        exact hc
      have hd : d=c := root_nonzero_eq_index d c _ _ (neg_ne_zero.mpr (mul_ne_zero hu ht)) he'
      exact Or.inr ⟨h2,congrArg (fun r => r.val.1) hd.symm,congrArg (fun r => r.val.2) hd.symm⟩
    · have he := roots_commute_of_not_glued a b h1 h2 t u
      have hz : root c w=root c 0 := by
        rw [he] at hc
        simpa [root,mul_assoc] using hc.symm
      exact (hw (root_injective c hz)).elim

variable [Fintype F]
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment

/-- The actual bare positive-root permutation is identity or reflection;
ONE common field automorphism is retained. -/
theorem sl_bare_root_graph_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F)
    (alpha : MulAut (SpecialLinearGroup (Fin n) F)) :
    ∃ c : SpecialLinearGroup (Fin n) F, ∃ chi : PositiveIndex n → Fˣ,
      ∃ phi : RingAut F, ∃ eps : Bool,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (diagonalTorus n F).map beta.toMonoidHom = diagonalTorus n F ∧
      ∀ r t, beta (root r t) = root (if eps then reflectRoot r else r) ((chi r:F)*phi t) := by
  classical
  obtain ⟨c,sigma,chi,phi,hU,hT,hs,hb⟩ := sl_bare_root_field_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (root r t)=root (sigma r) ((chi r:F)*phi t) at hb
  have hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      RootCompose (sigma ⟨(i,j),hij⟩) (sigma ⟨(j,k),hjk⟩) (sigma ⟨(i,k),hij.trans hjk⟩) := by
    intro i j k hij hjk
    have he0 := transvection_commutator_chain hij hjk (1:F) 1
    change root ⟨(i,j),hij⟩ 1*root ⟨(j,k),hjk⟩ 1*(root ⟨(i,j),hij⟩ 1)⁻¹*
      (root ⟨(j,k),hjk⟩ 1)⁻¹=root ⟨(i,k),hij.trans hjk⟩ (1*1) at he0
    have he := congrArg beta he0
    simp only [map_mul,map_inv,hb,map_one,mul_one,one_mul] at he
    exact root_commutator_compose _ _ _ _ _ _ (chi _).ne_zero (chi _).ne_zero (chi _).ne_zero he
  rcases root_permutation_identity_or_reflection hn sigma hinc with hid|hrev
  · refine ⟨c,chi,phi,false,hU,hT,?_⟩
    simpa only [Bool.false_eq_true,ite_false,hid] using hb
  · refine ⟨c,chi,phi,true,hU,hT,?_⟩
    simpa only [ite_true,hrev] using hb
end NikolovSegal.SLnRootAction

namespace NikolovSegal.PSLnRootAction
open Matrix
open NikolovSegal.SLnRootAction NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}

/-- Intrinsic quotient graph/field root action; no automorphism lift. -/
theorem psl_bare_root_graph_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F)
    (alpha : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ c : ProjectiveSpecialLinearGroup (Fin n) F, ∃ chi : PositiveIndex n → Fˣ,
      ∃ phi : RingAut F, ∃ eps : Bool,
      let beta := MulAut.conj c * alpha
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom = projectiveDiagonalTorus n F ∧
      ∀ r t, beta (projectiveRootValue r t) =
        projectiveRootValue (if eps then reflectRoot r else r) ((chi r:F)*phi t) := by
  classical
  obtain ⟨c,sigma,chi,phi,hU,hT,hs,hb⟩ := psl_bare_root_field_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (projectiveRootValue r t)=projectiveRootValue (sigma r) ((chi r:F)*phi t) at hb
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  have hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      RootCompose (sigma ⟨(i,j),hij⟩) (sigma ⟨(j,k),hjk⟩) (sigma ⟨(i,k),hij.trans hjk⟩) := by
    intro i j k hij hjk
    have he0 := congrArg q (transvection_commutator_chain hij hjk (1:F) 1)
    have he1 : projectiveRootValue ⟨(i,j),hij⟩ (1:F)*projectiveRootValue ⟨(j,k),hjk⟩ 1*
        (projectiveRootValue ⟨(i,j),hij⟩ 1)⁻¹*(projectiveRootValue ⟨(j,k),hjk⟩ 1)⁻¹ =
        projectiveRootValue ⟨(i,k),hij.trans hjk⟩ 1 := by
      simpa [q,projectiveRootValue,root,map_mul,map_inv] using he0
    have he := congrArg beta he1
    simp only [map_mul,map_inv,hb,map_one,mul_one] at he
    let A := root (sigma ⟨(i,j),hij⟩) (chi ⟨(i,j),hij⟩:F)
    let B := root (sigma ⟨(j,k),hjk⟩) (chi ⟨(j,k),hjk⟩:F)
    have hx : A*B*A⁻¹*B⁻¹ ∈ Uplus n F := (Uplus n F).mul_mem
      ((Uplus n F).mul_mem ((Uplus n F).mul_mem (root_mem_Uplus _ _) (root_mem_Uplus _ _))
        ((Uplus n F).inv_mem (root_mem_Uplus _ _))) ((Uplus n F).inv_mem (root_mem_Uplus _ _))
    have hc := quotient_injective_on_U _ _ hx (root_mem_Uplus _ _)
      (by simpa only [projectiveRootValue,map_mul,map_inv] using he)
    exact root_commutator_compose _ _ _ _ _ _ (chi _).ne_zero (chi _).ne_zero (chi _).ne_zero hc
  rcases root_permutation_identity_or_reflection hn sigma hinc with hid|hrev
  · refine ⟨c,chi,phi,false,hU,hT,?_⟩
    simpa only [Bool.false_eq_true,ite_false,hid] using hb
  · refine ⟨c,chi,phi,true,hU,hT,?_⟩
    simpa only [ite_true,hrev] using hb
end NikolovSegal.PSLnRootAction
