/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2RootGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2TorusAlignment
import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentSylow
import Mathlib.GroupTheory.Subgroup.Center
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace NikolovSegal.PartIIA2RootGeometry
open PartIIA2Orbital PartIISL3UnipotentSylow
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem upper3_injective {a b c A B C : F}
    (h : upper3 a b c = upper3 A B C) : a=A ∧ b=B ∧ c=C := by
  exact ⟨congrArg (fun g : SL(3,F) => g 0 1) h,
    congrArg (fun g : SL(3,F) => g 1 2) h,
    congrArg (fun g : SL(3,F) => g 0 2) h⟩

/-- The central height-two root is computed inside the actual U, not assumed. -/
theorem mem_center_U3_iff (z : upperUnipotent (F := F)) :
    z ∈ Subgroup.center upperUnipotent ↔ ∃ t : F, z.val = upper3 0 0 t := by
  obtain ⟨a,b,c,hz⟩ := z.prop
  constructor
  · intro h
    have h1 := Subgroup.mem_center_iff.mp h ⟨upper3 1 0 0,1,0,0,rfl⟩
    have h2 := Subgroup.mem_center_iff.mp h ⟨upper3 0 1 0,0,1,0,rfl⟩
    have he1 := congrArg (fun g : upperUnipotent (F := F) => g.val) h1
    have he2 := congrArg (fun g : upperUnipotent (F := F) => g.val) h2
    change upper3 1 0 0*z.val = z.val*upper3 1 0 0 at he1
    change upper3 0 1 0*z.val = z.val*upper3 0 1 0 at he2
    rw [← hz,(a2Kernel% upper3_mul),(a2Kernel% upper3_mul)] at he1 he2
    have hb : b=0 := by
      have hh := (upper3_injective he1).2.2
      simpa using hh
    have ha : a=0 := by
      have hh := (upper3_injective he2).2.2
      simpa using hh.symm
    exact ⟨c,by simpa only [ha,hb] using hz.symm⟩
  · rintro ⟨t,ht⟩
    apply Subgroup.mem_center_iff.mpr
    intro g
    obtain ⟨A,B,C,hg⟩ := g.prop
    apply Subtype.ext
    change g.val*z.val=z.val*g.val
    rw [ht,← hg,(a2Kernel% upper3_mul),(a2Kernel% upper3_mul)]
    congr 1 <;> ring

/-- The central positive root subgroup is characteristic inside actual U.
The centre is computed from the matrix equations above, and actual U
preservation supplies the coordinate transport. No central/root image oracle. -/
theorem actual_U_preserving_central_root_map [Fintype F]
    (beta : MulAut SL(3,F))
    (hU : upperUnipotent.map beta.toMonoidHom=upperUnipotent) :
    (PartIIA2RootNormalization.positiveRoot (F := F) 2).map beta.toMonoidHom=
      PartIIA2RootNormalization.positiveRoot 2 := by
  classical
  let Z := PartIIA2RootNormalization.positiveRoot (F := F) 2
  have hle : Z.map beta.toMonoidHom ≤ Z := by
    rintro g ⟨z,⟨t,rfl⟩,rfl⟩
    have hz : (a2Kernel% root) 2 t ∈ upperUnipotent := (a2Kernel% root_mem) 2 t
    have hzU : beta ((a2Kernel% root) 2 t) ∈ upperUnipotent := by
      rw [← hU]
      exact Subgroup.mem_map_of_mem beta.toMonoidHom hz
    have hzc : (⟨(a2Kernel% root) 2 t,hz⟩ : upperUnipotent) ∈
        Subgroup.center upperUnipotent := by
      apply (mem_center_U3_iff _).mpr
      refine ⟨t,?_⟩
      change Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 2 by decide) t=upper3 0 0 t
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upper3,Matrix.SpecialLinearGroup.transvection_coe]
    have hbc : (⟨beta ((a2Kernel% root) 2 t),hzU⟩ : upperUnipotent) ∈
        Subgroup.center upperUnipotent := by
      apply Subgroup.mem_center_iff.mpr
      intro v
      have hv : v.val ∈ upperUnipotent.map beta.toMonoidHom := by rw [hU]; exact v.prop
      obtain ⟨w,hw,hv⟩ := hv
      have hh := congrArg (fun z : upperUnipotent (F := F) => z.val)
        (Subgroup.mem_center_iff.mp hzc ⟨w,hw⟩)
      change w*((a2Kernel% root) 2 t)=((a2Kernel% root) 2 t)*w at hh
      change beta w=v.val at hv
      apply Subtype.ext
      change v.val*beta ((a2Kernel% root) 2 t)=beta ((a2Kernel% root) 2 t)*v.val
      rw [← hv,← map_mul,← map_mul,hh]
    obtain ⟨s,hs⟩ := (mem_center_U3_iff _).mp hbc
    refine ⟨s,?_⟩
    change (a2Kernel% root) 2 s=beta ((a2Kernel% root) 2 t)
    change beta ((a2Kernel% root) 2 t)=upper3 0 0 s at hs
    rw [hs]
    change Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 2 by decide) s=upper3 0 0 s
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,Matrix.SpecialLinearGroup.transvection_coe]
  apply Subgroup.eq_of_le_of_card_ge hle
  exact (Nat.card_congr (Z.equivMapOfInjective beta.toMonoidHom beta.injective).toEquiv).le
/-- Consumed actual geometry for EVERY bare SL3 automorphism: one inner
normalization simultaneously preserves U, T, and the computed central root.
No subgroup-image/semilinearity/coverage hypothesis is introduced. -/
theorem actual_bare_SL3_U_T_central_root_normalization [Fintype F] [DecidableEq F]
    (beta : MulAut SL(3,F)) :
    ∃ g : SL(3,F),
      upperUnipotent.map (MulAut.conj g⁻¹*beta).toMonoidHom=upperUnipotent ∧
      PartIIA2TorusAlignment.diagonalTorus.map (MulAut.conj g⁻¹*beta).toMonoidHom=
        PartIIA2TorusAlignment.diagonalTorus ∧
      (PartIIA2RootNormalization.positiveRoot (F := F) 2).map
        (MulAut.conj g⁻¹*beta).toMonoidHom=PartIIA2RootNormalization.positiveRoot 2 := by
  obtain ⟨g,hU,hT⟩ := PartIIA2TorusAlignment.actual_bare_SL3_U_torus_normalization beta
  exact ⟨g,hU,hT,actual_U_preserving_central_root_map _ hU⟩
end NikolovSegal.PartIIA2RootGeometry
