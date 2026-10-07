/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3UnipotentGeometry
import D5.S3.FiniteGroups.NikolovSegal.PartIIA2RootGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! Actual PSL3 central-root geometry toward Nikolov--Segal Part II
Inn D Phi Gamma normalization. The accepted literal quotient/U equivalence
transports the computed centre, without a bare-automorphism lift. -/
namespace NikolovSegal.PartIIPSL3RootGeometry
open PartIIPSL3Unipotent PartIISL3UnipotentSylow PartIIA2Orbital PartIIA2RootGeometry
open PartIIA2RootNormalization Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev pi : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (Subgroup.center _)

/-- Literal quotient images of the actual positive root subgroups. -/
def projectivePositiveRoot (r : Fin 3) : Subgroup PSL(3,F) :=
  (positiveRoot (F := F) r).map pi

private theorem central_root_chart (t : F) :
    (a2Kernel% root) 2 t=upper3 0 0 t := by
  change transvection (show (0:Fin 3) ≠ 2 by decide) t=upper3 0 0 t
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]

private theorem mem_projectiveCentralRoot_iff (g : PSL(3,F)) :
    g ∈ projectivePositiveRoot (F := F) 2 ↔ ∃ t : F, projectiveUpper3 0 0 t=g := by
  constructor
  · rintro ⟨z,⟨t,rfl⟩,rfl⟩
    refine ⟨t,?_⟩
    change pi (upper3 0 0 t)=pi ((a2Kernel% root) 2 t)
    rw [central_root_chart]
  · rintro ⟨t,rfl⟩
    refine ⟨(a2Kernel% root) 2 t,⟨t,rfl⟩,?_⟩
    change pi ((a2Kernel% root) 2 t)=pi (upper3 0 0 t)
    rw [central_root_chart]

/-- The literal projective U centre is computed by the actual quotient
coordinate equivalence and the already proved matrix centre. Every field;
no central/root-image hypothesis or automorphism lift. -/
theorem mem_center_projective_U3_iff (z : projectiveUpperUnipotent (F := F)) :
    z ∈ Subgroup.center projectiveUpperUnipotent ↔
      ∃ t : F, z.val=projectiveUpper3 0 0 t := by
  let E := projectiveUpperEquiv (F := F)
  constructor
  · intro h
    have hw : E.symm z ∈ Subgroup.center (U3 (F := F)) :=
      ((Subgroup.centerCongr E.symm) ⟨z,h⟩).prop
    obtain ⟨t,ht⟩ := (mem_center_U3_iff (E.symm z)).mp hw
    have hh := congrArg Subtype.val (E.apply_symm_apply z)
    change pi ((E.symm z).val)=z.val at hh
    rw [ht] at hh
    exact ⟨t,hh.symm⟩
  · rintro ⟨t,ht⟩
    let w : U3 (F := F) := ⟨upper3 0 0 t,0,0,t,rfl⟩
    have hw : w ∈ Subgroup.center (U3 (F := F)) :=
      (mem_center_U3_iff w).mpr ⟨t,rfl⟩
    have hz : z=E w := Subtype.ext ht
    rw [hz]
    exact ((Subgroup.centerCongr E) ⟨w,hw⟩).prop

/-- Actual projective U preservation forces preservation of its literal
central positive root. Centre transport is through the true restricted
automorphism; no central root-image law is assumed. -/
theorem actual_projective_U_preserving_central_root_map [Fintype F]
    (beta : MulAut PSL(3,F))
    (hU : (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom=projectiveUpperUnipotent) :
    (projectivePositiveRoot (F := F) 2).map beta.toMonoidHom=projectivePositiveRoot 2 := by
  classical
  let V := projectiveUpperUnipotent (F := F)
  let Z := projectivePositiveRoot (F := F) 2
  let f : V ≃* V := (beta.subgroupMap V).trans (MulEquiv.subgroupCongr hU)
  have hle : Z.map beta.toMonoidHom ≤ Z := by
    rintro g ⟨z,hz,rfl⟩
    obtain ⟨t,ht⟩ := (mem_projectiveCentralRoot_iff z).mp hz
    have hzV : z ∈ V := (mem_projectiveUpperUnipotent z).mpr ⟨0,0,t,ht⟩
    have hzC : (⟨z,hzV⟩ : V) ∈ Subgroup.center V :=
      (mem_center_projective_U3_iff _).mpr ⟨t,ht.symm⟩
    have hbC : f ⟨z,hzV⟩ ∈ Subgroup.center V :=
      ((Subgroup.centerCongr f) ⟨⟨z,hzV⟩,hzC⟩).prop
    obtain ⟨s,hs⟩ := (mem_center_projective_U3_iff _).mp hbC
    change beta z=projectiveUpper3 0 0 s at hs
    exact (mem_projectiveCentralRoot_iff _).mpr ⟨s,hs.symm⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  exact (Nat.card_congr (Z.equivMapOfInjective beta.toMonoidHom beta.injective).toEquiv).le

/-- Every bare PSL3 automorphism over every finite field has ONE genuine
projective inner normalization preserving U and its computed central root.
The Sylow/quotient donors are consumed; no lift/cutoff/root-image premise. -/
theorem actual_bare_PSL3_U_central_root_normalization [Finite F]
    (beta : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F),
      (projectiveUpperUnipotent (F := F)).map (MulAut.conj g⁻¹*beta).toMonoidHom=
        projectiveUpperUnipotent ∧
      (projectivePositiveRoot (F := F) 2).map (MulAut.conj g⁻¹*beta).toMonoidHom=
        projectivePositiveRoot 2 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨g,_,hU⟩ := automorphism_projectiveUpper_normalize (ringChar F) beta
  exact ⟨g,hU,actual_projective_U_preserving_central_root_map _ hU⟩
end NikolovSegal.PartIIPSL3RootGeometry
