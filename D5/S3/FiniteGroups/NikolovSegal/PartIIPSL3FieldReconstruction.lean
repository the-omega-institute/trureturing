/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3FieldReconstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3FieldReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3RootSeparation
import D5.S3.FiniteGroups.NikolovSegal.PartIIA2BareOrbital

set_option autoImplicit false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "psl3Field%" id:ident : term => do
  let env ← getEnv
  let owner := if id.getId == `positive_commutator then "PartIIA2RootNormalization" else "PartIIPSL3RootSeparation"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ owner
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique proved projective field kernel {id} not found"
namespace NikolovSegal.PartIIPSL3FieldReconstruction
open PartIIPSL3Unipotent PartIIPSL3RootGeometry PartIIPSL3RootSeparation
open PartIIA2Orbital PartIIA2RootNormalization PartIIA2GraphSupply PartIIA2GraphTorus
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev pi : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (Subgroup.center _)
private abbrev rt (r : Fin 3) (t : F) : SL(3,F) := (a2Kernel% root) r t
private abbrev prt (r : Fin 3) (t : F) : PSL(3,F) := pi (rt r t)
/-- The genuine induced projective action of an actual SL3 model; this is
used only for the constructed model, never assumed for a bare PSL3 auto. -/
def projectiveAut (beta : MulAut SL(3,F)) : MulAut PSL(3,F) :=
  QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) beta
    ((Subgroup.characteristic_iff_map_eq.mp inferInstance) beta)
@[simp] theorem projectiveAut_apply (beta : MulAut SL(3,F)) (z : SL(3,F)) :
    projectiveAut beta (pi z)=pi (beta z) := rfl
private theorem positive_commutator (t s : F) :
    prt 0 t*prt 1 s*(prt 0 t)⁻¹*(prt 1 s)⁻¹=prt 2 (t*s) := by
  have hh := congrArg (pi (F := F)) ((psl3Field% positive_commutator) t s)
  change pi (rt 0 t*rt 1 s*(rt 0 t)⁻¹*(rt 1 s)⁻¹)=pi (rt 2 (t*s)) at hh
  simpa only [map_mul,map_inv] using hh
private theorem prt_injective (r : Fin 3) : Function.Injective (prt (F := F) r) :=
  (psl3Field% prt_injective) r
theorem actual_projective_positive_root_field (beta : MulAut PSL(3,F))
    (f : Fin 3 → F ≃+ F)
    (hb : ∀ r t, beta (prt r t) = prt r (f r t)) :
    ∃ phi : RingAut F,
      (∀ t, f 0 t = f 0 1*phi t) ∧
      (∀ t, f 1 t = f 1 1*phi t) ∧
      (∀ t, f 2 t = f 0 1*f 1 1*phi t) := by
  have hf0 : f 0 1 ≠ 0 := by intro h; exact one_ne_zero ((f 0).map_eq_zero_iff.mp h)
  have hf1 : f 1 1 ≠ 0 := by intro h; exact one_ne_zero ((f 1).map_eq_zero_iff.mp h)
  have hmul : ∀ t s, f 2 (t*s) = f 0 t*f 1 s := by
    intro t s
    have hh := congrArg beta (positive_commutator t s)
    simp only [map_mul,map_inv,hb] at hh
    rw [positive_commutator] at hh
    exact (prt_injective 2 hh).symm
  have h20 : ∀ t, f 2 t = f 0 t*f 1 1 := by intro t; simpa only [mul_one] using hmul t 1
  have h21 : ∀ t, f 2 t = f 0 1*f 1 t := by intro t; simpa only [one_mul] using hmul 1 t
  have hg : ∀ t, f 1 t = (f 0 1)⁻¹*f 0 t*f 1 1 := by
    intro t
    have h := (h21 t).symm.trans (h20 t)
    calc
      _ = (f 0 1)⁻¹*(f 0 1*f 1 t) := by rw [← mul_assoc,inv_mul_cancel₀ hf0,one_mul]
      _ = _ := by rw [h,mul_assoc]
  let fn : F ≃+ F :=
    { toFun := fun t => (f 0 1)⁻¹*f 0 t
      invFun := fun t => (f 0).symm (f 0 1*t)
      left_inv := by intro t; simp [mul_assoc,hf0]
      right_inv := by intro t; simp [mul_assoc,hf0]
      map_add' := by intro t s; simp [map_add,mul_add] }
  have hfnmul : ∀ t s, fn (t*s) = fn t*fn s := by
    intro t s
    have hh := hmul t s
    rw [h20 (t*s),hg s] at hh
    have hff : f 0 (t*s) = f 0 t*((f 0 1)⁻¹*f 0 s) := by
      apply mul_right_cancel₀ hf1
      simpa only [mul_assoc] using hh
    change (f 0 1)⁻¹*f 0 (t*s)=((f 0 1)⁻¹*f 0 t)*((f 0 1)⁻¹*f 0 s)
    rw [hff,mul_assoc]
  let phi : RingAut F := {fn with map_mul' := hfnmul}
  have hf0t : ∀ t, f 0 t = f 0 1*phi t := by
    intro t
    change f 0 t = f 0 1*((f 0 1)⁻¹*f 0 t)
    rw [← mul_assoc,mul_inv_cancel₀ hf0,one_mul]
  refine ⟨phi,hf0t,?_,?_⟩
  · intro t
    rw [hg]
    change (f 0 1)⁻¹*f 0 t*f 1 1 = f 1 1*((f 0 1)⁻¹*f 0 t)
    ring
  · intro t
    rw [h20,hf0t]
    ring
private theorem root_additive_coordinates (beta : MulAut PSL(3,F)) (r : Fin 3)
    (hmap : (projectivePositiveRoot r).map beta.toMonoidHom = projectivePositiveRoot (F := F) r) :
    ∃ f : F ≃+ F, ∀ t, beta (prt r t) = prt r (f t) := by
  classical
  have hmem : ∀ t : F, beta (prt r t) ∈ projectivePositiveRoot r := by
    intro t
    rw [← hmap]
    exact Subgroup.mem_map_of_mem beta.toMonoidHom ⟨rt r t,⟨t,rfl⟩,rfl⟩
  have hchart : ∀ t : F, ∃ s : F, prt r s=beta (prt r t) := by
    intro t
    obtain ⟨g,⟨s,rfl⟩,h⟩ := hmem t
    exact ⟨s,h⟩
  choose f hf using hchart
  have hinj : Function.Injective f := by
    intro t s h
    apply prt_injective r
    apply beta.injective
    rw [← hf t,← hf s,h]
  have hsurj : Function.Surjective f := by
    intro s
    have hs : prt r s ∈ (projectivePositiveRoot r).map beta.toMonoidHom := by
      rw [hmap]
      exact ⟨rt r s,⟨s,rfl⟩,rfl⟩
    obtain ⟨g,⟨z,⟨t,rfl⟩,rfl⟩,ht⟩ := hs
    refine ⟨t,prt_injective r ?_⟩
    change prt r (f t)=prt r s
    rw [hf t]
    exact ht
  have hadd : ∀ t s, f (t+s)=f t+f s := by
    intro t s
    apply prt_injective r
    change prt r (f (t+s))=prt r (f t+f s)
    have hradd : ∀ t s : F, prt r (t+s)=prt r t*prt r s :=
      fun t s => by
        change pi (rt r (t+s))=pi (rt r t)*pi (rt r s)
        rw [← map_mul]
        exact congrArg pi (transvection_add ((a2Kernel% root_ne) r) t s)
    rw [hf (t+s),hradd,map_mul,← hf t,← hf s,← hradd]
  let fa : F →+ F :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        simp only [zero_add] at h
        linear_combination -h
      map_add' := hadd }
  let fe := AddEquiv.ofBijective fa ⟨hinj,hsurj⟩
  exact ⟨fe,fun t => (hf t).symm⟩

private def swapRoot : Fin 3 → Fin 3 := ![1,0,2]
private theorem tau_prt (r : Fin 3) (t : F) :
    projectiveAut tau (prt r t)=prt (swapRoot r) (-t) := by
  rw [projectiveAut_apply]
  apply congrArg pi
  fin_cases r
  · exact tau_T01 t
  · exact tau_T12 t
  · exact tau_T02 t
private theorem tau_root_image (r : Fin 3) :
    (projectivePositiveRoot (F := F) r).map (projectiveAut tau).toMonoidHom=
      projectivePositiveRoot (swapRoot r) := by
  apply le_antisymm
  · rintro g ⟨z,⟨w,⟨t,rfl⟩,rfl⟩,rfl⟩
    exact ⟨rt (swapRoot r) (-t),⟨-t,rfl⟩,(tau_prt r t).symm⟩
  · rintro g ⟨z,⟨t,rfl⟩,rfl⟩
    refine ⟨prt r (-t),⟨rt r (-t),⟨-t,rfl⟩,rfl⟩,?_⟩
    change projectiveAut tau (prt r (-t))=prt (swapRoot r) t
    simpa only [neg_neg] using tau_prt r (-t)
private theorem root_preserving_projective_U_model (nu : MulAut PSL(3,F))
    (hroot : ∀ r, (projectivePositiveRoot r).map nu.toMonoidHom=projectivePositiveRoot (F := F) r) :
    ∃ (a : Fin 3 → Fˣ) (phi : RingAut F), ∀ z ∈ upperUnipotent (F := F),
      nu (pi z)=pi (diagonalFieldAut a phi z) := by
  classical
  choose f hf using fun r => root_additive_coordinates nu r (hroot r)
  obtain ⟨phi,h0,h1,h2⟩ := actual_projective_positive_root_field nu f hf
  have hc0 : f 0 1 ≠ 0 := by intro h; exact one_ne_zero ((f 0).map_eq_zero_iff.mp h)
  have hc1 : f 1 1 ≠ 0 := by intro h; exact one_ne_zero ((f 1).map_eq_zero_iff.mp h)
  let u0 : Fˣ := Units.mk0 (f 0 1) hc0
  let u1 : Fˣ := Units.mk0 (f 1 1) hc1
  let a : Fin 3 → Fˣ := ![u0*u1,u1,1]
  have hf' : ∀ r t, nu (prt r t)=prt r (f r t) := by
    intro r t; exact hf r t
  have hr : ∀ r t, nu (prt r t)=pi (diagonalFieldAut a phi (rt r t)) := by
    intro r t
    rw [hf' r]
    apply congrArg pi
    change transvection ((a2Kernel% root_ne) r) (f r t)=
      diagonalFieldAut a phi (transvection ((a2Kernel% root_ne) r) t)
    rw [diagonalFieldAut,MulAut.mul_apply,(a2Kernel% field_root),(a2Kernel% diagonal_root)]
    apply congrArg (transvection ((a2Kernel% root_ne) r))
    fin_cases r
    · change f 0 t=(↑(u0*u1):F)*(↑u1:F)⁻¹*phi t
      rw [h0]
      simp [a,u0,u1,Units.val_mul,mul_assoc,hc1]
    · change f 1 t=(↑u1:F)*(↑((1:Fˣ)⁻¹):F)*phi t
      rw [h1]
      simp [a,u1]
    · change f 2 t=(↑(u0*u1):F)*(↑((1:Fˣ)⁻¹):F)*phi t
      rw [h2]
      simp [a,u0,u1,Units.val_mul]
  refine ⟨a,phi,?_⟩
  rintro z ⟨A,B,C,rfl⟩
  rw [← (a2Kernel% three_root_product) A B C]
  simp only [map_mul]
  change nu (prt 0 A)*nu (prt 1 B)*nu (prt 2 (C-A*B))=
    pi (diagonalFieldAut a phi (rt 0 A))*pi (diagonalFieldAut a phi (rt 1 B))*
      pi (diagonalFieldAut a phi (rt 2 (C-A*B)))
  rw [hr,hr,hr]

/-- Every bare PSL3 automorphism has an actual inner/diagonal/field/graph
model ON actual U. Root images and the common field automorphism are derived
from the actual quotient geometry and root incidence; no SL3-auto lift. -/
theorem actual_bare_PSL3_U_action_model [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (beta : MulAut PSL(3,F)) :
    ∃ (g : PSL(3,F)) (a : Fin 3 → Fˣ) (phi : RingAut F) (eps : Bool),
      ∀ z ∈ upperUnipotent (F := F),
        (MulAut.conj g⁻¹*beta) (pi z)=pi (diagonalFieldGraphAut a phi eps z) := by
  classical
  obtain ⟨g,hU,hZ,hroots⟩ := actual_bare_PSL3_root_normalization hF beta
  let alpha := MulAut.conj g⁻¹*beta
  rcases hroots with ⟨h0,h1⟩|⟨h0,h1⟩
  · have hr : ∀ r, (projectivePositiveRoot r).map alpha.toMonoidHom=projectivePositiveRoot (F := F) r := by
      intro r; fin_cases r
      · exact h0
      · exact h1
      · exact hZ
    obtain ⟨a,phi,hm⟩ := root_preserving_projective_U_model alpha hr
    refine ⟨g,a,phi,false,?_⟩
    intro z hz
    simpa only [diagonalFieldGraphAut,Bool.false_eq_true,ite_false,mul_one] using hm z hz
  · let nu := alpha*projectiveAut tau
    have hr : ∀ r, (projectivePositiveRoot r).map nu.toMonoidHom=projectivePositiveRoot (F := F) r := by
      intro r
      change (projectivePositiveRoot r).map (alpha.toMonoidHom.comp (projectiveAut tau).toMonoidHom)=_
      rw [← Subgroup.map_map,tau_root_image]
      fin_cases r
      · exact h1
      · exact h0
      · exact hZ
    obtain ⟨a,phi,hm⟩ := root_preserving_projective_U_model nu hr
    refine ⟨g,a,phi,true,?_⟩
    intro z hz
    have hh := hm (tau z) ((a2Actual% tau_preserves_U) z hz)
    change alpha (pi (tau (tau z)))=pi (diagonalFieldAut a phi (tau z)) at hh
    rw [tau_involutive z] at hh
    exact hh
end NikolovSegal.PartIIPSL3FieldReconstruction
