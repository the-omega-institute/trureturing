/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2TransvectionRecognition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2FullAgreement
import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIIPSLnF2FullAgreement
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Bare
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer NikolovSegal.SLnF2Residual
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

abbrev first (hn : 4<n) : Fin n := ⟨0,by omega⟩
abbrev last (hn : 4<n) : Fin n := ⟨n-1,by omega⟩
theorem first_ne_last (hn : 4<n) : first hn ≠ last hn := by
  intro he; have hv:=congrArg Fin.val he; dsimp [first,last] at hv; omega
abbrev top (hn : 4<n) : G := SpecialLinearGroup.transvection (first_ne_last hn) 1

theorem top_ne_one (hn : 4<n) : top (F := F) hn ≠ 1 := by
  intro he
  have hv := congrArg (fun g : G => g.val (first hn) (last hn)) he
  simpa [top,SpecialLinearGroup.transvection_coe,Matrix.single_apply,Matrix.one_apply,first_ne_last hn] using hv

/-- The actual top-right root element centralizes the whole U, using the
accepted root generation body rather than a centre oracle. -/
theorem top_commutes_U (hn : 4<n) : ∀ x ∈ Uplus n F, top hn*x=x*top hn := by
  have hpos : ∀ r : PositiveIndex n, ∀ t : F, (MulAut.conj (top hn)) (root r t)=root r t := by
    intro r t
    have hli : last hn ≠ r.val.1 := by
      intro he
      have hv:=congrArg Fin.val he; dsimp [last] at hv
      have hr:=r.property; change r.val.1.val<r.val.2.val at hr
      have hb:=r.val.2.isLt; omega
    have hjf : r.val.2 ≠ first hn := by
      intro he
      have hv:=congrArg Fin.val he; dsimp [first] at hv
      have hr:=r.property; change r.val.1.val<r.val.2.val at hr; omega
    have he := transvections_commute (first_ne_last hn) (ne_of_lt r.property) hli hjf (1:F) t
    change top hn*root r t=root r t*top hn at he
    change top hn*root r t*(top hn)⁻¹=root r t
    rw [he]; simp [mul_assoc]
  have hU := hom_ext_on_Uplus (MulAut.conj (top (F := F) hn)).toMonoidHom (MonoidHom.id G) hpos
  intro x hx
  have he := hU x hx
  change top hn*x*(top hn)⁻¹=x at he
  calc
    top hn*x = (top hn*x*(top hn)⁻¹)*top hn := by group
    _ = x*top hn := by rw [he]

/-- A U-normalized bare automorphism fixes the unique nonidentity actual
central-U top-right transvection over F2. -/
theorem normalized_fixes_top (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F) :
    alpha (top hn)=top hn := by
  have hx : alpha (top hn) ∈ Uplus n F := by
    rw [← hU]
    exact Subgroup.mem_map_of_mem _ (transvection_mem_Uplus (by change 0<n-1; omega) 1)
  have hc : ∀ r : PositiveIndex n, alpha (top hn)*root r 1=root r 1*alpha (top hn) := by
    intro r
    have hy : root r (1:F) ∈ (Uplus n F).map alpha.toMonoidHom := hU.symm ▸ root_mem_Uplus r 1
    obtain ⟨y,hy,he⟩ := hy
    change alpha y=root r 1 at he
    simpa only [map_mul,he] using congrArg alpha (top_commutes_U hn y hy)
  let r : PositiveIndex n := ⟨(⟨1,by omega⟩,⟨2,by omega⟩),by change 1<2; omega⟩
  have hs := interior_centralizer_shape hF hn r (by change 0<1; omega)
    (by change 2+1<n; omega) (alpha (top hn)) (fun s _ => hc s)
  have he : alpha (top hn)=SpecialLinearGroup.transvection (first_ne_last hn)
      ((alpha (top hn)).val (first hn) (last hn)) := Subtype.ext hs
  rcases eq_zero_or_one hF ((alpha (top hn)).val (first hn) (last hn)) with hz|hz
  · rw [hz,SpecialLinearGroup.transvection_coeff_zero] at he
    exact False.elim (top_ne_one hn (alpha.injective (he.trans alpha.map_one.symm)))
  · simpa only [hz] using he

/-- In a two-element field the actual permutation matrix has determinant1. -/
noncomputable def permutationSL (hF : Fintype.card F=2) (sigma : Equiv.Perm (Fin n)) : G :=
  ⟨sigma.permMatrix F,by
    have hp : sigma.permMatrix F*(sigma⁻¹).permMatrix F=1 := by
      rw [← Matrix.permMatrix_mul]; simp
    have hnz : Matrix.det (sigma.permMatrix F) ≠ 0 := by
      intro hz
      have hd := congrArg Matrix.det hp
      rw [Matrix.det_mul,hz,zero_mul,Matrix.det_one] at hd
      exact zero_ne_one hd
    exact (eq_zero_or_one hF _).resolve_left hnz⟩

theorem permutationSL_inv (hF : Fintype.card F=2) (sigma : Equiv.Perm (Fin n)) :
    (permutationSL hF sigma)⁻¹=permutationSL hF sigma⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change sigma.permMatrix F*(sigma⁻¹).permMatrix F=1
  rw [← Matrix.permMatrix_mul]; simp

theorem permutationSL_conj (hF : Fintype.card F=2) (sigma : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i ≠ j) (t : F) :
    (MulAut.conj (permutationSL hF sigma)) (SpecialLinearGroup.transvection hij t)=
      SpecialLinearGroup.transvection (sigma.symm.injective.ne hij) t := by
  change permutationSL hF sigma*SpecialLinearGroup.transvection hij t*(permutationSL hF sigma)⁻¹=_
  rw [permutationSL_inv]
  apply Subtype.ext
  change sigma.permMatrix F*(1+Matrix.single i j t)*(sigma⁻¹).permMatrix F=
    1+Matrix.single (sigma.symm i) (sigma.symm j) t
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  simp only [Equiv.Perm.inv_def,Equiv.symm_symm]
  ext a b
  simp [Matrix.submatrix_apply,Matrix.one_apply,Matrix.single_apply,← Equiv.eq_symm_apply]

/-- Every literal elementary transvection is genuinely conjugate to the
actual central-U element in SLn(F2), including the determinant-one condition. -/
theorem transvection_conjugate_top (hF : Fintype.card F=2) (hn : 4<n)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ c : G, SpecialLinearGroup.transvection hij (1:F)=(MulAut.conj c) (top hn) := by
  classical
  let f : Bool → Fin n := fun b => if b then j else i
  let g : Bool → Fin n := fun b => if b then last hn else first hn
  have hf : Function.Injective f := by intro a b; cases a <;> cases b <;> simp_all [f,hij.symm]
  have hg : Function.Injective g := by
    intro a b; cases a <;> cases b <;> simp_all [g,first_ne_last hn,(first_ne_last hn).symm]
  obtain ⟨sigma,hs⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hi : sigma i=first hn := hs false
  have hj : sigma j=last hn := hs true
  have hi' : sigma.symm (first hn)=i := by rw [← hi,sigma.symm_apply_apply]
  have hj' : sigma.symm (last hn)=j := by rw [← hj,sigma.symm_apply_apply]
  refine ⟨permutationSL hF sigma,?_⟩
  rw [top,permutationSL_conj]
  apply Subtype.ext
  simp only [SpecialLinearGroup.transvection_coe,hi',hj']

def deviation (g : G) : Matrix (Fin n) (Fin n) F := g.val-1

/-- Literal rank-one minors of a conjugated elementary transvection; no
rank/eigenvector or transvection-recognition premise is used. -/
theorem conjugate_transvection_minors (c : G) (i j : Fin n) (hij : i ≠ j) :
    let A := (MulAut.conj c) (SpecialLinearGroup.transvection hij (1:F))
    ∀ a b d e, deviation A a b*deviation A d e=deviation A a e*deviation A d b := by
  let A := (MulAut.conj c) (SpecialLinearGroup.transvection hij (1:F))
  change ∀ a b d e, deviation A a b*deviation A d e=deviation A a e*deviation A d b
  have hdev : deviation A=c.val*Matrix.single i j (1:F)*(c⁻¹).val := by
    change (c.val*(1+Matrix.single i j (1:F))*(c⁻¹).val)-1=_
    rw [Matrix.mul_add,Matrix.mul_one,Matrix.add_mul]
    have he : c.val*(c⁻¹).val=1 := by
      have he := congrArg (fun g : G => g.val) (mul_inv_cancel c)
      change c.val*(c⁻¹).val=1 at he
      exact he
    rw [he,add_sub_cancel_left]
  have hentry : ∀ a b, deviation A a b=c.val a i*(c⁻¹).val j b := by
    intro a b
    rw [hdev]
    simp [Matrix.mul_apply,Matrix.single_apply,ite_and,mul_ite,ite_mul,mul_assoc,eq_comm]
  intro a b d e
  rw [hentry,hentry,hentry,hentry]
  ring

/-- U-normalization forces actual rank-one-minor equations on every image
of an elementary transvection, derived from the full-group conjugacy relation. -/
theorem normalized_transvection_image_minors (hF : Fintype.card F=2) (hn : 4<n)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom=Uplus n F)
    (i j : Fin n) (hij : i ≠ j) :
    ∀ a b d e, deviation (alpha (SpecialLinearGroup.transvection hij 1)) a b*
      deviation (alpha (SpecialLinearGroup.transvection hij 1)) d e=
      deviation (alpha (SpecialLinearGroup.transvection hij 1)) a e*
      deviation (alpha (SpecialLinearGroup.transvection hij 1)) d b := by
  obtain ⟨c,hc⟩ := transvection_conjugate_top hF hn i j hij
  have he : alpha (SpecialLinearGroup.transvection hij 1)=(MulAut.conj (alpha c)) (top hn) := by
    rw [hc]
    change alpha (c*top hn*c⁻¹)=alpha c*top hn*(alpha c)⁻¹
    rw [map_mul,map_mul,map_inv,normalized_fixes_top hF hn alpha hU]
  rw [he]
  exact conjugate_transvection_minors (alpha c) (first hn) (last hn) (first_ne_last hn)

end NikolovSegal.SLnF2Bare
