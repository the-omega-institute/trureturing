/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2Opposite
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2Opposite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2Relations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Residual
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- The cube relation eliminates the actual top-right discrepancy at every
interior negative simple root in F2. -/
theorem fixes_interior_negative (hF : Fintype.card F=2) (hn : 4<n)
    (gamma : MulAut G) (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (r : PositiveIndex n) (hr : r.val.2.val=r.val.1.val+1)
    (hi : 0<r.val.1.val) (hj : r.val.2.val+1<n) :
    gamma (negativeRoot r 1)=negativeRoot r 1 := by
  classical
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hfl : first ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [first,last] at hv; omega
  have hif : r.val.1 ≠ first := by intro he; have hv:=congrArg Fin.val he; dsimp [first] at hv; omega
  have hjl : r.val.2 ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [last] at hv; omega
  have hil : r.val.1 ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [last] at hv; omega
  have hjf : r.val.2 ≠ first := by intro he; have hv:=congrArg Fin.val he; dsimp [first] at hv; omega
  let g := negativeRoot r (1:F)
  let x := root r (1:F)
  let k := gamma g*g⁻¹
  have hs := interior_centralizer_shape hF hn r hi hj k (discrepancy_commutes gamma hU r hr 1)
  have hk : k=SpecialLinearGroup.transvection hfl (k.val first last) := Subtype.ext hs
  have hkg : Commute k g := by
    rw [hk]
    exact transvections_commute hfl (ne_of_lt r.property).symm hjl.symm hif (k.val first last) 1
  have hkx : Commute k x := by
    rw [hk]
    exact transvections_commute hfl (ne_of_lt r.property) hil.symm hjf (k.val first last) 1
  have hgk : gamma g=k*g := by simp [k,mul_assoc]
  have hc : (x*g)^3=1 := opposite_pair_cube (ne_of_lt r.property)
  have hp := congrArg gamma hc
  have hem : gamma (x*g)=k*(x*g) := by
    rw [map_mul,hU x (root_mem_Uplus r 1),hgk,← mul_assoc,← hkx.eq,mul_assoc]
  rw [map_pow,map_one,hem,(hkx.mul_right hkg).mul_pow,hc,mul_one] at hp
  have hk2 : k^2=1 := by rw [hk]; exact transvection_pow_char 2 _ _ _ _
  have hk1 : k=1 := by simpa only [pow_succ,hk2,one_mul] using hp
  simpa only [hk1,one_mul] using hgk

/-- The involution relation removes the central top-right coefficient at the
first endpoint; the remaining coefficient is the actual residual inner freedom. -/
theorem first_negative_shape (hF : Fintype.card F=2) (hn : 4<n)
    (gamma : MulAut G) (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (r : PositiveIndex n) (hi : r.val.1.val=0)
    (hr : r.val.2.val=r.val.1.val+1) :
    let last : Fin n := ⟨n-1,by omega⟩
    ∃ v : F, (gamma (negativeRoot r 1)).val=
      1+Matrix.single r.val.2 r.val.1 1+Matrix.single r.val.2 last v := by
  classical
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hfi : first=r.val.1 := Fin.ext hi.symm
  have hfl : first ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [first,last] at hv; omega
  have hjl : r.val.2 ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [last] at hv; omega
  have hfj : first ≠ r.val.2 := by rw [hfi]; exact ne_of_lt r.property
  have hil : r.val.1 ≠ last := by simpa only [hfi] using hfl
  let g := negativeRoot r (1:F)
  let k := gamma g*g⁻¹
  have hs := first_centralizer_shape hF hn r hi hr k (discrepancy_commutes gamma hU r hr 1)
  change k.val=1+Matrix.single first last (k.val first last)+Matrix.single r.val.2 last (k.val r.val.2 last) at hs
  have hgk : gamma g=k*g := by simp [k,mul_assoc]
  have he : (gamma g).val=1+Matrix.single first last (k.val first last)+
      Matrix.single r.val.2 last (k.val r.val.2 last)+Matrix.single r.val.2 r.val.1 1 := by
    rw [hgk]
    change k.val*(1+Matrix.single r.val.2 r.val.1 1)=_
    conv_lhs => rw [hs]
    simp [Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne,hjl.symm]
  have hp : (gamma g)^2=1 := by rw [← map_pow,transvection_pow_char 2 _ _ _ (1:F),map_one]
  rw [pow_two] at hp
  have hv := congrArg (fun z : G => z.val r.val.2 last) hp
  change ((gamma g).val*(gamma g).val) r.val.2 last=(1:Matrix (Fin n) (Fin n) F) r.val.2 last at hv
  rw [he] at hv
  have hb : k.val first last=0 := by
    simp [Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne,hfi,ne_of_lt r.property,
      (ne_of_lt r.property).symm,hfl,hfl.symm,hjl,hjl.symm,Matrix.single_apply,
      Matrix.one_apply,hil,hil.symm] at hv
    ring_nf at hv
    simpa [CharTwo.two_eq_zero,hfi] using hv
  refine ⟨k.val r.val.2 last,?_⟩
  change (gamma g).val=_
  rw [he,hb]
  simp [Matrix.single_zero,add_comm,add_left_comm,add_assoc,last]

/-- The symmetric endpoint involution calculation, with actual matrix entries. -/
theorem last_negative_shape (hF : Fintype.card F=2) (hn : 4<n)
    (gamma : MulAut G) (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (r : PositiveIndex n) (hj : r.val.2.val+1=n)
    (hr : r.val.2.val=r.val.1.val+1) :
    let first : Fin n := ⟨0,by omega⟩
    ∃ w : F, (gamma (negativeRoot r 1)).val=
      1+Matrix.single r.val.2 r.val.1 1+Matrix.single first r.val.1 w := by
  classical
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hlj : last=r.val.2 := Fin.ext (by dsimp [last]; omega)
  have hfl : first ≠ last := by intro he; have hv:=congrArg Fin.val he; dsimp [first,last] at hv; omega
  have hfi : first ≠ r.val.1 := by intro he; have hv:=congrArg Fin.val he; dsimp [first] at hv; omega
  have hil : r.val.1 ≠ last := by rw [hlj]; exact ne_of_lt r.property
  have hjf : r.val.2 ≠ first := by simpa only [hlj] using hfl.symm
  let g := negativeRoot r (1:F)
  let k := gamma g*g⁻¹
  have hs := last_centralizer_shape hF hn r hj hr k (discrepancy_commutes gamma hU r hr 1)
  change k.val=1+Matrix.single first last (k.val first last)+Matrix.single first r.val.1 (k.val first r.val.1) at hs
  have hgk : gamma g=k*g := by simp [k,mul_assoc]
  have he : (gamma g).val=1+Matrix.single first last (k.val first last)+
      Matrix.single first r.val.1 (k.val first r.val.1+k.val first last)+
      Matrix.single r.val.2 r.val.1 1 := by
    rw [hgk]
    change k.val*(1+Matrix.single r.val.2 r.val.1 1)=_
    conv_lhs => rw [hs]
    simp [Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne,hlj,ne_of_lt r.property,
      Matrix.single_add]
    abel
  have hp : (gamma g)^2=1 := by rw [← map_pow,transvection_pow_char 2 _ _ _ (1:F),map_one]
  rw [pow_two] at hp
  have hv := congrArg (fun z : G => z.val first r.val.1) hp
  change ((gamma g).val*(gamma g).val) first r.val.1=(1:Matrix (Fin n) (Fin n) F) first r.val.1 at hv
  rw [he] at hv
  have hb : k.val first last=0 := by
    simp [Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne,hlj,ne_of_lt r.property,
      (ne_of_lt r.property).symm,hfl,hfl.symm,hfi,hfi.symm,hil,hil.symm,Matrix.single_apply,
      Matrix.one_apply,hjf,hjf.symm] at hv
    ring_nf at hv
    have h3 : (3:F)=1 := by
      rw [show (3:F)=(2:F)+1 by norm_num,CharTwo.two_eq_zero,zero_add]
    simpa [CharTwo.two_eq_zero,h3,hlj] using hv
  refine ⟨k.val first r.val.1,?_⟩
  change (gamma g).val=_
  rw [he,hb]
  simp [Matrix.single_zero,add_comm,add_left_comm,add_assoc,first]

end NikolovSegal.SLnF2Residual
