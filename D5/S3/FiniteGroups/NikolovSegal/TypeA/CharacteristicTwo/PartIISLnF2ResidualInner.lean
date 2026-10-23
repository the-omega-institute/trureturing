/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2ResidualInner
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2ResidualInner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo.PartIISLnF2Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnF2Residual
open Matrix NikolovSegal.SLnRootAction NikolovSegal.SLnFullGroup
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

/-- Commutation of the separated endpoint images forces one common residual
parameter. The equation is derived from the literal (j,k) matrix entry. -/
theorem endpoint_parameters {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (A B : G) (v w : F)
    (hA : A.val=1+Matrix.single j i 1+Matrix.single j l v)
    (hB : B.val=1+Matrix.single l k 1+Matrix.single i k w)
    (hc : A*B=B*A) : v=w := by
  have he := congrArg (fun g : G => g.val j k) hc
  change (A.val*B.val) j k=(B.val*A.val) j k at he
  rw [hA,hB] at he
  have hsum : v+w=0 := by
    simpa [Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,
      hij,hij.symm,hik,hik.symm,hil,hil.symm,hjk,hjk.symm,hjl,hjl.symm,hkl,hkl.symm,
      Matrix.single_apply,Matrix.one_apply,add_comm,add_left_comm,add_assoc] using he
  exact CharTwo.add_eq_zero.mp hsum

theorem conj_top_first {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (v : F) :
    ((MulAut.conj (SpecialLinearGroup.transvection hil v))
      (SpecialLinearGroup.transvection hij.symm (1:F))).val=
      1+Matrix.single j i 1+Matrix.single j l v := by
  have he := transvection_conjugate_chain_right hij.symm hil hjl v (1:F)
  change (SpecialLinearGroup.transvection hil v * SpecialLinearGroup.transvection hij.symm 1 *
    (SpecialLinearGroup.transvection hil v)⁻¹).val=_
  rw [he]
  change (1+Matrix.single j i (1:F))*(1+Matrix.single j l (-1*v))=_
  simp [CharTwo.neg_eq,Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,
    hij,add_assoc]

theorem conj_top_last {i k l : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) (v : F) :
    ((MulAut.conj (SpecialLinearGroup.transvection hil v))
      (SpecialLinearGroup.transvection hkl.symm (1:F))).val=
      1+Matrix.single l k 1+Matrix.single i k v := by
  have he := transvection_conjugate_chain hil hkl.symm hik v (1:F)
  change (SpecialLinearGroup.transvection hil v * SpecialLinearGroup.transvection hkl.symm 1 *
    (SpecialLinearGroup.transvection hil v)⁻¹).val=_
  rw [he]
  change (1+Matrix.single l k (1:F))*(1+Matrix.single i k (v*1))=_
  simp [Matrix.mul_add,Matrix.add_mul,Matrix.single_mul_single_of_ne,hik.symm,add_assoc]

/-- Every actual automorphism fixing U pointwise over a two-element field is
the conjugation by ONE actual top-right root element. The residual freedom is
proved and retained, rather than falsely asserting pointwise-U rigidity. -/
theorem pointwise_U_is_central_U_inner (hF : Fintype.card F=2) (hn : 4<n)
    (gamma : MulAut G) (hU : ∀ x ∈ Uplus n F, gamma x=x) :
    ∃ c ∈ Uplus n F, (∀ x ∈ Uplus n F, c*x=x*c) ∧
      ∀ x : G, gamma x=(MulAut.conj c) x := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  let k : Fin n := ⟨n-2,by omega⟩
  let l : Fin n := ⟨n-1,by omega⟩
  have hij : i ≠ j := by intro he; have hv:=congrArg Fin.val he; dsimp [i,j] at hv; omega
  have hik : i ≠ k := by intro he; have hv:=congrArg Fin.val he; dsimp [i,k] at hv; omega
  have hil : i ≠ l := by intro he; have hv:=congrArg Fin.val he; dsimp [i,l] at hv; omega
  have hjk : j ≠ k := by intro he; have hv:=congrArg Fin.val he; dsimp [j,k] at hv; omega
  have hjl : j ≠ l := by intro he; have hv:=congrArg Fin.val he; dsimp [j,l] at hv; omega
  have hkl : k ≠ l := by intro he; have hv:=congrArg Fin.val he; dsimp [k,l] at hv; omega
  let r : PositiveIndex n := ⟨(i,j),by change 0<1; omega⟩
  let s : PositiveIndex n := ⟨(k,l),by change n-2<n-1; omega⟩
  obtain ⟨v,hv⟩ := first_negative_shape hF hn gamma hU r rfl rfl
  obtain ⟨w,hw⟩ := last_negative_shape hF hn gamma hU s (by dsimp [s,l]; omega) (by dsimp [s,k,l]; omega)
  change (gamma (negativeRoot r 1)).val=1+Matrix.single j i 1+Matrix.single j l v at hv
  change (gamma (negativeRoot s 1)).val=1+Matrix.single l k 1+Matrix.single i k w at hw
  have hc : gamma (negativeRoot r 1)*gamma (negativeRoot s 1)=
      gamma (negativeRoot s 1)*gamma (negativeRoot r 1) := by
    simpa only [map_mul] using congrArg gamma
      (transvections_commute hij.symm hkl.symm hil hjk.symm (1:F) (1:F))
  have hvw := endpoint_parameters hij hik hil hjk hjl hkl _ _ v w hv hw hc
  let c : G := SpecialLinearGroup.transvection hil v
  have hcpos : ∀ a : PositiveIndex n, ∀ t : F, (MulAut.conj c) (root a t)=root a t := by
    intro a t
    have hai : a.val.2 ≠ i := by
      intro he
      have ha := a.property
      change a.val.1.val<a.val.2.val at ha
      have hval := congrArg Fin.val he
      dsimp [i] at hval; omega
    have hal : l ≠ a.val.1 := by
      intro he
      have ha := a.property
      change a.val.1.val<a.val.2.val at ha
      have hb := a.val.2.isLt
      have hval := congrArg Fin.val he
      dsimp [l] at hval; omega
    have hcomm := transvections_commute hil (ne_of_lt a.property) hal hai v t
    change c*root a t=root a t*c at hcomm
    change c*root a t*c⁻¹=root a t
    rw [hcomm]
    simp [mul_assoc]
  have hcU : ∀ x ∈ Uplus n F, (MulAut.conj c) x=x :=
    hom_ext_on_Uplus (MulAut.conj c).toMonoidHom (MonoidHom.id G) hcpos
  have hneg : ∀ a : PositiveIndex n, a.val.2.val=a.val.1.val+1 →
      ∀ t : F, gamma (negativeRoot a t)=(MulAut.conj c) (negativeRoot a t) := by
    intro a ha t
    rcases eq_zero_or_one hF t with ht|ht
    · subst t; simp [negativeRoot]
    subst t
    by_cases hfirst : a.val.1.val=0
    · have har : a=r := by
        apply Subtype.ext; apply Prod.ext
        · exact Fin.ext hfirst
        · apply Fin.ext; dsimp [r,j]; omega
      subst a
      apply Subtype.ext
      rw [hv]
      exact (conj_top_first hij hil hjl v).symm
    by_cases hlast : a.val.2.val+1=n
    · have has : a=s := by
        apply Subtype.ext; apply Prod.ext
        · apply Fin.ext; dsimp [s,k]; omega
        · apply Fin.ext; dsimp [s,l]; omega
      subst a
      apply Subtype.ext
      rw [hw,← hvw]
      exact (conj_top_last hik hil hkl v).symm
    · have hint : gamma (negativeRoot a 1)=negativeRoot a 1 :=
        fixes_interior_negative hF hn gamma hU a ha (by omega) (by have hb:=a.val.2.isLt; omega)
      rw [hint]
      have hai : a.val.1 ≠ i := by
        intro he; have hv := congrArg Fin.val he; dsimp [i] at hv; exact hfirst hv
      have hal : l ≠ a.val.2 := by
        intro he; have hv := congrArg Fin.val he; dsimp [l] at hv; omega
      have hcomm := transvections_commute hil (ne_of_lt a.property).symm hal hai v (1:F)
      change c*negativeRoot a 1=negativeRoot a 1*c at hcomm
      change negativeRoot a 1=c*negativeRoot a 1*c⁻¹
      rw [hcomm]
      simp [mul_assoc]
  refine ⟨c,transvection_mem_Uplus (by change 0<n-1; omega) v,?_,?_⟩
  · intro x hx
    have he := hcU x hx
    change c*x*c⁻¹=x at he
    simpa [mul_assoc] using congrArg (fun y : G => y*c) he
  · apply hom_ext_positive_negative_simple (by omega) gamma.toMonoidHom (MulAut.conj c).toMonoidHom
    · intro a t; exact (hU _ (root_mem_Uplus a t)).trans (hcpos a t).symm
    · exact hneg

/-- An actual central-U inner correction removes the entire F2 residual
automorphism before every full-group target. -/
theorem pointwise_U_inner_correction (hF : Fintype.card F=2) (hn : 4<n)
    (gamma : MulAut G) (hU : ∀ x ∈ Uplus n F, gamma x=x) :
    ∃ c ∈ Uplus n F, (∀ x ∈ Uplus n F, c*x=x*c) ∧
      ∀ x : G, (MulAut.conj c*gamma) x=x := by
  obtain ⟨c,hc,hcomm,hgamma⟩ := pointwise_U_is_central_U_inner hF hn gamma hU
  refine ⟨c⁻¹,(Uplus n F).inv_mem hc,?_,?_⟩
  · intro x hx; exact (show Commute c x from hcomm x hx).inv_left.eq
  · intro x
    change c⁻¹*gamma x*(c⁻¹)⁻¹=x
    rw [hgamma]
    change c⁻¹*(c*x*c⁻¹)*(c⁻¹)⁻¹=x
    group

end NikolovSegal.SLnF2Residual
