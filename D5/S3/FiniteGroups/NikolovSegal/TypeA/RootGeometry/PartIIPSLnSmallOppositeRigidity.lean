/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnSmallOppositeRigidity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnSmallOppositeRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallCentralizer
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.PSLnSmallField
open Matrix NikolovSegal.SLnRootAction NikolovSegal.PSLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
open NikolovSegal.SLnSmallField NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)
local notation "T" => diagonalTorus n F
open NikolovSegal.SLnFullGroup

theorem fixes_U_kernel_preimage [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (gamma : MulAut Q) (hU : ∀ x ∈ Uplus n F, gamma (π x)=π x)
    (hT : (projectiveDiagonalTorus n F).map gamma.toMonoidHom=projectiveDiagonalTorus n F)
    (r : PositiveIndex n) (d : G) (hd : d ∈ torusKernel (F := F) r) :
    ∃ e ∈ torusKernel (F := F) r, gamma (π e)=π d := by
  have hdT : π d ∈ (projectiveDiagonalTorus n F).map gamma.toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_map_of_mem π ((mem_torusKernel_iff r d).mp hd).1
  obtain ⟨v,⟨e,he,rfl⟩,hed⟩ := hdT
  change gamma (π e)=π d at hed
  refine ⟨e,(mem_torusKernel_iff r e).mpr ⟨he,?_⟩,hed⟩
  apply commute_transvection_diagonal e r.val.1 r.val.2 (ne_of_lt r.property)
  apply lift_commutation e (root r 1) (root_mem_Uplus r 1)
  apply gamma.injective
  change gamma (π e*π (root r 1))=gamma (π (root r 1)*π e)
  simp only [map_mul,hU (root r 1) (root_mem_Uplus r 1),hed]
  have hc := (fixed_torusKernel_iff hn hF r (root r 1) (root_mem_Uplus r 1)).mpr ⟨1,rfl⟩ d hd
  simpa only [map_mul] using congrArg π hc

theorem fixes_negative_simple [Fintype F] (hn : 4 < n)
    (hF : 2 < Fintype.card F) (gamma : MulAut Q)
    (hU : ∀ x ∈ Uplus n F, gamma (π x)=π x)
    (hT : (projectiveDiagonalTorus n F).map gamma.toMonoidHom=projectiveDiagonalTorus n F)
    (r : PositiveIndex n) (hsimple : r.val.2.val=r.val.1.val+1) (t : F) :
    gamma (π (negativeRoot r t))=π (negativeRoot r t) := by
  let g := negativeRoot r t
  obtain ⟨h,hh⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) (gamma (π g))
  let k := h*g⁻¹
  have hpos : ∀ s : PositiveIndex n, s ≠ r → k*root s 1=root s 1*k := by
    intro s hsr
    have hy : g⁻¹*root s 1*g ∈ Uplus n F := by
      simpa only [g,negativeRoot,SpecialLinearGroup.transvection_inv,inv_inv,neg_neg] using
        negative_simple_conjugate_mem_U r s hsimple hsr (-t) (1:F)
    have he : (π h)⁻¹*π (root s 1)*π h=π (g⁻¹*root s 1*g) := by
      rw [hh]
      simpa only [map_mul,map_inv,hU (root s 1) (root_mem_Uplus s 1)] using hU _ hy
    have hq : π (k*root s 1*k⁻¹)=π (root s 1) := by
      simp only [map_mul,map_inv,k]
      calc
        _ = π h*((π g)⁻¹*π (root s 1)*π g)*(π h)⁻¹ := by group
        _ = π h*((π h)⁻¹*π (root s 1)*π h)*(π h)⁻¹ := by
          have he' : (π g)⁻¹*π (root s 1)*π g=(π h)⁻¹*π (root s 1)*π h := by
            simpa only [map_mul,map_inv] using he.symm
          rw [he']
        _ = π (root s 1) := by group
    have hc := conjugate_eq_of_quotient_eq k (root s 1) (root s 1)
      (root_mem_Uplus s 1) (root_mem_Uplus s 1) hq
    simpa [mul_assoc] using congrArg (fun x : G => x*k) hc
  obtain ⟨v,hvi,hvj⟩ := Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by omega)
  let s : PositiveIndex n := if hv : v < r.val.1 then ⟨(v,r.val.1),hv⟩
    else ⟨(r.val.1,v),lt_of_le_of_ne (le_of_not_gt hv) hvi.symm⟩
  have hsr : s ≠ r := by
    dsimp only [s]
    split_ifs with hv
    · intro he; exact hvi (congrArg (fun x : PositiveIndex n => x.val.1) he)
    · intro he; exact hvj (congrArg (fun x : PositiveIndex n => x.val.2) he)
  have hknz := commuting_root_diagonal_nonzero k s (hpos s hsr)
  have hK : ∀ d ∈ torusKernel (F := F) r, d*k=k*d := by
    intro d hd
    obtain ⟨e,he,hed⟩ := fixes_U_kernel_preimage hn hF gamma hU hT r d hd
    have hc : Commute (π d) (π h) := by
      change π d*π h=π h*π d
      have hec := congrArg (fun x : G => gamma (π x)) (negativeRoot_commutes_kernel r t e he)
      simpa only [map_mul,hed,← hh,g] using hec
    have hdg : Commute (π d) (π g) := by
      change π d*π g=π g*π d
      simpa only [map_mul,g] using congrArg π (negativeRoot_commutes_kernel r t d hd)
    apply lift_diagonal_commutation k d ((mem_torusKernel_iff r d).mp hd).1 s.val.2 hknz
    simpa only [k,map_mul,map_inv] using (hc.mul_right hdg.inv_right).eq
  have hk := simple_root_centralizer_is_center hn hF r hsimple k hK hpos
  have hqk : π k=1 := (QuotientGroup.eq_one_iff k).mpr hk
  have hkprod : h=k*g := by simp [k,mul_assoc]
  rw [← hh,hkprod,map_mul,hqk,one_mul]

end NikolovSegal.PSLnSmallField
