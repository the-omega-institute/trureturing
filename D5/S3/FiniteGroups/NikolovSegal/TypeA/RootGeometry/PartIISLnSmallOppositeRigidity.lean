/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallOppositeRigidity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallOppositeRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallCentralizer
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnSmallOppositeRigidity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnSmallField
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F
open NikolovSegal.SLnFullGroup

theorem fixes_U_kernel_preimage [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F) (gamma : MulAut G)
    (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (hT : (T).map gamma.toMonoidHom=T)
    (r : PositiveIndex n) (d : G) (hd : d ∈ torusKernel (F := F) r) :
    ∃ e ∈ torusKernel (F := F) r, gamma e=d := by
  have hdT := ((mem_torusKernel_iff r d).mp hd).1
  rw [← hT] at hdT
  obtain ⟨e,he,hed⟩ := hdT
  change gamma e=d at hed
  refine ⟨e,(mem_torusKernel_iff r e).mpr ⟨he,?_⟩,hed⟩
  apply commute_transvection_diagonal e r.val.1 r.val.2 (ne_of_lt r.property)
  apply gamma.injective
  change gamma (e*root r 1)=gamma (root r 1*e)
  simp only [map_mul,hU (root r 1) (root_mem_Uplus r 1),hed]
  exact (fixed_torusKernel_iff (F := F) hn hF r (root r 1) (root_mem_Uplus r 1)).mpr ⟨1,rfl⟩ d hd

theorem fixes_negative_simple [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (gamma : MulAut G)
    (hU : ∀ x ∈ Uplus n F, gamma x=x)
    (hT : (T).map gamma.toMonoidHom=T)
    (r : PositiveIndex n) (hsimple : r.val.2.val=r.val.1.val+1) (t : F) :
    gamma (negativeRoot r t)=negativeRoot r t := by
  let g := negativeRoot r t
  let k := gamma g*g⁻¹
  have hK : ∀ d ∈ torusKernel (F := F) r, d*k=k*d := by
    intro d hd
    obtain ⟨e,he,hed⟩ := fixes_U_kernel_preimage hn hF gamma hU hT r d hd
    have hc : Commute d (gamma g) := by
      change d*gamma g=gamma g*d
      have hec := congrArg gamma (negativeRoot_commutes_kernel r t e he)
      simpa only [map_mul,hed,g] using hec
    have hdg : Commute d g := negativeRoot_commutes_kernel r t d hd
    exact (hc.mul_right hdg.inv_right).eq
  have hpos : ∀ s : PositiveIndex n, s ≠ r → k*root s 1=root s 1*k := by
    intro s hsr
    have hy : g⁻¹*root s 1*g ∈ Uplus n F := by
      simpa only [g,negativeRoot,SpecialLinearGroup.transvection_inv,inv_inv,neg_neg] using
        negative_simple_conjugate_mem_U r s hsimple hsr (-t) (1:F)
    have he : (gamma g)⁻¹*root s 1*gamma g = g⁻¹*root s 1*g := by
      simpa only [map_mul,map_inv,hU (root s 1) (root_mem_Uplus s 1)] using hU _ hy
    calc
      k*root s 1 = gamma g*(g⁻¹*root s 1*g)*g⁻¹ := by dsimp [k]; group
      _ = gamma g*((gamma g)⁻¹*root s 1*gamma g)*g⁻¹ := by rw [← he]
      _ = root s 1*k := by dsimp [k]; group
  have hk : k ∈ Subgroup.center G := simple_root_centralizer_is_center hn hF r hsimple k hK hpos
  have hgp : g^p=1 := transvection_pow_char p _ _ _ t
  have hgk : gamma g=k*g := by simp [k,mul_assoc]
  have hkg : Commute k g := (Subgroup.mem_center_iff.mp hk g).symm
  have hkp : k^p=1 := by
    have hp := congrArg gamma hgp
    rw [map_pow,map_one,hgk,hkg.mul_pow,hgp,mul_one] at hp
    exact hp
  have hk1 := center_p_torsion_eq_one p (by omega) k hk hkp
  simpa [hk1] using hgk

end NikolovSegal.SLnSmallField

