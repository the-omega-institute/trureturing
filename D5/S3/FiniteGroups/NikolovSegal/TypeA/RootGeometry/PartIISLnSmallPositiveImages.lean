/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallPositiveImages
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallPositiveImages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallTorus
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Genuine high-rank small-field root recognition. Only the rank/field-bound
parts are adapted from frozen accepted proofs; coordinate equivalences are
consumed directly from their unchanged private native declarations. -/
-- Direct consumption of the unchanged accepted native coordinate inferences.
macro "acceptedSLRootCoordinates%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootPermutation
    `NikolovSegal.SLnRootAction.root_coordinate_equiv))
macro "acceptedPSLRootCoordinates%" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnRootPermutation
    `NikolovSegal.PSLnRootAction.projective_coordinate_equiv))

namespace NikolovSegal.SLnSmallField
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F

theorem normalized_root_image [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom = Uplus n F)
    (hT : (T).map alpha.toMonoidHom = T) (r : PositiveIndex n) :
    ∃ s : PositiveIndex n, (rootSubgroup r).map alpha.toMonoidHom = rootSubgroup (F := F) s := by
  classical
  let L := (torusKernel (F := F) r).map alpha.toMonoidHom
  have hLT : L ≤ T := by
    rintro g ⟨k,hk,rfl⟩
    rw [← hT]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom ((mem_torusKernel_iff r k).mp hk).1
  have hcard : Nat.card L = Nat.card (torusKernel (F := F) r) :=
    (Nat.card_congr ((torusKernel (F := F) r).equivMapOfInjective alpha.toMonoidHom alpha.injective).toEquiv).symm
  have hu : alpha (root r 1) ∈ Uplus n F := by
    rw [← hU]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom (root_mem_Uplus r 1)
  have hne : alpha (root r (1:F)) ≠ 1 := by
    intro h
    have he : root r (1:F) = root r 0 := by
      apply alpha.injective
      simpa [root, SpecialLinearGroup.transvection_coeff_zero] using h
    exact one_ne_zero (root_injective r he)
  obtain ⟨s,hs⟩ := exists_nonzero_upper_entry _ hu hne
  have hcomm : ∀ t k, k ∈ L → k*alpha (root r t) = alpha (root r t)*k := by
    rintro t k ⟨d,hd,rfl⟩
    have hc := (fixed_torusKernel_iff hn hF r (root r t) (root_mem_Uplus r t)).mpr ⟨t,rfl⟩ d hd
    simpa [map_mul] using congrArg alpha hc
  have hle : L ≤ torusKernel (F := F) s := by
    intro d hd
    apply (mem_torusKernel_iff s d).mpr
    refine ⟨hLT hd, ?_⟩
    have hc := (diagonal_commutes_iff d _ (hLT hd)).mp (hcomm 1 d hd) s.val.1 s.val.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hs)
  have hL : L = torusKernel (F := F) s := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, card_torusKernel_eq (by omega) r s]
  have hrootle : (rootSubgroup r).map alpha.toMonoidHom ≤ rootSubgroup (F := F) s := by
    rintro z ⟨g,⟨t,rfl⟩,rfl⟩
    apply (fixed_torusKernel_iff hn hF s _ ?_).mp
    · intro d hd
      exact hcomm t d (hL.symm ▸ hd)
    · rw [← hU]
      exact Subgroup.mem_map_of_mem alpha.toMonoidHom (root_mem_Uplus r t)
  refine ⟨s, Subgroup.eq_of_le_of_card_ge hrootle ?_⟩
  rw [card_rootSubgroup, ← Nat.card_congr ((rootSubgroup r).equivMapOfInjective
    alpha.toMonoidHom alpha.injective).toEquiv, card_rootSubgroup]

theorem normalized_root_permutation [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut G) (hU : (Uplus n F).map alpha.toMonoidHom = Uplus n F)
    (hT : (T).map alpha.toMonoidHom = T) :
    ∃ sigma : Equiv.Perm (PositiveIndex n), ∀ r,
      (rootSubgroup r).map alpha.toMonoidHom = rootSubgroup (F := F) (sigma r) := by
  classical
  choose f hf using normalized_root_image hn hF alpha hU hT
  have hi : Function.Injective f := by
    intro r s h
    apply rootSubgroup_injective (F := F)
    apply Subgroup.map_injective (f := alpha.toMonoidHom) alpha.injective
    rw [hf r, hf s, h]
  exact ⟨Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩, hf⟩

theorem sl_bare_positive_root_coordinates [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (alpha : MulAut G) :
    ∃ c : G, ∃ sigma : Equiv.Perm (PositiveIndex n), ∃ f : PositiveIndex n → F ≃+ F,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (T).map beta.toMonoidHom = T ∧
      (∀ r, (rootSubgroup r).map beta.toMonoidHom = rootSubgroup (F := F) (sigma r)) ∧
      ∀ r t, beta (root r t) = root (sigma r) (f r t) := by
  classical
  obtain ⟨c,hU,hT,_,_,_,_⟩ := sl_inner_U_T_correction p n alpha
  obtain ⟨sigma,hs⟩ := normalized_root_permutation hn hF (MulAut.conj c * alpha) hU hT
  choose f hf using fun r => (acceptedSLRootCoordinates%) (MulAut.conj c * alpha) r (sigma r) (hs r)
  exact ⟨c,sigma,f,hU,hT,hs,hf⟩

end NikolovSegal.SLnSmallField

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

theorem normalized_projective_root_image [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut Q) (hU : (projectiveUplus n F).map alpha.toMonoidHom = projectiveUplus n F)
    (hT : (projectiveDiagonalTorus n F).map alpha.toMonoidHom = projectiveDiagonalTorus n F)
    (r : PositiveIndex n) : ∃ s : PositiveIndex n,
    (projectiveRoot r).map alpha.toMonoidHom = projectiveRoot (F := F) s := by
  classical
  let L := (((torusKernel (F := F) r).map π).map alpha.toMonoidHom).comap π
  have hLT : L ≤ T := by
    intro d hd
    have hm : π d ∈ (projectiveDiagonalTorus n F).map alpha.toMonoidHom :=
      (Subgroup.map_mono (Subgroup.map_mono (show torusKernel (F := F) r ≤ T from
        fun k hk => ((mem_torusKernel_iff r k).mp hk).1))) hd
    rw [hT] at hm
    have he := quotient_torus_preimage (n := n) (F := F)
    exact he ▸ hm
  have hcomm : ∀ t d, d ∈ L → π d * alpha (projectiveRootValue r t) =
      alpha (projectiveRootValue r t) * π d := by
    rintro t d ⟨z,⟨k,hk,rfl⟩,hz⟩
    have hc := (fixed_torusKernel_iff hn hF r (root r t) (root_mem_Uplus r t)).mpr ⟨t,rfl⟩ k hk
    have hp := congrArg (fun x : G => alpha (π x)) hc
    change alpha (π k) = π d at hz
    rw [← hz]
    simpa [projectiveRootValue, map_mul] using hp
  have hu : alpha (projectiveRootValue r 1) ∈ projectiveUplus n F := by
    rw [← hU]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom (Subgroup.mem_map_of_mem π (root_mem_Uplus r 1))
  obtain ⟨g,hg,hq⟩ := hu
  have hne : g ≠ 1 := by
    intro he
    have hp : alpha (projectiveRootValue r (1:F)) = alpha (projectiveRootValue r 0) := by
      rw [← hq, he]
      simp [projectiveRootValue, root]
    exact one_ne_zero (projectiveRootValue_injective r (alpha.injective hp))
  obtain ⟨s,hs⟩ := exists_nonzero_upper_entry g hg hne
  have hle : L ≤ torusKernel (F := F) s := by
    intro d hd
    apply (mem_torusKernel_iff s d).mpr
    refine ⟨hLT hd, ?_⟩
    have hc := hcomm 1 d hd
    rw [← hq] at hc
    have he := (diagonal_commutes_iff d g (hLT hd)).mp (lift_commutation d g hg hc) s.val.1 s.val.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hs)
  have hL : L = torusKernel (F := F) s := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_kernel_image_preimage, card_torusKernel_eq (by omega) r s]
  have hrootle : (projectiveRoot r).map alpha.toMonoidHom ≤ projectiveRoot (F := F) s := by
    rintro z ⟨x,hx,rfl⟩
    obtain ⟨t,rfl⟩ := (mem_projectiveRoot_iff r x).mp hx
    have hu : alpha (projectiveRootValue r t) ∈ projectiveUplus n F := by
      rw [← hU]
      exact Subgroup.mem_map_of_mem alpha.toMonoidHom (Subgroup.mem_map_of_mem π (root_mem_Uplus r t))
    obtain ⟨w,hw,hqw⟩ := hu
    have hwroot : w ∈ rootSubgroup (F := F) s := by
      apply (fixed_torusKernel_iff hn hF s w hw).mp
      intro d hd
      apply lift_commutation d w hw
      rw [hqw]
      exact hcomm t d (hL.symm ▸ hd)
    exact Subgroup.mem_map.mpr ⟨w,hwroot,hqw⟩
  refine ⟨s, Subgroup.eq_of_le_of_card_ge hrootle ?_⟩
  rw [card_projectiveRoot, ← Nat.card_congr ((projectiveRoot r).equivMapOfInjective
    alpha.toMonoidHom alpha.injective).toEquiv, card_projectiveRoot]

theorem normalized_projective_root_permutation [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut Q) (hU : (projectiveUplus n F).map alpha.toMonoidHom = projectiveUplus n F)
    (hT : (projectiveDiagonalTorus n F).map alpha.toMonoidHom = projectiveDiagonalTorus n F) :
    ∃ sigma : Equiv.Perm (PositiveIndex n), ∀ r,
      (projectiveRoot r).map alpha.toMonoidHom = projectiveRoot (F := F) (sigma r) := by
  classical
  choose f hf using normalized_projective_root_image hn hF alpha hU hT
  have hi : Function.Injective f := by
    intro r s h
    apply projectiveRoot_injective (F := F)
    apply Subgroup.map_injective (f := alpha.toMonoidHom) alpha.injective
    rw [hf r,hf s,h]
  exact ⟨Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,hf⟩

theorem psl_bare_positive_root_coordinates [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F) (alpha : MulAut Q) :
    ∃ c : Q, ∃ sigma : Equiv.Perm (PositiveIndex n), ∃ f : PositiveIndex n → F ≃+ F,
      let beta := MulAut.conj c * alpha
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom = projectiveDiagonalTorus n F ∧
      (∀ r, (projectiveRoot r).map beta.toMonoidHom = projectiveRoot (F := F) (sigma r)) ∧
      ∀ r t, beta (projectiveRootValue r t) = projectiveRootValue (sigma r) (f r t) := by
  classical
  obtain ⟨c,hU,hT,_,_,_,_⟩ := psl_inner_U_T_correction p n alpha
  obtain ⟨sigma,hs⟩ := normalized_projective_root_permutation hn hF (MulAut.conj c * alpha) hU hT
  choose f hf using fun r => (acceptedPSLRootCoordinates%) (MulAut.conj c * alpha) r (sigma r) (hs r)
  exact ⟨c,sigma,f,hU,hT,hs,hf⟩

end NikolovSegal.PSLnSmallField
