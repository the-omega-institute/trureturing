/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootPermutation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootPermutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootKernels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F

theorem exists_nonzero_upper_entry (g : G) (hg : g ∈ Uplus n F) (hne : g ≠ 1) :
    ∃ r : PositiveIndex n, g.val r.val.1 r.val.2 ≠ 0 := by
  classical
  by_contra h
  apply hne
  apply Subtype.ext
  ext i j
  by_cases he : i = j
  · subst j; simpa using hg.2 i
  · by_cases hij : i < j
    · have hz : g.val i j = 0 := by
        by_contra hn
        exact h ⟨⟨(i,j),hij⟩,hn⟩
      simp [hz, Matrix.one_apply, he]
    · have hji : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
        omega
      simp [hg.1 i j hji, Matrix.one_apply, he]

theorem rootSubgroup_injective : Function.Injective (rootSubgroup (n := n) (F := F)) := by
  intro r s h
  have hm : root r (1:F) ∈ rootSubgroup (F := F) s := h ▸ ⟨1,rfl⟩
  obtain ⟨t,ht⟩ := hm
  by_contra hne
  have hpair : ¬(s.val.1=r.val.1 ∧ s.val.2=r.val.2) := by
    rintro ⟨hi,hj⟩
    exact hne (Subtype.ext (Prod.ext hi hj)).symm
  have he := congrArg (fun g : G => g.val r.val.1 r.val.2) ht
  simp [root, SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, ne_of_lt r.property, hpair] at he

/-- An actual normalized bare automorphism maps EVERY positive root to a
literal positive root. The image is forced by a nonzero matrix entry and
the proved order of its whole torus kernel. -/
theorem normalized_root_image [Fintype F] (hn : 2 < n) (hF : 4 < Fintype.card F)
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
    have hc := (fixed_torusKernel_iff hF r (root r t) (root_mem_Uplus r t)).mpr ⟨t,rfl⟩ d hd
    simpa [map_mul] using congrArg alpha hc
  have hle : L ≤ torusKernel (F := F) s := by
    intro d hd
    apply (mem_torusKernel_iff s d).mpr
    refine ⟨hLT hd, ?_⟩
    have hc := (diagonal_commutes_iff d _ (hLT hd)).mp (hcomm 1 d hd) s.val.1 s.val.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hs)
  have hL : L = torusKernel (F := F) s := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, card_torusKernel_eq hn r s]
  have hrootle : (rootSubgroup r).map alpha.toMonoidHom ≤ rootSubgroup (F := F) s := by
    rintro z ⟨g,⟨t,rfl⟩,rfl⟩
    apply (fixed_torusKernel_iff hF s _ ?_).mp
    · intro d hd
      exact hcomm t d (hL.symm ▸ hd)
    · rw [← hU]
      exact Subgroup.mem_map_of_mem alpha.toMonoidHom (root_mem_Uplus r t)
  refine ⟨s, Subgroup.eq_of_le_of_card_ge hrootle ?_⟩
  rw [card_rootSubgroup, ← Nat.card_congr ((rootSubgroup r).equivMapOfInjective
    alpha.toMonoidHom alpha.injective).toEquiv, card_rootSubgroup]

theorem normalized_root_permutation [Fintype F] (hn : 2 < n) (hF : 4 < Fintype.card F)
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

private theorem root_coordinate_equiv (alpha : MulAut G) (r s : PositiveIndex n)
    (hmap : (rootSubgroup r).map alpha.toMonoidHom = rootSubgroup (F := F) s) :
    ∃ f : F ≃+ F, ∀ t, alpha (root r t) = root s (f t) := by
  classical
  have hm : ∀ t : F, alpha (root r t) ∈ rootSubgroup (F := F) s := by
    intro t
    rw [← hmap]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom ⟨t,rfl⟩
  choose f hf using hm
  have hi : Function.Injective f := by
    intro t u h
    apply root_injective r
    apply alpha.injective
    rw [← hf t, ← hf u, h]
  have hs : Function.Surjective f := by
    intro u
    have hm : root s u ∈ (rootSubgroup r).map alpha.toMonoidHom := by rw [hmap]; exact ⟨u,rfl⟩
    obtain ⟨g,⟨t,rfl⟩,ht⟩ := hm
    exact ⟨t, root_injective s ((hf t).trans ht)⟩
  have ha : ∀ t u, f (t+u) = f t+f u := by
    intro t u
    apply root_injective s
    rw [hf (t+u)]
    have hadd : ∀ (q : PositiveIndex n) (a b : F), root q (a+b) = root q a * root q b :=
      fun q a b => SpecialLinearGroup.transvection_add _ a b
    rw [hadd r, map_mul, ← hf t, ← hf u, ← hadd s]
  let h : F →+ F :=
    { toFun := f
      map_zero' := by
        have he : f 0+f 0 = f 0+0 := by simpa using (ha 0 0).symm
        exact add_left_cancel he
      map_add' := ha }
  exact ⟨AddEquiv.ofBijective h ⟨hi,hs⟩, fun t => (hf t).symm⟩

/-- Complete actual root-image/additive-coordinate branch, rank>=3 and
field size>4. Images and all additive equivalences are DERIVED from the bare
automorphism; field multiplication and graph/reflection are subsequent gaps. -/
theorem sl_bare_positive_root_coordinates [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F) (alpha : MulAut G) :
    ∃ c : G, ∃ sigma : Equiv.Perm (PositiveIndex n), ∃ f : PositiveIndex n → F ≃+ F,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (T).map beta.toMonoidHom = T ∧
      (∀ r, (rootSubgroup r).map beta.toMonoidHom = rootSubgroup (F := F) (sigma r)) ∧
      ∀ r t, beta (root r t) = root (sigma r) (f r t) := by
  classical
  obtain ⟨c,hU,hT,_,_,_,_⟩ := sl_inner_U_T_correction p n alpha
  obtain ⟨sigma,hs⟩ := normalized_root_permutation hn hF (MulAut.conj c * alpha) hU hT
  choose f hf using fun r => root_coordinate_equiv (MulAut.conj c * alpha) r (sigma r) (hs r)
  exact ⟨c,sigma,f,hU,hT,hs,hf⟩

end NikolovSegal.SLnRootAction
