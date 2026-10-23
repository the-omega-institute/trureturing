/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnRootPermutation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnRootPermutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootPermutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.PSLnRootAction
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
open NikolovSegal.SLnRootAction
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)
local notation "T" => diagonalTorus n F

def projectiveRoot (r : PositiveIndex n) : Subgroup Q := (rootSubgroup (F := F) r).map π
def projectiveRootValue (r : PositiveIndex n) (t : F) : Q := π (root r t)

theorem quotient_injective_on_U (x y : G) (hx : x ∈ Uplus n F) (hy : y ∈ Uplus n F)
    (h : π x = π y) : x = y := by
  have he := conjugate_eq_of_quotient_eq (1:G) x y hx hy (by simpa using h)
  simpa using he

theorem projectiveRootValue_injective (r : PositiveIndex n) :
    Function.Injective (projectiveRootValue (F := F) r) := by
  intro t s h
  exact root_injective r (quotient_injective_on_U _ _ (root_mem_Uplus r t) (root_mem_Uplus r s) h)

theorem mem_projectiveRoot_iff (r : PositiveIndex n) (g : Q) :
    g ∈ projectiveRoot r ↔ ∃ t, projectiveRootValue (F := F) r t = g := by
  constructor
  · rintro ⟨x,⟨t,rfl⟩,rfl⟩; exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩; exact Subgroup.mem_map_of_mem π ⟨t,rfl⟩

theorem card_projectiveRoot (r : PositiveIndex n) : Nat.card (projectiveRoot (F := F) r) = Nat.card F := by
  let f : F → projectiveRoot (F := F) r :=
    fun t => ⟨projectiveRootValue r t, (mem_projectiveRoot_iff r _).mpr ⟨t,rfl⟩⟩
  have hi : Function.Injective f := fun _ _ h => projectiveRootValue_injective r (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨t,ht⟩ := (mem_projectiveRoot_iff r g.val).mp g.property
    exact ⟨t,Subtype.ext ht⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

theorem projectiveRoot_injective : Function.Injective (projectiveRoot (n := n) (F := F)) := by
  intro r s h
  have hm : projectiveRootValue r (1:F) ∈ projectiveRoot (F := F) s :=
    h ▸ (mem_projectiveRoot_iff r _).mpr ⟨1,rfl⟩
  obtain ⟨t,ht⟩ := (mem_projectiveRoot_iff s _).mp hm
  have he := quotient_injective_on_U _ _ (root_mem_Uplus s t) (root_mem_Uplus r 1) ht
  by_contra hne
  have hp : ¬(s.val.1=r.val.1 ∧ s.val.2=r.val.2) := by
    rintro ⟨hi,hj⟩; exact hne (Subtype.ext (Prod.ext hi hj)).symm
  have hc := congrArg (fun g : G => g.val r.val.1 r.val.2) he
  simp [root, SpecialLinearGroup.transvection_coe, ne_of_lt r.property, hp] at hc

theorem center_le_torusKernel (r : PositiveIndex n) : (π).ker ≤ torusKernel (F := F) r := by
  intro g hg
  apply (mem_torusKernel_iff r g).mpr
  refine ⟨center_le_torus hg, ?_⟩
  have hc : g ∈ Subgroup.center G := (QuotientGroup.eq_one_iff g).mp hg
  obtain ⟨z,_,he⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  rw [← he]
  simp

/-- The whole actual SL preimage of the projective kernel image has the
original kernel order. Native quotient indices retain the scalar center. -/
theorem card_kernel_image_preimage [Fintype F] (alpha : MulAut Q) (r : PositiveIndex n) :
    Nat.card ((((torusKernel (F := F) r).map π).map alpha.toMonoidHom).comap π) =
      Nat.card (torusKernel (F := F) r) := by
  let W := (((torusKernel (F := F) r).map π).map alpha.toMonoidHom).comap π
  have hi : W.index = (torusKernel (F := F) r).index := by
    dsimp only [W]
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hb : (((torusKernel (F := F) r).map π).map alpha.toMonoidHom).index =
        ((torusKernel (F := F) r).map π).index := Subgroup.index_map_equiv _ alpha
    rw [hb]
    exact Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (center_le_torusKernel r)
  apply (mul_left_inj' (torusKernel (F := F) r).index_ne_zero_of_finite).mp
  calc
    Nat.card W*(torusKernel (F := F) r).index = Nat.card W*W.index := by rw [hi]
    _ = Nat.card G := W.card_mul_index
    _ = Nat.card (torusKernel (F := F) r)*(torusKernel (F := F) r).index :=
      (torusKernel (F := F) r).card_mul_index.symm

theorem quotient_torus_preimage : ((T).map π).comap π = T := by
  rw [Subgroup.comap_map_eq, sup_of_le_left (center_le_torus (n := n) (F := F))]

theorem lift_commutation (d g : G) (hg : g ∈ Uplus n F) (h : π d * π g = π g * π d) : d*g = g*d := by
  have hp : π (d*g*d⁻¹) = π g := by
    simpa only [map_mul, map_inv, mul_assoc, mul_inv_cancel, mul_one] using
      congrArg (fun x : Q => x * (π d)⁻¹) h
  have he := conjugate_eq_of_quotient_eq d g g hg hg hp
  simpa [mul_assoc] using congrArg (fun x : G => x*d) he

/-- EVERY projective positive root image is derived intrinsically, without
lifting the automorphism: representatives, scalar-center cancellation and
the full preimage kernel order force its actual SL root coordinate. -/
theorem normalized_projective_root_image [Fintype F] (hn : 2 < n) (hF : 4 < Fintype.card F)
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
    have hc := (fixed_torusKernel_iff hF r (root r t) (root_mem_Uplus r t)).mpr ⟨t,rfl⟩ k hk
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
    rw [card_kernel_image_preimage, card_torusKernel_eq hn r s]
  have hrootle : (projectiveRoot r).map alpha.toMonoidHom ≤ projectiveRoot (F := F) s := by
    rintro z ⟨x,hx,rfl⟩
    obtain ⟨t,rfl⟩ := (mem_projectiveRoot_iff r x).mp hx
    have hu : alpha (projectiveRootValue r t) ∈ projectiveUplus n F := by
      rw [← hU]
      exact Subgroup.mem_map_of_mem alpha.toMonoidHom (Subgroup.mem_map_of_mem π (root_mem_Uplus r t))
    obtain ⟨w,hw,hqw⟩ := hu
    have hwroot : w ∈ rootSubgroup (F := F) s := by
      apply (fixed_torusKernel_iff hF s w hw).mp
      intro d hd
      apply lift_commutation d w hw
      rw [hqw]
      exact hcomm t d (hL.symm ▸ hd)
    exact Subgroup.mem_map.mpr ⟨w,hwroot,hqw⟩
  refine ⟨s, Subgroup.eq_of_le_of_card_ge hrootle ?_⟩
  rw [card_projectiveRoot, ← Nat.card_congr ((projectiveRoot r).equivMapOfInjective
    alpha.toMonoidHom alpha.injective).toEquiv, card_projectiveRoot]

theorem normalized_projective_root_permutation [Fintype F] (hn : 2 < n) (hF : 4 < Fintype.card F)
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

private theorem projective_coordinate_equiv (alpha : MulAut Q) (r s : PositiveIndex n)
    (hmap : (projectiveRoot r).map alpha.toMonoidHom = projectiveRoot (F := F) s) :
    ∃ f : F ≃+ F, ∀ t, alpha (projectiveRootValue r t) = projectiveRootValue s (f t) := by
  classical
  have hm : ∀ t, ∃ u, projectiveRootValue s u = alpha (projectiveRootValue r t) := by
    intro t
    apply (mem_projectiveRoot_iff s _).mp
    rw [← hmap]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom ((mem_projectiveRoot_iff r _).mpr ⟨t,rfl⟩)
  choose f hf using hm
  have hi : Function.Injective f := by
    intro t u h
    apply projectiveRootValue_injective r
    apply alpha.injective
    rw [← hf t, ← hf u, h]
  have hs : Function.Surjective f := by
    intro u
    have hm : projectiveRootValue s u ∈ (projectiveRoot r).map alpha.toMonoidHom := by
      rw [hmap]; exact (mem_projectiveRoot_iff s _).mpr ⟨u,rfl⟩
    obtain ⟨g,hg,he⟩ := hm
    obtain ⟨t,rfl⟩ := (mem_projectiveRoot_iff r g).mp hg
    exact ⟨t, projectiveRootValue_injective s ((hf t).trans he)⟩
  have hadd : ∀ (q : PositiveIndex n) (a b : F), projectiveRootValue q (a+b) =
      projectiveRootValue q a * projectiveRootValue q b := by
    intro q a b
    change π (SpecialLinearGroup.transvection _ (a+b)) = _
    rw [SpecialLinearGroup.transvection_add, map_mul]
    rfl
  have ha : ∀ t u, f (t+u) = f t+f u := by
    intro t u
    apply projectiveRootValue_injective s
    rw [hf (t+u), hadd r, map_mul, ← hf t, ← hf u, ← hadd s]
  let h : F →+ F :=
    { toFun := f
      map_zero' := by
        have he : f 0+f 0 = f 0+0 := by simpa using (ha 0 0).symm
        exact add_left_cancel he
      map_add' := ha }
  exact ⟨AddEquiv.ofBijective h ⟨hi,hs⟩,fun t => (hf t).symm⟩

/-- Actual all-positive-root coordinate branch for arbitrary bare PSLn
automorphisms, rank>=3 and field size>4, without an SL automorphism lift. -/
theorem psl_bare_positive_root_coordinates [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F) (alpha : MulAut Q) :
    ∃ c : Q, ∃ sigma : Equiv.Perm (PositiveIndex n), ∃ f : PositiveIndex n → F ≃+ F,
      let beta := MulAut.conj c * alpha
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom = projectiveDiagonalTorus n F ∧
      (∀ r, (projectiveRoot r).map beta.toMonoidHom = projectiveRoot (F := F) (sigma r)) ∧
      ∀ r t, beta (projectiveRootValue r t) = projectiveRootValue (sigma r) (f r t) := by
  classical
  obtain ⟨c,hU,hT,_,_,_,_⟩ := psl_inner_U_T_correction p n alpha
  obtain ⟨sigma,hs⟩ := normalized_projective_root_permutation hn hF (MulAut.conj c * alpha) hU hT
  choose f hf using fun r => projective_coordinate_equiv (MulAut.conj c * alpha) r (sigma r) (hs r)
  exact ⟨c,sigma,f,hU,hT,hs,hf⟩

end NikolovSegal.PSLnRootAction
