/- GID: D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ambient conjugation is transitive on actual minimal normal factors. -/

import D5.S3.FiniteGroups.NikolovSegal.MinimalNormalStructure

set_option autoImplicit false
namespace NikolovSegal
universe u
variable {G : Type u} [Group G]

/-- Ambient conjugates of a nontrivial subgroup of a minimal normal subgroup
join to that whole subgroup. The inner ambient action may permute its factors. -/
theorem conjugate_join_of_minimal_normal
    (N : Subgroup G) [N.Normal]
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (M : Subgroup N) (hMb : M ≠ ⊥) :
    (⨆ g : G, M.map (MulAut.conjNormal g).toMonoidHom) = ⊤ := by
  let C : Subgroup N := ⨆ g : G, M.map (MulAut.conjNormal g).toMonoidHom
  have hfix (g : G) : (C.map N.subtype).map (MulAut.conj g).toMonoidHom ≤
      C.map N.subtype := by
    dsimp only [C]
    simp only [Subgroup.map_iSup]
    apply iSup_le
    intro h
    apply le_iSup_of_le (g * h)
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    apply le_of_eq
    congr 1
    ext x
    simp [mul_assoc, MulAut.conjNormal_apply]
  have hn : (C.map N.subtype).Normal := by
    constructor
    intro a ha g
    exact hfix g (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  have hMle : M ≤ C := by
    apply le_iSup_of_le (1 : G)
    intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
  have hCb : C.map N.subtype ≠ ⊥ := by
    intro hb
    apply hMb
    have hc : C = ⊥ := by
      apply Subgroup.map_injective (f := N.subtype) Subtype.coe_injective
      simpa using hb
    exact le_bot_iff.mp (hMle.trans_eq hc)
  have hc := hN.eq_of_le ⟨hn, hCb⟩ (Subgroup.map_subtype_le C)
  apply Subgroup.map_injective (f := N.subtype) Subtype.coe_injective
  rw [← N.subtype.range_eq_map, N.range_subtype]
  exact hc

/-- Ambient conjugation acts transitively on the simple factors. In particular
one cannot use only an average factor-order bound in Proposition 2. -/
theorem minimal_normal_factors_conjugate [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (hna : ¬IsMulCommutative N) (M L : MinimalNormalFactor N) :
    ∃ g : G, M.val.map (MulAut.conjNormal g).toMonoidHom = L.val := by
  by_contra h
  push Not at h
  have hs := conjugate_join_of_minimal_normal N hN M.val M.property.prop.2
  have hcomm : (⊤ : Subgroup N) ≤ Subgroup.centralizer (L.val : Set N) := by
    rw [← hs]
    apply iSup_le
    intro g x hx y hy
    let M' : MinimalNormalFactor N :=
      ⟨M.val.map (MulAut.conjNormal g).toMonoidHom,
        minimal_normal_map_equiv M.property (MulAut.conjNormal g)⟩
    have hne : M' ≠ L := fun he => h g (congrArg Subtype.val he)
    exact (minimal_normal_factors_commute hne x y hx hy).symm.eq
  have hLcen : L.val ≤ Subgroup.center N := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro x
    exact (hcomm (Subgroup.mem_top x) y hy).symm
  have hz := (perfect_centerless_minimal_normal N hN hna).2
  exact L.property.prop.2 (le_bot_iff.mp (hLcen.trans_eq hz))

/-- All the factors have genuinely equal order, via actual group isomorphisms. -/
theorem minimal_normal_factors_isomorphic [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (hna : ¬IsMulCommutative N) (M L : MinimalNormalFactor N) :
    Nonempty (M.val ≃* L.val) := by
  obtain ⟨g, hg⟩ := minimal_normal_factors_conjugate N hN hna M L
  exact ⟨(M.val.equivMapOfInjective (MulAut.conjNormal g).toMonoidHom
      (MulAut.conjNormal g).injective).trans (MulEquiv.subgroupCongr hg)⟩

end NikolovSegal
