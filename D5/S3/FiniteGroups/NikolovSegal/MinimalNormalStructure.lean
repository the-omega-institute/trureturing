/- GID: D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite nonabelian minimal normal subgroups are internal products. -/

import D5.S3.FiniteGroups.NikolovSegal.MinimalNormalSocle
import D5.S3.FiniteGroups.NikolovSegal.FiniteNormalInduction

set_option autoImplicit false
namespace NikolovSegal
universe u
variable {G : Type u} [Group G]

/-- Minimal normality makes every characteristic subgroup internally trivial or full. -/
theorem characteristic_subgroup_of_minimal_normal
    (N : Subgroup G)
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (K : Subgroup N) [K.Characteristic] : K = ⊥ ∨ K = ⊤ := by
  let := hN.prop.1
  by_cases hb : K = ⊥
  · exact Or.inl hb
  · right
    have hn : (K.map N.subtype).Normal := inferInstance
    have hmb : K.map N.subtype ≠ ⊥ := by
      intro h
      apply hb
      apply Subgroup.map_injective (f := N.subtype) Subtype.coe_injective
      simpa using h
    have heq := hN.eq_of_le ⟨hn, hmb⟩ (Subgroup.map_subtype_le K)
    apply Subgroup.map_injective (f := N.subtype) Subtype.coe_injective
    rw [← N.subtype.range_eq_map, N.range_subtype]
    exact heq

/-- A nonabelian minimal normal subgroup is perfect and centerless. -/
theorem perfect_centerless_minimal_normal
    (N : Subgroup G)
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (hna : ¬IsMulCommutative N) :
    _root_.commutator N = ⊤ ∧ Subgroup.center N = ⊥ := by
  have hc := characteristic_subgroup_of_minimal_normal N hN (_root_.commutator N)
  have hz := characteristic_subgroup_of_minimal_normal N hN (Subgroup.center N)
  refine ⟨hc.resolve_left ?_, hz.resolve_right ?_⟩
  · exact fun h => hna ((_root_.commutator_eq_bot_iff N).mp h)
  · exact fun h => hna (Subgroup.center_eq_top_iff.mp h)

/-- The socle fills any finite minimal normal subgroup, including the abelian case.
The existing accepted finite minimal-normal existence theorem supplies a factor. -/
theorem socle_of_finite_minimal_normal [Finite G]
    (N : Subgroup G)
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N) :
    minimalNormalSocle N = ⊤ := by
  let : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.prop.2
  let : (minimalNormalSocle N).Characteristic := minimalNormalSocle_characteristic
  obtain ⟨L, hL⟩ := exists_minimal_normal (G := N)
  have hs := characteristic_subgroup_of_minimal_normal N hN (minimalNormalSocle N)
  apply hs.resolve_left
  intro hb
  apply hL.prop.2
  apply le_bot_iff.mp
  exact (le_iSup (fun M : MinimalNormalFactor N => M.val) ⟨L, hL⟩).trans_eq hb

/-- The canonical internal-product map is an isomorphism. Its injectivity uses
full supremum independence, not only pairwise disjointness. -/
noncomputable def socleProductEquiv [Finite G]
    (hs : minimalNormalSocle G = ⊤) (hz : Subgroup.center G = ⊥) :
    (∀ M : MinimalNormalFactor G, M.val) ≃* G := by
  let := Fintype.ofFinite (MinimalNormalFactor G)
  let f := Subgroup.noncommPiCoprod (minimal_normal_factors_commute (G := G))
  apply MulEquiv.ofBijective f
  constructor
  · exact Subgroup.injective_noncommPiCoprod_of_iSupIndep
      (minimal_normal_factors_independent hs hz)
  · apply MonoidHom.range_eq_top.mp
    exact (Subgroup.noncommPiCoprod_range).trans hs

/-- The full elementary nonabelian minimal-normal decomposition used before
Nikolov--Segal Proposition 2. This is an unconditional structure theorem for every
finite ambient group; it asserts no power-width or absorption conclusion. -/
theorem minimal_normal_nonabelian_direct_product [Finite G]
    (N : Subgroup G)
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (hna : ¬IsMulCommutative N) :
    _root_.commutator N = ⊤ ∧ Subgroup.center N = ⊥ ∧
      (∀ M : MinimalNormalFactor N, IsSimpleGroup M.val ∧ ¬IsMulCommutative M.val) ∧
      Nonempty ((∀ M : MinimalNormalFactor N, M.val) ≃* N) := by
  obtain ⟨hp, hz⟩ := perfect_centerless_minimal_normal N hN hna
  have hs := socle_of_finite_minimal_normal N hN
  refine ⟨hp, hz, ?_, ⟨socleProductEquiv hs hz⟩⟩
  intro M
  exact ⟨simple_minimal_normal_factor_of_socle_eq_top hs M,
    noncommutative_minimal_normal_factor_of_socle_eq_top hs hz M⟩

end NikolovSegal
