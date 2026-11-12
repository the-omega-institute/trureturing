/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/AllDendroid
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/AllDendroid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All standard dendroids obstruct finite positive expansivity. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.CoconnectedOpening
import D5.S1.Dynamics.Shadowing.DendriteObstruction.MinimalInvariant

/-! Classical static openings discharge the last premise of the dynamical obstruction. -/

open Set Function TopologicalSpace

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X]

private theorem standard_dendroid_paths (hX : StandardDendroid X) (c y : X) :
    ∃ α : ℝ → X, ContinuousOn α (Icc (0 : ℝ) 1) ∧ α 0 = c ∧ α 1 = y := by
  by_cases heq : c = y
  · exact ⟨fun _ => c, continuousOn_const, rfl, heq⟩
  · obtain ⟨A, h0, h1⟩ := hX.arcwise c y heq
    exact ⟨A.param, A.continuous, h0, h1⟩

/-- Actual arcwise connectedness and hereditary unicoherence imply the
classical small co-connected-opening law on every subcontinuum. -/
theorem StandardDendroid.smallCoconnectedOpenings [CompactSpace X]
    (hX : StandardDendroid X) : SmallCoconnectedOpenings X := by
  intro H hHc hHcon hHnt δ hδ
  let : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  have hstd : StandardDendroid H := hX.subcontinuum hHc hHcon
  have hnt : (univ : Set H).Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hHnt
    exact ⟨⟨a, ha⟩, mem_univ _, ⟨b, hb⟩, mem_univ _, fun h => hab (congrArg Subtype.val h)⟩
  obtain ⟨Q, hQc, hQcon, hQp, hQsmall⟩ := compact_path_small_opening
    (standard_dendroid_paths hstd) hnt hδ
  have hdiff : H \ (Subtype.val '' Q : Set X) = Subtype.val '' Qᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      intro hq
      exact hx.2 ⟨⟨x, hx.1⟩, hq, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      rintro ⟨y, hy, he⟩
      have : y = x := Subtype.ext he
      exact hx (this ▸ hy)
  refine ⟨Subtype.val '' Q, hQc.image continuous_subtype_val,
    hQcon.image _ continuous_subtype_val.continuousOn,
    (fun x hx => by obtain ⟨y, _, rfl⟩ := hx; exact y.2), ?_, ?_⟩
  · rw [hdiff]
    exact (Set.nonempty_compl.mpr hQp).image _
  · rw [hdiff, (show Isometry (Subtype.val : H → X) from fun _ _ => rfl).diam_image]
    exact hQsmall

/-- For every continuous self-map of every nondegenerate standard compact
metric dendroid, every positive scale admits any prescribed finite number of
distinct points whose image diameters stay strictly below that scale at all
natural times, including time zero. -/
theorem finite_small_orbits_of_standard_dendroid [CompactSpace X]
    (hX : StandardDendroid X) (hnt : (univ : Set X).Nontrivial)
    {f : X → X} (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : 2 ≤ m) :
    ∃ F : Finset X, F.card = m ∧
      ∀ n : ℕ, Metric.diam (f^[n] '' (F : Set X)) < ε := by
  exact finite_small_orbits_of_standard_dendroid_and_openings hX hnt
    hX.smallCoconnectedOpenings hf ε hε m hm

/-- No continuous self-map of a nondegenerate standard compact metric
dendroid is finitely positively expansive. -/
theorem not_finitelyPositiveExpansive_of_standard_dendroid [CompactSpace X]
    (hX : StandardDendroid X) (hnt : (univ : Set X).Nontrivial)
    {f : X → X} (hf : Continuous f) : ¬ FinitelyPositiveExpansive f := by
  exact not_finitelyPositiveExpansive_iff_finite_small_orbits.mpr
    (finite_small_orbits_of_standard_dendroid hX hnt hf)

end D5.S1.Dynamics.Shadowing.DendriteObstruction
