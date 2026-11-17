/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimal compact invariant sets retaining a nondegenerate continuum. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.CompactHistories
import D5.S1.Dynamics.Shadowing.DendriteObstruction.StandardDendroid
import Mathlib.Order.Zorn

/-! Continuum-preserving minimality and the tail-orbit obstruction. -/

open Set Function Filter
open scoped Topology
open TopologicalSpace

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

variable {X : Type*} [MetricSpace X]

/-- This class retains an actual nondegenerate continuum, without requiring
that the invariant compactum itself be connected. -/
def InvariantContinuumSet (f : X → X) (Y : Set X) : Prop :=
  IsCompact Y ∧ MapsTo f Y Y ∧
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ C.Nontrivial ∧ C ⊆ Y

/-- Zorn minimization in the class that retains a continuum, rather than in the
class of all nonempty invariant compacta. -/
theorem exists_minimal_invariant_continuum [CompactSpace X] {f : X → X}
    (hf : Continuous f) (hfin : FinitelyPositiveExpansive f) (hull : StaticArcHull X)
    (A : EmbeddedArc X) :
    ∃ Y : Set X, Minimal (InvariantContinuumSet f) Y := by
  classical
  obtain ⟨ε, hε, N, _, hB⟩ := hfin
  let a := ε / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have macroscopic : ∀ Y, InvariantContinuumSet f Y →
      ∃ K : NonemptyCompacts X,
        (IsConnected (K : Set X) ∧ a ≤ Metric.diam (K : Set X)) ∧ (K : Set X) ⊆ Y := by
    rintro Y ⟨_, hmap, C, hc, hcon, hnt, hCY⟩
    obtain ⟨n, _, hn⟩ := continuum_expands hf hε hB hull hc hcon hnt 0
    refine ⟨⟨⟨f^[n] '' C, hc.image (hf.iterate n)⟩, hcon.nonempty.image _⟩,
      ⟨hcon.image _ (hf.iterate n).continuousOn, ?_⟩,
      (image_mono hCY).trans (hmap.iterate n).image_subset⟩
    exact (by dsimp [a]; linarith : a ≤ ε).trans hn
  have hX : InvariantContinuumSet f univ :=
    ⟨isCompact_univ, mapsTo_univ f univ, A.carrier, A.compact, A.connected,
      A.infinite.nontrivial, subset_univ _⟩
  apply zorn_superset {Y | InvariantContinuumSet f Y}
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨univ, hX, by simp⟩
  let : Nonempty c := hne.to_subtype
  let S : c → Set (NonemptyCompacts X) := fun Y =>
    {K | (IsConnected (K : Set X) ∧ a ≤ Metric.diam (K : Set X)) ∧ (K : Set X) ⊆ Y.1}
  have hSc (Y : c) : IsCompact (S Y) :=
    compact_continua_ge_in a (hc Y.2).1.isClosed
  have hSn (Y : c) : (S Y).Nonempty := macroscopic Y.1 (hc Y.2)
  have hdir : Directed (· ⊇ ·) S := by
    intro Y Z
    rcases hchain.total Y.2 Z.2 with hYZ | hZY
    · exact ⟨Y, Subset.rfl, fun K hK => ⟨hK.1, hK.2.trans hYZ⟩⟩
    · exact ⟨Z, (fun K hK => ⟨hK.1, hK.2.trans hZY⟩), Subset.rfl⟩
  obtain ⟨K, hK⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hdir hSn hSc (fun Y => (hSc Y).isClosed)
  have hKS (Y : c) : K ∈ S Y := mem_iInter.mp hK Y
  obtain ⟨Y₀, hY₀⟩ := hne
  have hbase := (hKS ⟨Y₀, hY₀⟩).1
  have hKsub : (K : Set X) ⊆ ⋂₀ c := by
    intro x hx
    exact mem_sInter.mpr (fun Y hY => (hKS ⟨Y, hY⟩).2 hx)
  refine ⟨⋂₀ c, ⟨?_, ?_, (K : Set X), K.isCompact, hbase.1,
    nontrivial_of_diam_pos (ha.trans_le hbase.2), hKsub⟩, ?_⟩
  · exact (isClosed_sInter (fun Y hY => (hc hY).1.isClosed)).isCompact
  · intro x hx
    exact mem_sInter.mpr (fun Y hY => (hc hY).2.1 (mem_sInter.mp hx Y hY))
  · exact fun Y hY => sInter_subset_of_mem hY

/-- The closure of the rooted arc union is the least subcontinuum containing
an arbitrary nonempty set, which may be disconnected. -/
theorem exists_least_continuum [CompactSpace X] (hull : StaticArcHull X)
    {Y : Set X} (hY : Y.Nonempty) :
    ∃ H : Set X, IsCompact H ∧ IsConnected H ∧ Y ⊆ H ∧
      ∀ C : Set X, IsCompact C → IsConnected C → Y ⊆ C → H ⊆ C := by
  classical
  obtain ⟨y₀, hy₀⟩ := hY
  have paths : ∀ y : Y, ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ y₀ ∈ C ∧
      y.1 ∈ C ∧ ∀ D : Set X, IsCompact D → IsConnected D → Y ⊆ D → C ⊆ D := by
    intro y
    by_cases he : y₀ = y.1
    · refine ⟨{y₀}, isCompact_singleton, isConnected_singleton, rfl, he ▸ rfl, ?_⟩
      intro D _ _ hYD
      exact singleton_subset_iff.mpr (hYD hy₀)
    · obtain ⟨A, h0, h1, hA⟩ := hull y₀ y.1 he
      refine ⟨A.carrier, A.compact, A.connected, ?_, ?_, ?_⟩
      · rw [← h0]; exact mem_image_of_mem _ (by norm_num)
      · rw [← h1]; exact mem_image_of_mem _ (by norm_num)
      · intro D hc hcon hYD
        exact hA D hc hcon (hYD hy₀) (hYD y.2)
  choose C hCc hCcon h0 hy hleast using paths
  let V := ⋃ y : Y, C y
  have hyV : y₀ ∈ V := mem_iUnion.mpr ⟨⟨y₀, hy₀⟩, h0 _⟩
  have hV : IsPreconnected V := isPreconnected_iUnion
    ⟨y₀, mem_iInter.mpr h0⟩ (fun y => (hCcon y).isPreconnected)
  refine ⟨closure V, isClosed_closure.isCompact,
    ⟨⟨y₀, subset_closure hyV⟩, hV.closure⟩, ?_, ?_⟩
  · intro y hyY
    exact subset_closure (mem_iUnion.mpr ⟨⟨y, hyY⟩, hy _⟩)
  · intro D hc hcon hYD
    exact closure_minimal (iUnion_subset (fun y => hleast y D hc hcon hYD)) hc.isClosed

/-- The static small-opening conclusion used in the dendroid endgame.
The compact connected complement makes the opening relatively open in H.
This is separate from, and is not a field of, StandardDendroid. -/
def SmallCoconnectedOpenings (X : Type*) [MetricSpace X] : Prop :=
  ∀ H : Set X, IsCompact H → IsConnected H → H.Nontrivial →
    ∀ δ : ℝ, 0 < δ → ∃ Q : Set X,
      IsCompact Q ∧ IsConnected Q ∧ Q ⊆ H ∧
        (H \ Q).Nonempty ∧ Metric.diam (H \ Q) < δ

private theorem middle_third_eventually_in_complement [CompactSpace X] {f : X → X}
    (hf : Continuous f) (hull : StaticArcHull X)
    (K : EmbeddedArc X) (hK : ∀ n : ℕ, InjOn (f^[n]) K.carrier)
    {Y H Q : Set X} (hmap : MapsTo f Y Y) (hKY : K.carrier ⊆ Y) (hYH : Y ⊆ H)
    (hH : IsCompact H) (hQc : IsCompact Q) (hQcon : IsConnected Q)
    {δ : ℝ} (hsmall : Metric.diam (H \ Q) < δ)
    (hpersist : ∀ A : EmbeddedArc X, ∃ T : ℕ, ∀ n ≥ T,
      δ ≤ Metric.diam (f^[n] '' A.carrier)) :
    ∃ M : EmbeddedArc X, M.carrier ⊆ K.carrier ∧
      ∃ T : ℕ, ∀ n ≥ T, f^[n] '' M.carrier ⊆ Q := by
  let L := K.subarc (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 / 3 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1 / 3)
  let M := K.subarc (by norm_num : (1 / 3 : ℝ) ∈ Icc 0 1)
    (by norm_num : (2 / 3 : ℝ) ∈ Icc 0 1) (by norm_num : (1 / 3 : ℝ) < 2 / 3)
  let R := K.subarc (by norm_num : (2 / 3 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (2 / 3 : ℝ) < 1)
  have hLK : L.carrier ⊆ K.carrier := K.subarc_subset _ _ _
  have hMK : M.carrier ⊆ K.carrier := K.subarc_subset _ _ _
  have hRK : R.carrier ⊆ K.carrier := K.subarc_subset _ _ _
  obtain ⟨TL, hTL⟩ := hpersist L
  obtain ⟨TR, hTR⟩ := hpersist R
  refine ⟨M, hMK, max TL TR, fun n hn => ?_⟩
  have outside (A : EmbeddedArc X) (hAK : A.carrier ⊆ K.carrier)
      (hlarge : δ ≤ Metric.diam (f^[n] '' A.carrier)) :
      ∃ x ∈ A.carrier, f^[n] x ∈ Q := by
    by_contra! hno
    have hsub : f^[n] '' A.carrier ⊆ H \ Q := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hYH ((hmap.iterate n) (hKY (hAK hx))), hno x hx⟩
    exact (not_lt_of_ge (hlarge.trans (Metric.diam_mono hsub
      (hH.isBounded.subset sdiff_subset)))) hsmall
  obtain ⟨x, hxL, hxQ⟩ := outside L hLK (hTL n ((le_max_left _ _).trans hn))
  obtain ⟨y, hyR, hyQ⟩ := outside R hRK (hTR n ((le_max_right _ _).trans hn))
  rw [show L.carrier = K.param '' Icc 0 (1 / 3) from K.subarc_carrier _ _ _] at hxL
  rw [show R.carrier = K.param '' Icc (2 / 3) 1 from K.subarc_carrier _ _ _] at hyR
  obtain ⟨s, hs, rfl⟩ := hxL
  obtain ⟨t, ht, rfl⟩ := hyR
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hst : s < t := by linarith [hs.2, ht.1]
  let B : EmbeddedArc X := {
    param := fun u => f^[n] (K.param (s + (t - s) * u))
    continuous := (hf.iterate n).comp_continuousOn (K.subarc hs01 ht01 hst).continuous
    injective := by
      intro u hu v hv he
      apply (K.subarc hs01 ht01 hst).injective hu hv
      exact hK n (K.subarc_subset hs01 ht01 hst (mem_image_of_mem _ hu))
        (K.subarc_subset hs01 ht01 hst (mem_image_of_mem _ hv)) he }
  have hBQ : B.carrier ⊆ Q := B.subset_continuum hull hQc hQcon
    (by simpa [B] using hxQ) (by simpa [B] using hyQ)
  rintro z ⟨w, hw, rfl⟩
  rw [show M.carrier = K.param '' Icc (1 / 3) (2 / 3) from K.subarc_carrier _ _ _] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  apply hBQ
  refine ⟨(u - s) / (t - s), ?_, ?_⟩
  · constructor
    · exact div_nonneg (by linarith [hu.1, hs.2]) (by linarith)
    · exact (div_le_one (by linarith : 0 < t - s)).mpr (by linarith [hu.2, ht.1])
  · change f^[n] (K.param (s + (t - s) * ((u - s) / (t - s)))) = f^[n] (K.param u)
    congr 2
    field_simp
    <;> ring

/-- The tail-orbit contradiction uses only static small co-connected openings;
there is no uniform arc-packing premise. This does not assert that the opening
law has been derived from the standard dendroid definition. -/
theorem not_finitelyPositiveExpansive_of_coconnected_openings [CompactSpace X]
    {f : X → X} (hf : Continuous f) (hull : StaticArcHull X)
    (no_circle : ∀ g : AddCircle (1 : ℝ) → X, Continuous g → ¬ Injective g)
    (openings : SmallCoconnectedOpenings X) (A : EmbeddedArc X) :
    ¬ FinitelyPositiveExpansive f := by
  classical
  intro hfin
  obtain ⟨Y, hY, hminimal⟩ := exists_minimal_invariant_continuum hf hfin hull A
  obtain ⟨C, hc, hcon, hnt, hCY⟩ := hY.2.2
  obtain ⟨B, hBC⟩ := arc_in_continuum hull hc hcon hnt
  obtain ⟨K, hKY, hK⟩ := exists_iterate_injective_arc_invariant hf hfin hull no_circle
    hY.2.1 B (hBC.trans hCY)
  obtain ⟨H, hHc, hHcon, hYH, hleast⟩ := exists_least_continuum hull
    (hcon.nonempty.mono hCY)
  obtain ⟨δ, hδ, hpersist⟩ := eventual_arc_persistence hf hfin hull
  obtain ⟨Q, hQc, hQcon, hQH, hU, hsmall⟩ := openings H hHc hHcon
    (hnt.mono (hCY.trans hYH)) δ hδ
  have hYQ : ¬ Y ⊆ Q := by
    intro hsub
    have hHQ := hleast Q hQc hQcon hsub
    obtain ⟨x, hxH, hxQ⟩ := hU
    exact hxQ (hHQ hxH)
  obtain ⟨M, hMK, T, htail⟩ := middle_third_eventually_in_complement hf hull K hK
    hY.2.1 hKY hYH hHc hQc hQcon hsmall hpersist
  let V := ⋃ n : {n : ℕ // T ≤ n}, f^[n.1] '' M.carrier
  let Z := closure V
  have hVY : V ⊆ Y := by
    apply iUnion_subset
    intro n
    exact (image_mono (hMK.trans hKY)).trans (hY.2.1.iterate n.1).image_subset
  have hVQ : V ⊆ Q := iUnion_subset (fun n => htail n.1 n.2)
  have hZY : Z ⊆ Y := closure_minimal hVY hY.1.isClosed
  have hZQ : Z ⊆ Q := closure_minimal hVQ hQc.isClosed
  have hmapV : MapsTo f V V := by
    rintro x hx
    obtain ⟨n, w, hw, rfl⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨⟨n.1 + 1, by omega⟩, w, hw, ?_⟩
    simp only [Function.iterate_succ_apply']
  have hmapZ : MapsTo f Z Z := hmapV.closure_of_continuousOn hf.continuousOn
  have hMZ : f^[T] '' M.carrier ⊆ Z :=
    (subset_iUnion (fun n : {n : ℕ // T ≤ n} => f^[n.1] '' M.carrier)
      ⟨T, le_rfl⟩).trans subset_closure
  have hZM : InvariantContinuumSet f Z :=
    ⟨isClosed_closure.isCompact, hmapZ, f^[T] '' M.carrier,
      M.compact.image (hf.iterate T), M.connected.image _ (hf.iterate T).continuousOn,
      (M.infinite.image ((hK T).mono hMK)).nontrivial, hMZ⟩
  exact hYQ ((hminimal hZM hZY).trans hZQ)

/-- Negating finite positive expansivity gives arbitrary finite sets with a strict
joint diameter bound at every natural time, including time zero. -/
theorem not_finitelyPositiveExpansive_iff_finite_small_orbits {f : X → X} :
    (¬ FinitelyPositiveExpansive f) ↔
      ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, 2 ≤ m →
        ∃ F : Finset X, F.card = m ∧
          ∀ n : ℕ, Metric.diam (f^[n] '' (F : Set X)) < ε := by
  classical
  constructor
  · intro hnot ε hε m hm
    have hnb : ¬ ForwardBowenBound f univ (ε / 3) m :=
      fun hB => hnot ⟨ε / 3, by positivity, m, by omega, hB⟩
    simp only [ForwardBowenBound, mem_univ, forall_true_left, univ_inter, not_forall, not_le] at hnb
    obtain ⟨x, hx⟩ := hnb
    obtain ⟨v, hv, hi⟩ := (Set.le_encard_iff_exists_fin_injective _ m).mp hx.le
    let F := Finset.univ.image v
    refine ⟨F, by simp [F, Finset.card_image_of_injective _ hi], fun n => ?_⟩
    apply lt_of_le_of_lt (Metric.diam_le_of_forall_dist_le (by positivity : 0 ≤ 2 * (ε / 3)) ?_)
      (by linarith : 2 * (ε / 3) < ε)
    rintro u ⟨_, hu, rfl⟩ w ⟨_, hw, rfl⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    exact (dist_triangle_left _ _ (f^[n] x)).trans
      (by simpa only [two_mul] using add_le_add (hv i n).le (hv j n).le)
  · intro hsmall ⟨ε, hε, N, hN, hB⟩
    obtain ⟨F, hcard, hF⟩ := hsmall ε hε (N + 1) (by omega)
    have hne : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    have hsub : (F : Set X) ⊆ univ ∩ ForwardBowen f ε x := by
      intro y hy
      refine ⟨mem_univ _, fun n => ?_⟩
      exact (Metric.dist_le_diam_of_mem (F.finite_toSet.image _).isBounded
        (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)).trans_lt (hF n)
    have hle := (Set.encard_mono hsub).trans (hB x (mem_univ _))
    have hbad : (N + 1 : ℕ) ≤ N := by
      simpa only [Set.encard_coe_eq_coe_finsetCard, hcard, ENat.natCast_le_natCast] using hle
    omega

/-- The complete dynamic endgame on the faithful standard carrier, conditional
only on the remaining classical small co-connected-opening theorem. -/
theorem finite_small_orbits_of_standard_dendroid_and_openings [CompactSpace X]
    (hX : StandardDendroid X) (hnt : (univ : Set X).Nontrivial)
    (openings : SmallCoconnectedOpenings X) {f : X → X} (hf : Continuous f)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : 2 ≤ m) :
    ∃ F : Finset X, F.card = m ∧
      ∀ n : ℕ, Metric.diam (f^[n] '' (F : Set X)) < ε := by
  obtain ⟨x, _, y, _, hxy⟩ := hnt
  obtain ⟨A, _, _⟩ := hX.arcwise x y hxy
  exact not_finitelyPositiveExpansive_iff_finite_small_orbits.mp
    (not_finitelyPositiveExpansive_of_coconnected_openings hf hX.staticArcHull
      hX.no_circle openings A) ε hε m hm

end D5.S1.Dynamics.Shadowing.DendriteObstruction
