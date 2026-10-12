/- GID: D5/S1/Dynamics/Shadowing/EquicontinuousObstruction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/EquicontinuousObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prescribed-source lifting forces equicontinuous compact subsets to have a clopen basis. -/

import D5.S1.Dynamics.Shadowing.UniformTracing
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic

open TopologicalSpace Topology Set Function Filter UniformSpace
open scoped Uniformity

namespace D5.S1.Dynamics.Shadowing

private theorem clopen_cell_entourage {Y : Type*} [UniformSpace Y] [CompactSpace Y]
    (C : Set Y) (hC : IsClopen C) : (C ×ˢ C ∪ Cᶜ ×ˢ Cᶜ) ∈ 𝓤 Y := by
  rw [← nhdsSet_diagonal_eq_uniformity]
  apply ((hC.isOpen.prod hC.isOpen).union (hC.compl.isOpen.prod hC.compl.isOpen)).mem_nhdsSet.mpr
  rintro ⟨a, b⟩ hab
  have he : a = b := hab
  subst b
  by_cases ha : a ∈ C
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨ha, ha⟩

/-- Images of clopen observations are clopen on any compact forward-equicontinuous
subset. The restricted iterates have codomain X, with no invariance assumption. -/
theorem orbit_lifting_clopen_image {X Y : Type*} [UniformSpace X] [T2Space X]
    [UniformSpace Y] [CompactSpace Y] (p : Y → X) (g : Y → Y) (f : X → X)
    (hp : Continuous p) (he : Semiconj p g f) (hol : OrbitLifting p g f)
    (K : Set X) (hEq : UniformEquicontinuous (fun n (x : K) => f^[n] x.val))
    (C : Set Y) (hC : IsClopen C) :
    IsClopen {x : K | x.val ∈ p '' C} := by
  have hclosed : IsClosed (p '' C) := (hC.isClosed.isCompact.image hp).isClosed
  refine ⟨hclosed.preimage continuous_subtype_val, ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨a, ha, hpa⟩ := hx
  obtain ⟨V, hV, ht⟩ := hol _ (clopen_cell_entourage C hC)
  have hn := hEq.equicontinuous x V hV
  apply mem_of_superset hn
  intro x' hx'
  obtain ⟨b, hpb, hb⟩ := ht a x'.val (fun n => by
    rw [he.iterate_right n, hpa]
    exact hx' n)
  have hbC : b ∈ C := by
    have hh := hb 0
    change (b, a) ∈ C ×ˢ C ∪ Cᶜ ×ˢ Cᶜ at hh
    rcases hh with hh | hh
    · exact hh.1
    · exact (hh.2 ha).elim
  exact ⟨b, hbC, hpb⟩

/-- OL gives a clopen basis on every compact forward-equicontinuous subset of X.
The entire fibre is separated at once, rather than one chosen fibre point. -/
theorem orbit_lifting_clopen_basis {X Y : Type*} [UniformSpace X] [T2Space X]
    [UniformSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    (p : Y → X) (g : Y → Y) (f : X → X) (hp : Continuous p)
    (hsur : Surjective p) (he : Semiconj p g f) (hol : OrbitLifting p g f)
    (K : Set X) (hK : IsCompact K)
    (hEq : UniformEquicontinuous (fun n (x : K) => f^[n] x.val)) :
    IsTopologicalBasis {A : Set K | IsClopen A} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply isTopologicalBasis_of_isOpen_of_nhds (fun A hA => hA.isOpen)
  intro x U hxU hU
  let D : Set X := Subtype.val '' Uᶜ
  have hD : IsClosed D := (hU.isClosed_compl.isCompact.image continuous_subtype_val).isClosed
  have hfibre : IsClosed (p ⁻¹' {x.val}) := isClosed_singleton.preimage hp
  have havoid : p ⁻¹' {x.val} ⊆ (p ⁻¹' D)ᶜ := by
    intro a ha hbad
    obtain ⟨x', hx', heq⟩ := hbad
    have hxx : x' = x := Subtype.ext (heq.trans ha)
    exact hx' (hxx.symm ▸ hxU)
  obtain ⟨C, hC, hfC, hCD⟩ := exists_clopen_of_closed_subset_open hfibre
    (hD.preimage hp).isOpen_compl havoid
  let A : Set K := {x : K | x.val ∈ p '' C}
  refine ⟨A, orbit_lifting_clopen_image p g f hp he hol K hEq C hC, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hsur x.val
    exact ⟨a, hfC ha, ha⟩
  · rintro x' ⟨a, ha, hpa⟩
    by_contra hx'
    exact hCD ha ⟨x', hx', hpa.symm⟩

/-- A connected nondegenerate equicontinuous compact subset forbids OL, and
therefore forbids SR, for any compact Hausdorff zero-dimensional extension. -/
theorem connected_subset_not_source_relative {X Y : Type*}
    [UniformSpace X] [T2Space X] [UniformSpace Y] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y]
    (p : Y → X) (g : Y → Y) (f : X → X) (hp : Continuous p)
    (hsur : Surjective p) (he : Semiconj p g f)
    (K : Set X) (hK : IsCompact K) (hconn : IsPreconnected K)
    (hne : ∃ x y : K, x ≠ y)
    (hEq : UniformEquicontinuous (fun n (x : K) => f^[n] x.val)) :
    ¬ SourceRelativeTracing p g f := by
  intro hsr
  have hol : OrbitLifting p g f := by
    intro E hE
    obtain ⟨D, hD, V, hV, ht⟩ := hsr E hE
    refine ⟨V, hV, fun a x hx => ht (fun n => g^[n] a) x ?_ hx⟩
    intro n
    simpa only [iterate_succ_apply'] using (refl_mem_uniformity hD (x := g (g^[n] a)))
  have hb := orbit_lifting_clopen_basis p g f hp hsur he hol K hK hEq
  letI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hconn
  letI : TotallySeparatedSpace K := totallySeparatedSpace_of_t0_of_basis_clopen hb
  letI : TotallyDisconnectedSpace K := TotallySeparatedSpace.totallyDisconnectedSpace K
  obtain ⟨x, y, hxy⟩ := hne
  have hh := (isPreconnected_univ : IsPreconnected (univ : Set K)).subsingleton
  exact hxy (hh (mem_univ x) (mem_univ y))

/-- Forward equicontinuity makes every positively expansive factor locally constant
on K. The maps f^n|K still take their values in X. -/
theorem expansive_factor_locally_constant_on {X B : Type*} [UniformSpace X] [MetricSpace B]
    (π : X → B) (f : X → X) (d : B → B) (hp : UniformContinuous π)
    (he : Semiconj π f d) (hd : PositivelyExpansive d) (K : Set X)
    (hEq : UniformEquicontinuous (fun n (x : K) => f^[n] x.val)) :
    IsLocallyConstant (fun x : K => π x.val) := by
  obtain ⟨c, hc, hex⟩ := hd
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hV := hp (Metric.dist_mem_uniformity hc)
  apply mem_of_superset (hEq.equicontinuous x _ hV)
  intro y hy
  apply (hex (π x.val) (π y.val) (fun n => ?_)).symm
  rw [← he.iterate_right n, ← he.iterate_right n]
  exact hy n

/-- A connected equicontinuous subset cannot be separated by positively expansive
factors: each such factor is constant on that subset. -/
theorem expansive_factor_constant_on_connected {X B : Type*} [UniformSpace X] [MetricSpace B]
    (π : X → B) (f : X → X) (d : B → B) (hp : UniformContinuous π)
    (he : Semiconj π f d) (hd : PositivelyExpansive d) (K : Set X)
    (hconn : IsPreconnected K)
    (hEq : UniformEquicontinuous (fun n (x : K) => f^[n] x.val)) :
    ∀ x y : K, π x.val = π y.val := by
  letI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hconn
  exact (expansive_factor_locally_constant_on π f d hp he hd K hEq).apply_eq_of_preconnectedSpace

/-- One fixed clopen observation and one fixed exact orbit defeat every pair
of proposed controls. Failure already occurs at time zero in the exact fibre. -/
theorem connected_fixed_orbit_obstruction {X Y : Type*}
    [UniformSpace X] [T2Space X] [UniformSpace Y] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y]
    (p : Y → X) (g : Y → Y) (f : X → X) (hp : Continuous p)
    (hsur : Surjective p) (he : Semiconj p g f)
    (K : Set X) (hconn : IsPreconnected K)
    (hne : ∃ u v : K, u ≠ v)
    (hEq : UniformEquicontinuous (fun n (x : K) => f^[n] x.val)) :
    ∃ E ∈ 𝓤 Y, ∃ a : Y, ∀ D ∈ 𝓤 Y, ∀ V ∈ 𝓤 X, ∃ x : K,
      UniformPseudoOrbit g D (fun n => g^[n] a) ∧
      (∀ n, (p (g^[n] a), f^[n] x.val) ∈ V) ∧
      ¬ ∃ b : Y, p b = x.val ∧ ∀ n, (g^[n] b, g^[n] a) ∈ E := by
  classical
  letI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hconn
  obtain ⟨u, v, huv⟩ := hne
  have hf : IsClosed (p ⁻¹' {u.val}) := isClosed_singleton.preimage hp
  have ho : IsOpen (p ⁻¹' {v.val})ᶜ := (isClosed_singleton.preimage hp).isOpen_compl
  have hsub : p ⁻¹' {u.val} ⊆ (p ⁻¹' {v.val})ᶜ := by
    intro a hau hav
    exact huv (Subtype.ext (hau.symm.trans hav))
  obtain ⟨C, hC, huC, hvC⟩ := exists_clopen_of_closed_subset_open hf ho hsub
  let A : Set K := {x : K | x.val ∈ p '' C}
  have hAc : IsClosed A := (hC.isClosed.isCompact.image hp).isClosed.preimage continuous_subtype_val
  have huA : u ∈ A := by
    obtain ⟨a, ha⟩ := hsur u.val
    exact ⟨a, huC ha, ha⟩
  have hvA : v ∉ A := by
    rintro ⟨a, ha, hpa⟩
    exact hvC ha hpa
  have hAn : ¬ IsOpen A := by
    intro hAo
    have hAu := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ ⟨u, huA⟩
    exact hvA (hAu.symm ▸ mem_univ v)
  have hboundary : ∃ x ∈ A, A ∉ 𝓝 x := by
    by_contra hh
    push_neg at hh
    exact hAn (isOpen_iff_mem_nhds.mpr hh)
  obtain ⟨x, hxA, hxN⟩ := hboundary
  obtain ⟨a, haC, hpa⟩ := hxA
  refine ⟨C ×ˢ C ∪ Cᶜ ×ˢ Cᶜ, clopen_cell_entourage C hC, a, fun D hD V hV => ?_⟩
  let N : Set K := {y | ∀ n, (f^[n] x.val, f^[n] y.val) ∈ V}
  have hN : N ∈ 𝓝 x := hEq.equicontinuous x V hV
  have hnot : ¬ N ⊆ A := fun h => hxN (mem_of_superset hN h)
  obtain ⟨y, hyN, hyA⟩ := not_subset.mp hnot
  refine ⟨y, ?_, ?_, ?_⟩
  · intro n
    simpa only [iterate_succ_apply'] using (refl_mem_uniformity hD (x := g (g^[n] a)))
  · intro n
    rw [he.iterate_right n, hpa]
    exact hyN n
  · rintro ⟨b, hpb, hb⟩
    have hh := hb 0
    change (b, a) ∈ C ×ˢ C ∪ Cᶜ ×ˢ Cᶜ at hh
    rcases hh with hh | hh
    · exact hyA ⟨b, hh.1, hpb⟩
    · exact hh.2 haC

/-- The corrected geometric error estimate includes q=0 and the empty sum. -/
theorem contraction_pseudo_orbit_estimate {X : Type*} [MetricSpace X]
    (f : X → X) (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y)
    (δ : ℝ) (hδ : 0 ≤ δ) (a : ℕ → X)
    (ha : ∀ n, dist (f (a n)) (a (n + 1)) ≤ δ) (n : ℕ) :
    dist (f^[n] (a 0)) (a n) ≤ δ * ∑ j ∈ Finset.range n, q ^ j ∧
      δ * ∑ j ∈ Finset.range n, q ^ j ≤ δ / (1 - q) := by
  have hsum : ∀ n : ℕ, dist (f^[n] (a 0)) (a n) ≤ δ * ∑ j ∈ Finset.range n, q ^ j := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      have hstep : dist (f^[n+1] (a 0)) (a (n+1)) ≤
          q * dist (f^[n] (a 0)) (a n) + δ := by
        rw [iterate_succ_apply']
        exact (dist_triangle _ (f (a n)) _).trans (add_le_add (hf _ _) (ha n))
      have hmul := mul_le_mul_of_nonneg_left hn hq
      have hgeom := geom_sum_mul_neg q n
      rw [Finset.sum_range_succ]
      nlinarith
  refine ⟨hsum n, ?_⟩
  apply (le_div_iff₀ (sub_pos.mpr hqone)).mpr
  have hgeom := geom_sum_mul_neg q n
  have hp : 0 ≤ q ^ n := pow_nonneg hq n
  nlinarith

/-- A contraction has the actual finite-cover shadowing property on compact
metric spaces; the final comparison is strict, while the geometric bound is weak. -/
theorem contraction_hasShadowing {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → X) (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y) : HasShadowing f := by
  apply (cover_shadowing_iff_uniform f).mpr
  intro E hE
  obtain ⟨ε, hε, hεE⟩ := Metric.mem_uniformity_dist.mp hE
  let δ := (1 - q) * ε / 2
  have hδ : 0 < δ := div_pos (mul_pos (sub_pos.mpr hqone) hε) (by norm_num)
  refine ⟨{xy | dist xy.1 xy.2 < δ}, Metric.dist_mem_uniformity hδ, fun a ha => ⟨a 0, fun n => ?_⟩⟩
  apply hεE
  have h := contraction_pseudo_orbit_estimate f q hq hqone hf δ hδ.le a (fun n => (ha n).le) n
  have hfinal : δ / (1 - q) < ε := by
    apply (div_lt_iff₀ (sub_pos.mpr hqone)).mpr
    dsimp only [δ]
    nlinarith [mul_pos (sub_pos.mpr hqone) hε]
  exact (h.1.trans h.2).trans_lt hfinal

private theorem contraction_nonexpansive_iterate {X : Type*} [MetricSpace X]
    (f : X → X) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y) (n : ℕ) :
    ∀ x y, dist (f^[n] x) (f^[n] y) ≤ dist x y := by
  intro x y
  induction n with
  | zero => exact le_rfl
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (hf _ _).trans ((mul_le_mul_of_nonneg_left hn hq).trans
      (by simpa using mul_le_mul_of_nonneg_right hqone (dist_nonneg : 0 ≤ dist x y)))

/-- A connected nondegenerate compact metric contraction has shadowing but
no compact Hausdorff zero-dimensional extension can have prescribed-source SR. -/
theorem connected_contraction_shadowing_obstruction {X Y : Type*}
    [MetricSpace X] [CompactSpace X] [PreconnectedSpace X]
    [UniformSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    (f : X → X) (q : ℝ) (hq : 0 ≤ q) (hqone : q < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ q * dist x y)
    (hne : ∃ x y : X, x ≠ y) (p : Y → X) (g : Y → Y)
    (hp : Continuous p) (hsur : Surjective p) (he : Semiconj p g f) :
    HasShadowing f ∧ ¬ SourceRelativeTracing p g f := by
  refine ⟨contraction_hasShadowing f q hq hqone hf, ?_⟩
  apply connected_subset_not_source_relative p g f hp hsur he univ isCompact_univ isPreconnected_univ
  · obtain ⟨x, y, hxy⟩ := hne
    exact ⟨⟨x, mem_univ x⟩, ⟨y, mem_univ y⟩, fun h => hxy (congrArg Subtype.val h)⟩
  · intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
    have hV : {xy : ↥(univ : Set X) × ↥(univ : Set X) |
        dist xy.1.val xy.2.val < ε} ∈ 𝓤 ↥(univ : Set X) :=
      (uniformContinuous_subtype_val : UniformContinuous (Subtype.val : ↥(univ : Set X) → X))
        (Metric.dist_mem_uniformity hε)
    apply mem_of_superset hV
    intro xy hxy n
    exact hεU ((contraction_nonexpansive_iterate f q hq hqone.le hf n _ _).trans_lt hxy)

#print axioms orbit_lifting_clopen_image
#print axioms orbit_lifting_clopen_basis
#print axioms connected_subset_not_source_relative
#print axioms connected_fixed_orbit_obstruction
#print axioms expansive_factor_locally_constant_on
#print axioms expansive_factor_constant_on_connected
#print axioms contraction_pseudo_orbit_estimate
#print axioms contraction_hasShadowing
#print axioms connected_contraction_shadowing_obstruction

end D5.S1.Dynamics.Shadowing
