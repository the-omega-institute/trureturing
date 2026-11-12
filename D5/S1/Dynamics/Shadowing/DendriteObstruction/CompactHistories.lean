/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attained compact-history multiplicity and injective iterate arcs. -/

import D5.S1.Dynamics.Shadowing.DendriteObstruction.ShortLoops
import D5.S1.Dynamics.Shadowing.IntervalObstruction.Basic
import Mathlib.Topology.Sets.VietorisTopology

/-! Actual compact histories retain complete terminal fibres and every prefix time. -/

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

/-- An actual nondegenerate embedded closed unit interval. -/
structure EmbeddedArc (X : Type*) [TopologicalSpace X] where
  param : ℝ → X
  continuous : ContinuousOn param (Icc 0 1)
  injective : InjOn param (Icc 0 1)

namespace EmbeddedArc

variable {X : Type*} [MetricSpace X]

def carrier (A : EmbeddedArc X) : Set X := A.param '' Icc 0 1

private theorem compact (A : EmbeddedArc X) : IsCompact A.carrier :=
  isCompact_Icc.image_of_continuousOn A.continuous

private theorem connected (A : EmbeddedArc X) : IsConnected A.carrier :=
  (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image A.param A.continuous

private theorem infinite (A : EmbeddedArc X) : A.carrier.Infinite :=
  (Icc_infinite (by norm_num : (0 : ℝ) < 1)).image A.injective

private theorem affine_mem {a b u : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) (hu : u ∈ Icc (0 : ℝ) 1) :
    a + (b - a) * u ∈ Icc (0 : ℝ) 1 := by
  constructor <;> nlinarith [ha.1, hb.2, hu.1, hu.2]

/-- Affine restriction to a genuine closed subinterval. -/
private def subarc (A : EmbeddedArc X) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) :
    EmbeddedArc X where
  param u := A.param (a + (b - a) * u)
  continuous := A.continuous.comp
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    (fun _ hu => affine_mem ha hb hab hu)
  injective := by
    intro u hu v hv he
    have := A.injective (affine_mem ha hb hab hu) (affine_mem ha hb hab hv) he
    nlinarith

private theorem subarc_carrier (A : EmbeddedArc X) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) :
    (A.subarc ha hb hab).carrier = A.param '' Icc a b := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨a + (b - a) * u, ?_, rfl⟩
    constructor <;> nlinarith [hu.1, hu.2]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(u - a) / (b - a), ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hu.1) (by linarith)
      · exact (div_le_one (by linarith : 0 < b - a)).mpr (by linarith [hu.2])
    · change A.param (a + (b - a) * ((u - a) / (b - a))) = A.param u
      congr 1
      field_simp
      <;> ring

private theorem subarc_subset (A : EmbeddedArc X) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) :
    (A.subarc ha hb hab).carrier ⊆ A.carrier := by
  rw [subarc_carrier]
  exact image_mono (fun _ hu => ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩)

private theorem small_subarc (A : EmbeddedArc X) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : EmbeddedArc X, B.carrier ⊆ A.carrier ∧
      ∀ x ∈ B.carrier, ∀ y ∈ B.carrier, dist x y < ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous A.continuous) ε hε
  let b := min (δ / 2) (1 / 2)
  have hb : 0 < b := lt_min (by positivity) (by norm_num)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let B := A.subarc (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨hb.le, hb1⟩ hb
  refine ⟨B, A.subarc_subset _ _ _, ?_⟩
  intro x hx y hy
  rw [show B.carrier = A.param '' Icc 0 b from A.subarc_carrier _ _ _] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  apply hd s ⟨hs.1, hs.2.trans hb1⟩ t ⟨ht.1, ht.2.trans hb1⟩
  rw [Real.dist_eq]
  have hbd : b ≤ δ / 2 := min_le_left _ _
  exact abs_lt.mpr ⟨by linarith [hs.1, ht.2], by linarith [ht.1, hs.2]⟩

end EmbeddedArc

variable {X : Type*} [MetricSpace X]

/-- Purely static arc hulls: the same chosen arc lies in every subcontinuum
containing its endpoints. No dynamical condition is included. -/
def StaticArcHull (X : Type*) [MetricSpace X] : Prop :=
  ∀ p y : X, p ≠ y → ∃ A : EmbeddedArc X,
    A.param 0 = p ∧ A.param 1 = y ∧
    ∀ C : Set X, IsCompact C → IsConnected C → p ∈ C → y ∈ C → A.carrier ⊆ C

/-- All source points are retained; the source compactum need not be connected. -/
structure CompactHistory (f : X → X) (ε : ℝ) (r : ℕ) where
  source : Set X
  compact : IsCompact source
  nonempty : source.Nonempty
  time : ℕ
  terminal : EmbeddedArc X
  onto : f^[time] '' source = terminal.carrier
  small : ∀ j ≤ time, ∀ x ∈ source, ∀ y ∈ source,
    dist (f^[j] x) (f^[j] y) < ε
  multiplicity : ∀ w ∈ terminal.carrier,
    (r : ℕ∞) ≤ (source ∩ (f^[time]) ⁻¹' {w}).encard

private theorem initial_history {f : X → X} {ε : ℝ} (hε : 0 < ε)
    (A : EmbeddedArc X) : Nonempty (CompactHistory f ε 1) := by
  obtain ⟨B, _, hsmall⟩ := A.small_subarc hε
  refine ⟨⟨B.carrier, B.compact, B.connected.nonempty, 0, B, by simp, ?_, ?_⟩⟩
  · intro j hj x hx y hy
    have : j = 0 := by omega
    subst j
    exact hsmall x hx y hy
  · intro w hw
    apply (Set.le_encard_iff_exists_fin_injective _ 1).mpr
    refine ⟨fun _ => w, fun _ => ⟨hw, rfl⟩, ?_⟩
    intro i j _
    exact Subsingleton.elim _ _

private theorem history_bound {f : X → X} {ε : ℝ} {N r : ℕ}
    (hε : 0 < ε) (hB : ForwardBowenBound f univ ε N) (H : CompactHistory f ε r) :
    r ≤ N := by
  by_contra hn
  obtain ⟨w, hw⟩ := H.terminal.connected.nonempty
  obtain ⟨v, hv, hi⟩ := (Set.le_encard_iff_exists_fin_injective _ r).mp (H.multiplicity w hw)
  apply IntervalObstruction.no_coalescing_witnesses hB hε (by omega) v hi
    (fun _ => mem_univ _)
  · exact fun i j t ht => H.small t ht _ (hv i).1 _ (hv j).1
  · exact fun i j => (hv i).2.trans (hv j).2.symm

private theorem attained_maximum {f : X → X} {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hB : ForwardBowenBound f univ ε N) (A : EmbeddedArc X) :
    ∃ r : ℕ, 1 ≤ r ∧ Nonempty (CompactHistory f ε r) ∧
      ∀ s : ℕ, Nonempty (CompactHistory f ε s) → s ≤ r := by
  classical
  let S := {r : ℕ | Nonempty (CompactHistory f ε r)}
  have hS : Set.Finite S := (finite_Iic N).subset (fun r hr => history_bound hε hB hr.some)
  have h1 : 1 ∈ S := initial_history hε A
  obtain ⟨r, hr, hmax⟩ := hS.toFinset.exists_max_image id ⟨1, hS.mem_toFinset.mpr h1⟩
  exact ⟨r, hmax 1 (hS.mem_toFinset.mpr h1), hS.mem_toFinset.mp hr,
    fun s hs => hmax s (hS.mem_toFinset.mpr hs)⟩

private theorem compact_double_cover [CompactSpace X] {f : X → X} {ε : ℝ}
    (hf : Continuous f) (hε : 0 < ε) {N : ℕ}
    (hB : ForwardBowenBound f univ ε N)
    (hull : StaticArcHull X)
    (no_circle : ∀ g : AddCircle (1 : ℝ) → X, Continuous g → ¬ Injective g)
    (A : EmbeddedArc X) (q : ℕ) (hn : ¬ InjOn (f^[q]) A.carrier) :
    ∃ B : EmbeddedArc X, ∃ P Q : Set X,
      IsCompact P ∧ IsCompact Q ∧ Disjoint P Q ∧
      P ∪ Q ⊆ A.carrier ∧ f^[q] '' P = B.carrier ∧ f^[q] '' Q = B.carrier ∧
      ∀ j ≤ q, ∀ x ∈ P ∪ Q, ∀ y ∈ P ∪ Q,
        dist (f^[j] x) (f^[j] y) < ε := by
  classical
  have hnparam : ¬ InjOn (fun u => f^[q] (A.param u)) (Icc 0 1) := by
    intro hi
    apply hn
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ he
    exact congrArg A.param (hi hs ht he)
  obtain ⟨a, ha, b, hb, hab, he, hsmall⟩ :=
    short_repeated_pair_finite_prefix no_circle hf A.continuous q hnparam hε
  have habsub : Icc a b ⊆ Icc (0 : ℝ) 1 :=
    fun _ hu => ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
  have hinf : (A.param '' Icc a b).Infinite :=
    (Icc_infinite hab).image (A.injective.mono habsub)
  have hfib := IntervalObstruction.finite_fibres isCompact_univ hB hε
  have himg := IntervalObstruction.infinite_iterate_image (mapsTo_univ f univ)
    hfib (subset_univ _) hinf q
  have hnot : ¬ f^[q] '' (A.param '' Icc a b) ⊆ {f^[q] (A.param a)} :=
    fun h => himg ((finite_singleton _).subset h)
  obtain ⟨y, hy, hyp⟩ := Set.not_subset.mp hnot
  obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hy
  have hcp : f^[q] (A.param c) ≠ f^[q] (A.param a) := hyp
  have hac : a < c := lt_of_le_of_ne hc.1 (fun h => hcp (by rw [← h]))
  have hcb : c < b := lt_of_le_of_ne hc.2 (fun h => hcp (by rw [h, ← he]))
  obtain ⟨D, hD0, hD1, hD⟩ := hull (f^[q] (A.param a)) (f^[q] (A.param c)) hcp.symm
  let B := D.subarc (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1 / 2)
  have hBD : B.carrier ⊆ D.carrier := D.subarc_subset _ _ _
  have hyB : f^[q] (A.param c) ∉ B.carrier := by
    intro hy
    rw [show B.carrier = D.param '' Icc 0 (1 / 2) from D.subarc_carrier _ _ _] at hy
    obtain ⟨u, hu, heu⟩ := hy
    have := D.injective ⟨hu.1, by linarith [hu.2]⟩ (by norm_num : (1 : ℝ) ∈ Icc 0 1)
      (heu.trans hD1.symm)
    linarith [hu.2]
  let L := A.param '' Icc a c
  let R := A.param '' Icc c b
  have hLsub : Icc a c ⊆ Icc (0 : ℝ) 1 := fun _ hu => habsub ⟨hu.1, hu.2.trans hc.2⟩
  have hRsub : Icc c b ⊆ Icc (0 : ℝ) 1 := fun _ hu => habsub ⟨hc.1.trans hu.1, hu.2⟩
  have hLc : IsCompact L := isCompact_Icc.image_of_continuousOn (A.continuous.mono hLsub)
  have hRc : IsCompact R := isCompact_Icc.image_of_continuousOn (A.continuous.mono hRsub)
  have hLcon : IsConnected L :=
    (isConnected_Icc hac.le).image A.param (A.continuous.mono hLsub)
  have hRcon : IsConnected R :=
    (isConnected_Icc hcb.le).image A.param (A.continuous.mono hRsub)
  have hBL : B.carrier ⊆ f^[q] '' L := hBD.trans
    (hD _ (hLc.image (hf.iterate q)) (hLcon.image _ (hf.iterate q).continuousOn)
      ⟨_, ⟨a, left_mem_Icc.mpr hac.le, rfl⟩, rfl⟩
      ⟨_, ⟨c, right_mem_Icc.mpr hac.le, rfl⟩, rfl⟩)
  have hBR : B.carrier ⊆ f^[q] '' R := hBD.trans
    (hD _ (hRc.image (hf.iterate q)) (hRcon.image _ (hf.iterate q).continuousOn)
      ⟨_, ⟨b, right_mem_Icc.mpr hcb.le, rfl⟩, he.symm⟩
      ⟨_, ⟨c, left_mem_Icc.mpr hcb.le, rfl⟩, rfl⟩)
  let P := L ∩ (f^[q]) ⁻¹' B.carrier
  let Q := R ∩ (f^[q]) ⁻¹' B.carrier
  have hPQsub : P ∪ Q ⊆ A.param '' Icc a b := by
    rintro x (hx | hx)
    · exact image_mono (show Icc a c ⊆ Icc a b from fun _ hu => ⟨hu.1, hu.2.trans hc.2⟩) hx.1
    · exact image_mono (show Icc c b ⊆ Icc a b from fun _ hu => ⟨hc.1.trans hu.1, hu.2⟩) hx.1
  refine ⟨B, P, Q,
    hLc.inter_right (B.compact.isClosed.preimage (hf.iterate q)),
    hRc.inter_right (B.compact.isClosed.preimage (hf.iterate q)), ?_,
    hPQsub.trans (image_mono habsub), ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxP hxQ
    obtain ⟨u, hu, hux⟩ := hxP.1
    obtain ⟨v, hv, hvx⟩ := hxQ.1
    have huv := A.injective (hLsub hu) (hRsub hv) (hux.trans hvx.symm)
    have huc : u = c := by linarith [hu.2, hv.1]
    apply hyB
    have hxc : x = A.param c := by rw [← hux, huc]
    simpa only [mem_preimage, hxc] using hxP.2
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro w hw
      obtain ⟨v, hv, heq⟩ := hBL hw
      exact ⟨v, ⟨hv, by change f^[q] v ∈ B.carrier; rw [heq]; exact hw⟩, heq⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro w hw
      obtain ⟨v, hv, heq⟩ := hBR hw
      exact ⟨v, ⟨hv, by change f^[q] v ∈ B.carrier; rw [heq]; exact hw⟩, heq⟩
  · intro j hj x hx y hy
    obtain ⟨s, hs, rfl⟩ := hPQsub hx
    obtain ⟨t, ht, rfl⟩ := hPQsub hy
    exact hsmall j hj s hs t ht

private theorem extend_double_history {f : X → X} (hf : Continuous f) {ε : ℝ} {r : ℕ}
    (H : CompactHistory f ε r) (q : ℕ) (B : EmbeddedArc X) (P Q : Set X)
    (hPc : IsCompact P) (hQc : IsCompact Q) (hPQ : Disjoint P Q)
    (hsub : P ∪ Q ⊆ H.terminal.carrier)
    (hP : f^[q] '' P = B.carrier) (hQ : f^[q] '' Q = B.carrier)
    (hsmall : ∀ j ≤ q, ∀ x ∈ P ∪ Q, ∀ y ∈ P ∪ Q,
      dist (f^[j] x) (f^[j] y) < ε) : Nonempty (CompactHistory f ε (2 * r)) := by
  classical
  let E := H.source ∩ (f^[H.time]) ⁻¹' (P ∪ Q)
  have hE : E ⊆ H.source := inter_subset_left
  have hmid : f^[H.time] '' E = P ∪ Q := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro v hv
      obtain ⟨x, hx, he⟩ := H.onto.symm ▸ hsub hv
      exact ⟨x, ⟨hx, by change f^[H.time] x ∈ P ∪ Q; rw [he]; exact hv⟩, he⟩
  have honto : f^[H.time + q] '' E = B.carrier := by
    rw [Nat.add_comm H.time q, Function.iterate_add, image_comp, hmid, image_union, hP, hQ,
      union_self]
  have hne : E.Nonempty := by
    have := B.connected.nonempty
    rw [← honto] at this
    exact this.of_image
  refine ⟨⟨E, H.compact.inter_right
    ((hPc.union hQc).isClosed.preimage (hf.iterate H.time)), hne,
    H.time + q, B, honto, ?_, ?_⟩⟩
  · intro k hk x hx y hy
    by_cases hkt : k ≤ H.time
    · exact H.small k hkt x (hE hx) y (hE hy)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : H.time ≤ k)
      rw [Nat.add_comm H.time j, Function.iterate_add_apply, Function.iterate_add_apply]
      exact hsmall j (by omega) _ hx.2 _ hy.2
  · intro w hw
    obtain ⟨v, hvP, hvw⟩ := hP.symm ▸ hw
    obtain ⟨u, huQ, huw⟩ := hQ.symm ▸ hw
    have hvK := hsub (Or.inl hvP)
    have huK := hsub (Or.inr huQ)
    have hvu : v ≠ u := by
      intro he
      exact Set.disjoint_left.mp hPQ hvP (he ▸ huQ)
    let V := H.source ∩ (f^[H.time]) ⁻¹' {v}
    let U := H.source ∩ (f^[H.time]) ⁻¹' {u}
    have hVU : Disjoint V U := by
      apply Set.disjoint_left.mpr
      intro x hxV hxU
      exact hvu (hxV.2.symm.trans hxU.2)
    have hVUsub : V ∪ U ⊆ E ∩ (f^[H.time + q]) ⁻¹' {w} := by
      rintro x (hx | hx)
      · refine ⟨⟨hx.1, ?_⟩, ?_⟩
        · change f^[H.time] x ∈ P ∪ Q
          rw [hx.2]; exact Or.inl hvP
        · change f^[H.time + q] x = w
          rw [Nat.add_comm H.time q, Function.iterate_add_apply, hx.2, hvw]
      · refine ⟨⟨hx.1, ?_⟩, ?_⟩
        · change f^[H.time] x ∈ P ∪ Q
          rw [hx.2]; exact Or.inr huQ
        · change f^[H.time + q] x = w
          rw [Nat.add_comm H.time q, Function.iterate_add_apply, hx.2, huw]
    calc
      ((2 * r : ℕ) : ℕ∞) = (r : ℕ∞) + (r : ℕ∞) := by simp [two_mul]
      _ ≤ V.encard + U.encard := add_le_add (H.multiplicity v hvK) (H.multiplicity u huK)
      _ = (V ∪ U).encard := (Set.encard_union_eq hVU).symm
      _ ≤ _ := Set.encard_mono hVUsub

/-- Finite positive expansivity and static dendroid geometry force an actual
nondegenerate arc on which every natural iterate is injective. -/
theorem exists_iterate_injective_arc [CompactSpace X] {f : X → X}
    (hf : Continuous f) (hfin : FinitelyPositiveExpansive f)
    (hull : StaticArcHull X)
    (no_circle : ∀ g : AddCircle (1 : ℝ) → X, Continuous g → ¬ Injective g)
    (A : EmbeddedArc X) :
    ∃ K : EmbeddedArc X, ∀ n : ℕ, InjOn (f^[n]) K.carrier := by
  classical
  obtain ⟨ε, hε, N, _, hB⟩ := hfin
  obtain ⟨r, hr, ⟨H⟩, hmax⟩ := attained_maximum hε hB A
  refine ⟨H.terminal, fun q => ?_⟩
  by_contra hn
  obtain ⟨B, P, Q, hPc, hQc, hPQ, hsub, hP, hQ, hs⟩ :=
    compact_double_cover hf hε hB hull no_circle H.terminal q hn
  have hd := hmax (2 * r) (extend_double_history hf H q B P Q hPc hQc hPQ hsub hP hQ hs)
  omega

end D5.S1.Dynamics.Shadowing.DendriteObstruction
