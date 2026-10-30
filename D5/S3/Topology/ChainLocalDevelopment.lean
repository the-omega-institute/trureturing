/- GID: D5/S3/Topology/ChainLocalDevelopment
   generality: G
   mirror-B: D5/B/S3/Topology/ChainLocalDevelopment
   mirror-E: none(waiver:local-chain-development)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Isometry]
   utility: none
   digest: Local short developments across guarded faces bound the complete original chain distance. -/

import D5.S3.Topology.FiniteOrbitChainMetric

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal NNReal

namespace D5.S3.Topology.ChainLocalDevelopment

universe u v w z
variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)]
variable (G : FiniteOrbitChainMetric.Datum I J X)
variable {Y : Type z} [EMetricSpace Y]

private theorem short_chain_control (a : Sigma X) (f : Sigma X → Y)
    (hdesc : ∀ b c, G.Rel b c → f b = f c) (r : ℝ≥0∞)
    (hLip : ∀ i (c : X i), G.Rel a ⟨i,c⟩ → ∀ x y : X i,
      edist c x < r+r+r → edist c y < r+r+r →
      edist (f ⟨i,x⟩) (f ⟨i,y⟩) ≤ edist x y)
    (hF : ∀ j (c : X (G.src j)), G.Rel a ⟨G.src j,c⟩ →
      ∀ x : G.dom j, edist c x.val < r+r+r → c ∈ G.dom j)
    (hB : ∀ j (c : X (G.dst j)), G.Rel a ⟨G.dst j,c⟩ →
      ∀ x : G.ran j, edist c x.val < r+r+r → c ∈ G.ran j)
    {i : I} (c x : X i) (hc : G.Rel a ⟨i,c⟩) (hx : edist c x < r)
    {b : Sigma X} {t : ℝ≥0∞} (h : G.Chain ⟨i,x⟩ b t) (ht : t < r+r) :
    ∃ d : X b.1, G.Rel a ⟨b.1,d⟩ ∧ edist d b.2 ≤ edist c x+t ∧
      edist (f ⟨i,x⟩) (f b) ≤ t := by
  induction h with
  | nil => exact ⟨c, hc, by simp, by simp⟩
  | @move k y z t h ih =>
      have ht' : t < r+r := le_self_add.trans_lt ht
      obtain ⟨d, hd, hdy, hfy⟩ := ih ht'
      have hnear : edist d y < r+r+r := by
        apply hdy.trans_lt
        simpa only [add_assoc] using ENNReal.add_lt_add hx ht'
      have hdz : edist d z ≤ edist c x + (t + edist y z) := by
        exact (edist_triangle d y z).trans (by simpa only [add_assoc] using add_le_add hdy le_rfl)
      have hnearz : edist d z < r+r+r := by
        apply hdz.trans_lt
        simpa only [add_assoc] using ENNReal.add_lt_add hx ht
      refine ⟨d, hd, hdz, ?_⟩
      exact (edist_triangle (f ⟨i,x⟩) (f ⟨k,y⟩) (f ⟨k,z⟩)).trans
        (add_le_add hfy (hLip k d hd y z hnear hnearz))
  | @forward j y t h ih =>
      obtain ⟨d, hd, hdy, hfy⟩ := ih ht
      have hnear : edist d y.val < r+r+r := by
        apply hdy.trans_lt
        simpa only [add_assoc] using ENNReal.add_lt_add hx ht
      let d' : G.dom j := ⟨d, hF j d hd y hnear⟩
      have hdrel : G.Rel ⟨G.src j,d⟩ ⟨G.dst j,(G.iso j d').val⟩ :=
        Relation.EqvGen.rel _ _ ⟨j,d',rfl,rfl⟩
      have hyrel : G.Rel ⟨G.src j,y.val⟩ ⟨G.dst j,(G.iso j y).val⟩ :=
        Relation.EqvGen.rel _ _ ⟨j,y,rfl,rfl⟩
      refine ⟨(G.iso j d').val, Relation.EqvGen.trans _ _ _ hd hdrel, ?_, ?_⟩
      · change edist (G.iso j d') (G.iso j y) ≤ _
        rw [(G.iso j).isometry.edist_eq]
        exact hdy
      · rw [← hdesc _ _ hyrel]
        exact hfy
  | @backward j y t h ih =>
      obtain ⟨d, hd, hdy, hfy⟩ := ih ht
      have hnear : edist d y.val < r+r+r := by
        apply hdy.trans_lt
        simpa only [add_assoc] using ENNReal.add_lt_add hx ht
      let d' : G.ran j := ⟨d, hB j d hd y hnear⟩
      have hdrel : G.Rel ⟨G.dst j,d⟩ ⟨G.src j,((G.iso j).symm d').val⟩ := by
        apply Relation.EqvGen.symm
        apply Relation.EqvGen.rel
        refine ⟨j,(G.iso j).symm d',rfl,?_⟩
        simp [d']
      have hyrel : G.Rel ⟨G.dst j,y.val⟩ ⟨G.src j,((G.iso j).symm y).val⟩ := by
        apply Relation.EqvGen.symm
        apply Relation.EqvGen.rel
        refine ⟨j,(G.iso j).symm y,rfl,?_⟩
        simp
      refine ⟨((G.iso j).symm d').val, Relation.EqvGen.trans _ _ _ hd hdrel, ?_, ?_⟩
      · change edist ((G.iso j).symm d') ((G.iso j).symm y) ≤ _
        rw [(G.iso j).symm.isometry.edist_eq]
        exact hdy
      · rw [← hdesc _ _ hyrel]
        exact hfy

/-- A development that is short only in source balls around one complete orbit
is short for the original global chain distance on smaller orbit balls. -/
theorem local_development_distance_le (a : Sigma X) (f : Sigma X → Y)
    (hdesc : ∀ b c, G.Rel b c → f b = f c) (r : ℝ≥0) (hr : 0 < r)
    (hLip : ∀ i (c : X i), G.Rel a ⟨i,c⟩ → ∀ x y : X i,
      edist c x < (r : ℝ≥0∞)+r+r → edist c y < (r : ℝ≥0∞)+r+r →
      edist (f ⟨i,x⟩) (f ⟨i,y⟩) ≤ edist x y)
    (hF : ∀ j (c : X (G.src j)), G.Rel a ⟨G.src j,c⟩ →
      ∀ x : G.dom j, edist c x.val < (r : ℝ≥0∞)+r+r → c ∈ G.dom j)
    (hB : ∀ j (c : X (G.dst j)), G.Rel a ⟨G.dst j,c⟩ →
      ∀ x : G.ran j, edist c x.val < (r : ℝ≥0∞)+r+r → c ∈ G.ran j)
    (x y : Sigma X) (cx : X x.1) (cy : X y.1)
    (hcx : G.Rel a ⟨x.1,cx⟩) (hcy : G.Rel a ⟨y.1,cy⟩)
    (hx : edist cx x.2 < (r : ℝ≥0∞)) (hy : edist cy y.2 < (r : ℝ≥0∞)) :
    edist (f x) (f y) ≤ G.distance x y := by
  have hr' : (0 : ℝ≥0∞) < r := ENNReal.coe_pos.mpr hr
  have hsmall : (r : ℝ≥0∞) ≤ (r : ℝ≥0∞)+r+r :=
    le_self_add.trans le_self_add
  have hthree : (0 : ℝ≥0∞) < (r : ℝ≥0∞)+r+r := hr'.trans_le hsmall
  have hfx : edist (f a) (f x) < (r : ℝ≥0∞) := by
    rw [hdesc _ _ hcx]
    exact (hLip x.1 cx hcx cx x.2 (by simpa using hthree)
      (hx.trans_le hsmall)).trans_lt hx
  have hfy : edist (f a) (f y) < (r : ℝ≥0∞) := by
    rw [hdesc _ _ hcy]
    exact (hLip y.1 cy hcy cy y.2 (by simpa using hthree)
      (hy.trans_le hsmall)).trans_lt hy
  have hfxy : edist (f x) (f y) < (r : ℝ≥0∞)+r := by
    apply (edist_triangle (f x) (f a) (f y)).trans_lt
    simpa only [edist_comm] using ENNReal.add_lt_add hfx hfy
  apply le_iInf₂
  intro t ht
  by_contra hnot
  have hshort : t < edist (f x) (f y) := lt_of_not_ge hnot
  obtain ⟨d,hd,hdy,hbound⟩ := short_chain_control G a f hdesc r hLip hF hB
    cx x.2 hcx hx ht (hshort.trans hfxy)
  exact (not_lt_of_ge hbound) hshort

#print axioms local_development_distance_le
end D5.S3.Topology.ChainLocalDevelopment
