import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneTwoHighSignsProbe

/-! An obstruction for balanced 21-point slices in Hong, Wu and Xia's
[Problem 2](https://arxiv.org/html/2610.09483v1#Thmproblem2).

Compression of degree-two paths leaves two possible bipartite degree profiles.
The four-high side is excluded by the signed cube geometry of its matched theta
graphs. For the two-high side, the signed eight-cycle fixes each core label.
Equal arm directions give a midpoint obstruction. Distinct directions give a
coordinate grid whose compressed edges would have to change both labels by
triangle-freeness. They would then have Hamming distance four. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
open GirthSliceCounting (degreeTwo)
open private diff from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_injective diff_triangle_card compressed_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private SideHigh compressed compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private matched_core_arm_label from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneTwoHighSignsProbe
open private two_high_core_shape twenty_one_slice_remaining_case from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneTwoHighProbe
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
attribute [local instance] Classical.propDecidable

private lemma no_compressed_core_grid
    {V : Type*} {n : ℕ}
    (f : V → Q n) (hf : Function.Injective f) (x : Q n) (b : Fin n)
    (K : SimpleGraph V) (U W C : Finset V) (hW : W.card = 2)
    (d c : V → Fin n)
    (hd : Set.InjOn d (U : Set V)) (hc : Set.InjOn c (W : Set V))
    (hbd : ∀ u ∈ U, b ≠ d u) (hbc : ∀ w ∈ W, b ≠ c w)
    (htriangle : ∀ p q r, K.Adj p q → K.Adj q r → K.Adj r p → False)
    (hrow : ∀ u ∈ U, ∃ v ∈ C, ∃ z ∈ C, v ≠ z ∧ K.Adj v u ∧ K.Adj z u)
    (hcol : ∀ v ∈ C, ∃ w ∈ W, K.Adj v w)
    (hlabel : ∀ v ∈ C, ∀ u ∈ U, ∀ w ∈ W, K.Adj v u → K.Adj v w →
      d u ≠ c w ∧ diff (f v) x = {b, c w, d u})
    (v z u u' w w' : V)
    (hv : v ∈ C) (hz : z ∈ C) (hu : u ∈ U) (hu' : u' ∈ U)
    (hw : w ∈ W) (hw' : w' ∈ W)
    (hvu : K.Adj v u) (hzu : K.Adj z u')
    (hvw : K.Adj v w) (hzw : K.Adj z w')
    (hvz : K.Adj v z) (hdist : hammingDist (f v) (f z) = 2) : False := by
  classical
  have hcross (p : V) (hp : p ∈ U) (q : V) (hq : q ∈ W) : d p ≠ c q := by
    intro he
    obtain ⟨v₁, hv₁, v₂, hv₂, hne, h₁p, h₂p⟩ := hrow p hp
    obtain ⟨q₁, hq₁, h₁q⟩ := hcol v₁ hv₁
    obtain ⟨q₂, hq₂, h₂q⟩ := hcol v₂ hv₂
    have l₁ := hlabel v₁ hv₁ p hp q₁ hq₁ h₁p h₁q
    have l₂ := hlabel v₂ hv₂ p hp q₂ hq₂ h₂p h₂q
    have h₁ : q₁ ≠ q := fun h => l₁.1 (h ▸ he)
    have h₂ : q₂ ≠ q := fun h => l₂.1 (h ▸ he)
    have hsingle : (W.erase q).card ≤ 1 := by rw [card_erase_of_mem hq, hW]
    have hq₁₂ : q₁ = q₂ :=
      Finset.card_le_one.mp hsingle q₁ (mem_erase.mpr ⟨h₁, hq₁⟩)
        q₂ (mem_erase.mpr ⟨h₂, hq₂⟩)
    exact hne (hf (diff_injective x (l₁.2.trans (hq₁₂ ▸ l₂.2.symm))))
  have hdd : d u ≠ d u' := by
    intro he
    have huu : u = u' := hd hu hu' he
    exact htriangle v z u hvz (huu ▸ hzu) hvu.symm
  have hcc : c w ≠ c w' := by
    intro he
    have hww : w = w' := hc hw hw' he
    exact htriangle v z w hvz (hww ▸ hzw) hvw.symm
  have lv := hlabel v hv u hu w hw hvu hvw
  have lz := hlabel z hz u' hu' w' hw' hzu hzw
  have hud := hcross u hu w' hw'
  have hcw := hcross u' hu' w hw
  have hbcu := hbc w hw
  have hbdw := hbd u hu
  have hbcu' := hbc w' hw'
  have hbdw' := hbd u' hu'
  have hi : ({b, c w, d u} : Finset (Fin n)) ∩ {b, c w', d u'} = {b} := by
    ext i
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, h⟩
      · rfl
      · rcases h with h | h | h
        · exact h
        · exact (hcc h).elim
        · exact (hcw h.symm).elim
      · rcases h with h | h | h
        · exact h
        · exact (hud h).elim
        · exact (hdd h).elim
    · intro h
      exact ⟨Or.inl h, Or.inl h⟩
  have h := diff_triangle_card (f v) (f z) x
  change hammingDist (f v) (f z) + 2 * _ = _ at h
  rw [hdist, lv.2, lz.2, hi] at h
  simp [hbcu, hbdw, hbcu', hbdw', lv.1.symm, lz.1.symm] at h

#print axioms no_compressed_core_grid

set_option maxHeartbeats 800000 in
private lemma two_high_slice_impossible
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (hp : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ ⦃v w⦄, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (hL : Fintype.card (SideHigh ((hypercube n).induce (S : Set (Q n))) L) = 2)
    (hR : Fintype.card (SideHigh ((hypercube n).induce (S : Set (Q n))) R) = 8)
    (he : (compressed ((hypercube n).induce (S : Set (Q n))) L).edgeFinset.card = 1) :
    False := by
  classical
  let G := (hypercube n).induce (S : Set (Q n))
  let K := compressed G R
  let V := SideHigh G R
  have hg := BalancedCubeGirth.eight_le_egirth S hb
  obtain ⟨x, y, hxy, hU, hW, hUW, hC, hrows, hcore⟩ :=
    two_high_core_shape hp hdeg (fun h hx hy => hlow h hx hy) hg hL hR he
  let U : Finset V := univ.filter fun u => G.Adj x.val u.val
  let W : Finset V := univ.filter fun w => G.Adj y.val w.val
  let C : Finset V := univ \ (U ∪ W)
  obtain ⟨hxy, m, hm2, hxm, hym⟩ := hxy
  obtain ⟨a, hm⟩ := adjacent_exists_flip (show (hypercube n).Adj x.val.val m.val from hxm)
  obtain ⟨b, hy⟩ := adjacent_exists_flip (show (hypercube n).Adj m.val y.val.val from hym.symm)
  have hab : a ≠ b := by
    intro h
    apply hxy
    apply Subtype.ext
    apply Subtype.ext
    rw [hy, hm, ← h, BalancedCriticalSpectrum.flip_flip]
  have uAdj (u : V) (hu : u ∈ U) : G.Adj x.val u.val := (mem_filter.mp hu).2
  have wAdj (w : V) (hw : w ∈ W) : G.Adj y.val w.val := (mem_filter.mp hw).2
  have uDir (u : V) : ∃ j : Fin n, u ∈ U → u.val.val = flip x.val.val j := by
    by_cases hu : u ∈ U
    · obtain ⟨j, hj⟩ := adjacent_exists_flip
        (show (hypercube n).Adj x.val.val u.val.val from uAdj u hu)
      exact ⟨j, fun _ => hj⟩
    · exact ⟨a, fun h => (hu h).elim⟩
  have wDir (w : V) : ∃ j : Fin n, w ∈ W → w.val.val = flip y.val.val j := by
    by_cases hw : w ∈ W
    · obtain ⟨j, hj⟩ := adjacent_exists_flip
        (show (hypercube n).Adj y.val.val w.val.val from wAdj w hw)
      exact ⟨j, fun _ => hj⟩
    · exact ⟨b, fun h => (hw h).elim⟩
  choose d hd using uDir
  choose c hc using wDir
  have ne_mid (u : V) : u.val.val ≠ m.val := by
    intro h
    have he' : u.val = m := Subtype.ext h
    have hu3 : G.degree u.val = 3 := (mem_filter.mp u.property).2
    change G.degree m = 2 at hm2
    rw [he', hm2] at hu3
    omega
  have huw (u : V) (hu : u ∈ U) (w : V) (hw : w ∈ W) : u ≠ w :=
    fun e => (Finset.disjoint_left.mp hUW) hu (e.symm ▸ hw)
  have outU (u : V) (hu : u ∈ U) : a ≠ d u ∧ b ≠ d u := by
    constructor
    · intro h
      exact ne_mid u ((hd u hu).trans (h ▸ hm.symm))
    · intro h
      have h₁ : u.val.val = flip x.val.val b := h.symm ▸ hd u hu
      have h₂ : y.val.val = flip u.val.val a := by
        rw [hy, hm, h₁, flip_comm x.val.val a b]
      have hAdj : G.Adj y.val u.val := by
        change (hypercube n).Adj y.val.val u.val.val
        rw [h₂]
        exact (BalancedCriticalSpectrum.flip_adj _ _).symm
      exact huw u hu u (mem_filter.mpr ⟨mem_univ _, hAdj⟩) rfl
  have outW (w : V) (hw : w ∈ W) : a ≠ c w ∧ b ≠ c w := by
    constructor
    · intro h
      have h₁ : w.val.val = flip y.val.val a := h.symm ▸ hc w hw
      have h₂ : w.val.val = flip x.val.val b := by
        rw [h₁, hy, hm, flip_comm (flip x.val.val a) b a,
          BalancedCriticalSpectrum.flip_flip]
      have hAdj : G.Adj x.val w.val := by
        change (hypercube n).Adj x.val.val w.val.val
        rw [h₂]
        exact BalancedCriticalSpectrum.flip_adj _ _
      exact huw w (mem_filter.mpr ⟨mem_univ _, hAdj⟩) w hw rfl
    · intro h
      have h₁ : w.val.val = flip y.val.val b := h.symm ▸ hc w hw
      have h₂ : w.val.val = m.val := by rw [h₁, hy, BalancedCriticalSpectrum.flip_flip]
      exact ne_mid w h₂
  have val_inj : Function.Injective (fun u : V => u.val.val) :=
    fun _ _ e => Subtype.ext (Subtype.ext e)
  have dih : Set.InjOn d (U : Set V) := by
    intro u hu z hz h
    apply val_inj
    change u.val.val = z.val.val
    rw [hd u hu, hd z hz, h]
  have cih : Set.InjOn c (W : Set V) := by
    intro w hw z hz h
    apply val_inj
    change w.val.val = z.val.val
    rw [hc w hw, hc z hz, h]
  have coreU (v : V) (hv : v ∈ C) : ∃ u ∈ U, K.Adj v u :=
    (hcore v hv).1.exists
  have coreW (v : V) (hv : v ∈ C) : ∃ w ∈ W, K.Adj v w :=
    (hcore v hv).2.1.exists
  have mate (v : V) (hv : v ∈ C) : ∃ z ∈ C, K.Adj v z :=
    (hcore v hv).2.2.exists
  have labels (v : V) (hv : v ∈ C) (u : V) (hu : u ∈ U) (w : V) (hw : w ∈ W)
      (hvu : K.Adj v u) (hvw : K.Adj v w) :
      d u ≠ c w ∧ diff v.val.val x.val.val = {b, c w, d u} := by
    obtain ⟨z, hz, hvz⟩ := mate v hv
    obtain ⟨u', hu', hzu⟩ := coreU z hz
    obtain ⟨w', hw', hzw⟩ := coreW z hz
    have huz : u ≠ z := fun e => (mem_sdiff.mp hz).2 (mem_union_left _ (e ▸ hu))
    exact matched_core_arm_label hb hp x y hxy m hm2 hxm hym hlow hab hm hy
      (huw u hu w hw) (huw u' hu' w' hw') huz
      (uAdj u hu) (wAdj w hw) (uAdj u' hu') (wAdj w' hw')
      hvu hvw hzu hzw hvz (hc w hw) (hd u hu) (hc w' hw') (hd u' hu')
      (outW w hw).1 (outW w' hw').1 (outU u' hu').1 (outW w' hw').2 (outU u' hu').2
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < C.card from by rw [show C.card = 4 from hC]; decide)
  obtain ⟨z, hz, hvz⟩ := mate v hv
  obtain ⟨u, hu, hvu⟩ := coreU v hv
  obtain ⟨u', hu', hzu⟩ := coreU z hz
  obtain ⟨w, hw, hvw⟩ := coreW v hv
  obtain ⟨w', hw', hzw⟩ := coreW z hz
  exact no_compressed_core_grid (fun u : V => u.val.val) val_inj x.val.val b K U W C hW
    d c dih cih (fun _ h => (outU _ h).2) (fun _ h => (outW _ h).2)
    (compressed_triangle_free hp.symm hg) hrows coreW labels
    v z u u' w w' hv hz hu hu' hw hw' hvu hzu hvw hzw hvz (compressed_distance hvz)

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- The 21-point coordinate half required by the small-half case of a
66-vertex Huang-balanced cubic support cannot occur. -/
theorem no_balanced_twenty_one_slice
    (S : Finset (Q 9)) (hS : S.card = 21) (hb : IsBalanced S)
    (hdeg : ∀ v, ((hypercube 9).induce (S : Set (Q 9))).degree v = 2 ∨
      ((hypercube 9).induce (S : Set (Q 9))).degree v = 3)
    (hcount : (degreeTwo ((hypercube 9).induce (S : Set (Q 9))) univ).card = 11)
    (hlow : ∀ ⦃v w⦄, ((hypercube 9).induce (S : Set (Q 9))).Adj v w →
      ((hypercube 9).induce (S : Set (Q 9))).degree v = 2 →
      ((hypercube 9).induce (S : Set (Q 9))).degree w = 2 → False) : False := by
  obtain ⟨b, hL, hR, he, _⟩ := twenty_one_slice_remaining_case S hS hb hdeg hcount hlow
  have hp : ((hypercube 9).induce (S : Set (Q 9))).IsBipartiteWith
      (paritySide S b : Set (S : Set (Q 9))) (paritySide S (!b) : Set (S : Set (Q 9))) := by
    cases b
    · exact parity_bipartite S
    · exact (parity_bipartite S).symm
  exact two_high_slice_impossible hb hp hdeg hlow hL hR he

#print axioms no_balanced_twenty_one_slice

end D5.S3.Combinatorics.Graph.HypercubeCritical
