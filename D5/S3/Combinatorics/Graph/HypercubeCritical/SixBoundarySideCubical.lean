/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCubical
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCubical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Private actual cubical obstruction for the twelve-left-vertex case. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideIncidence
import D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceMatching

/-! A labeled auxiliary cube supplies an actual induced fifteen-point subdivision
and three two-edge paths from its omitted vertex to the matching middles. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q)
open private cubeEdgeFrom cubeEdgeTo cubeEdgeEnds cubeEdgeOpposite firstThreeEdges
  cube_edge_labels cube_low_middles from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideIncidence
open private sideCore side_core_triangle_free twelve_core_data twelve_core_partners from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCore
open private twelve_side_structure from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
open private cubeEightNeighbors cube_eight_labeling from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideLabeling
open private Labels Labels.A Labels.B Labels.M Labels.mk from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity
open private labelled_matching_obstruction from
  D5.S3.Combinatorics.Graph.HypercubeCritical.NineteenPointSliceMatching
open private diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeNineSupport
open private diff from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

private def ringBranchIndex (h : Bool × Fin 3) : Fin 12 :=
  if h.1 then ![0,2,4] h.2 else ![5,1,3] h.2

private def ringMiddleIndex : Fin 3 × Fin 3 → Fin 8 ⊕ Fin 3 :=
  fun p => ![![Sum.inl 0, Sum.inr 2, Sum.inl 3],
    ![Sum.inl 1, Sum.inl 6, Sum.inr 1],
    ![Sum.inr 0, Sum.inl 5, Sum.inl 4]] p.1 p.2

private def ringLowPair (i : Fin 3) : Finset (Fin 12) :=
  {firstThreeEdges i, cubeEdgeOpposite (firstThreeEdges i)}

private def ringMiddleValue {V : Type*} (v : Fin 8 → V) (m : Fin 3 → V) :
    Fin 8 ⊕ Fin 3 → V := Sum.elim v m

private theorem cubical_ring_obstruction {C : Finset (Q 9)}
    {L R : Finset (C : Set (Q 9))}
    (hb : ((hypercube 9).induce (C : Set (Q 9))).IsBipartiteWith (L : Set _) (R : Set _))
    (hr : ∀ y ∈ R, ((hypercube 9).induce (C : Set (Q 9))).degree y ≤ 3)
    (v : Fin 8 → (degreeThree ((hypercube 9).induce (C : Set (Q 9))) R : Set _))
    (hv : Function.Bijective v)
    (e : Fin 12 → (C : Set (Q 9))) (he : Function.Injective e) (heL : ∀ j, e j ∈ L)
    (hinc : ∀ i j, ((hypercube 9).induce (C : Set (Q 9))).Adj (v i).val (e j) ↔
      i ∈ cubeEdgeEnds j)
    (m : Fin 3 → (C : Set (Q 9)))
    (hm : ∀ i, m i ∈ degreeTwo ((hypercube 9).induce (C : Set (Q 9))) R)
    (hmN : ∀ i, ((hypercube 9).induce (C : Set (Q 9))).neighborFinset (m i) =
      {e (firstThreeEdges i), e (cubeEdgeOpposite (firstThreeEdges i))}) : False := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  have hmi : Function.Injective m := by
    intro i j hij
    have hh := congrArg (fun x => G.neighborFinset x) hij
    rw [hmN i, hmN j] at hh
    have hp : (ringLowPair i).image e = (ringLowPair j).image e := by
      simpa only [ringLowPair, Finset.image_insert, Finset.image_singleton] using hh
    have hpair := (Finset.image_injective he) hp
    exact (by decide : Function.Injective ringLowPair) hpair
  have hvi : Function.Injective (fun i => (v i).val) := by
    intro i j h; exact hv.1 (Subtype.ext h)
  have hvm : Function.Injective (ringMiddleValue (fun i => (v i).val) m) := by
    intro s t hst
    cases s with
    | inl i =>
      cases t with
      | inl j => exact congrArg Sum.inl (hvi hst)
      | inr j =>
        have h3 := (Finset.mem_filter.mp (v i).property).2
        have h2 := (Finset.mem_filter.mp (hm j)).2
        change (v i).val = m j at hst
        rw [hst] at h3
        omega
    | inr i =>
      cases t with
      | inl j =>
        have h2 := (Finset.mem_filter.mp (hm i)).2
        have h3 := (Finset.mem_filter.mp (v j).property).2
        change m i = (v j).val at hst
        rw [hst] at h2
        omega
      | inr j => exact congrArg Sum.inr (hmi hst)
  let high (h : Bool × Fin 3) := e (ringBranchIndex h)
  let middle (p : Fin 3 × Fin 3) := ringMiddleValue (fun i => (v i).val) m (ringMiddleIndex p)
  have hhigh : Function.Injective high :=
    he.comp (by decide : Function.Injective ringBranchIndex)
  have hmiddle : Function.Injective middle :=
    hvm.comp (by decide : Function.Injective ringMiddleIndex)
  have hhighL (h : Bool × Fin 3) : high h ∈ L := heL _
  have hmiddleR (p : Fin 3 × Fin 3) : middle p ∈ R := by
    change ringMiddleValue (fun i => (v i).val) m (ringMiddleIndex p) ∈ R
    cases h : ringMiddleIndex p with
    | inl i => exact (Finset.mem_filter.mp (v i).property).1
    | inr i => exact (Finset.mem_filter.mp (hm i)).1
  have hcross (p : Fin 3 × Fin 3) (h : Bool × Fin 3) : middle p ≠ high h := by
    intro heq
    exact Set.disjoint_left.mp hb.disjoint (hhighL h) (heq ▸ hmiddleR p)
  have hmidnotadj (p q : Fin 3 × Fin 3) : ¬ G.Adj (middle p) (middle q) := by
    intro h
    have hL := hb.mem_of_mem_adj' (hmiddleR p) h.symm
    exact Set.disjoint_left.mp hb.disjoint hL (hmiddleR q)
  have hbase (t : Fin 8 ⊕ Fin 3) (j : Fin 12) :
      G.Adj (ringMiddleValue (fun i => (v i).val) m t) (e j) ↔
        match t with
        | Sum.inl k => k ∈ cubeEdgeEnds j
        | Sum.inr k => j ∈ ringLowPair k := by
    cases t with
    | inl k => exact hinc k j
    | inr k =>
      change G.Adj (m k) (e j) ↔ _
      rw [← SimpleGraph.mem_neighborFinset, hmN]
      simp only [ringLowPair, Finset.mem_insert, Finset.mem_singleton, he.eq_iff]
  have hadj (p : Fin 3 × Fin 3) (h : Bool × Fin 3) :
      G.Adj (middle p) (high h) ↔ h = (false,p.1) ∨ h = (true,p.2) := by
    change G.Adj (ringMiddleValue (fun i => (v i).val) m (ringMiddleIndex p))
      (e (ringBranchIndex h)) ↔ _
    rw [hbase]
    have hf : ∀ (p : Fin 3 × Fin 3) (h : Bool × Fin 3),
        (match ringMiddleIndex p with
          | Sum.inl k => k ∈ cubeEdgeEnds (ringBranchIndex h)
          | Sum.inr k => ringBranchIndex h ∈ ringLowPair k) ↔
        h = (false,p.1) ∨ h = (true,p.2) := by
      rintro ⟨i,j⟩ ⟨s,k⟩
      fin_cases i <;> fin_cases j <;> cases s <;> fin_cases k <;>
        simp [ringMiddleIndex, ringBranchIndex, ringLowPair, cubeEdgeEnds,
          cubeEdgeFrom, cubeEdgeTo, firstThreeEdges, cubeEdgeOpposite]
    exact hf p h
  let K := Finset.univ.image (fun h => (high h).val) ∪
    Finset.univ.image (fun p => (middle p).val)
  have hKS : K ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx; exact (high h).property
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx; exact (middle p).property
  let A (i : Fin 3) : (K : Set (Q 9)) := ⟨(high (false,i)).val,
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(false,i), Finset.mem_univ _, rfl⟩)⟩
  let B (j : Fin 3) : (K : Set (Q 9)) := ⟨(high (true,j)).val,
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(true,j), Finset.mem_univ _, rfl⟩)⟩
  let M (i j : Fin 3) : (K : Set (Q 9)) := ⟨(middle (i,j)).val,
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩)⟩
  have hhighval : Function.Injective (fun h => (high h).val) := by
    intro h k heq; exact hhigh (Subtype.ext heq)
  let l : Labels ((hypercube 9).induce (K : Set (Q 9))) := Labels.mk A B M
    (by
      intro h k heq
      apply hhighval
      have hh := congrArg (fun z : (K : Set (Q 9)) => z.val) heq
      rcases h with ⟨s,i⟩; rcases k with ⟨t,j⟩
      cases s <;> cases t <;> simpa [A,B] using hh)
    (by
      intro i j z
      rcases Finset.mem_union.mp z.property with hz | hz
      · obtain ⟨h, _, hz⟩ := Finset.mem_image.mp hz
        change (hypercube 9).Adj (middle (i,j)).val z.val ↔ z = A i ∨ z = B j
        have hh := hadj (i,j) h
        change (hypercube 9).Adj (middle (i,j)).val (high h).val ↔ _ at hh
        simpa only [Subtype.ext_iff, A, B, ← hz, hhighval.eq_iff] using hh
      · obtain ⟨p, _, hz⟩ := Finset.mem_image.mp hz
        have hno : ¬ (hypercube 9).Adj (middle (i,j)).val z.val := by
          rw [← hz]; exact hmidnotadj (i,j) p
        have hnA : z ≠ A i := by
          intro h
          exact hcross p (false,i) (Subtype.ext (hz.trans (congrArg Subtype.val h)))
        have hnB : z ≠ B j := by
          intro h
          exact hcross p (true,j) (Subtype.ext (hz.trans (congrArg Subtype.val h)))
        exact iff_of_false hno (not_or.mpr ⟨hnA,hnB⟩))
    (by
      intro i j k heq
      have hval : (middle (i,j)).val = (middle (i,k)).val :=
        congrArg (fun x : (K : Set (Q 9)) => x.val) heq
      have hh := hmiddle (show middle (i,j) = middle (i,k) from Subtype.ext hval)
      exact congrArg Prod.snd hh)
    (by
      intro j i k heq
      have hval : (middle (i,j)).val = (middle (k,j)).val :=
        congrArg (fun x : (K : Set (Q 9)) => x.val) heq
      have hh := hmiddle (show middle (i,j) = middle (k,j) from Subtype.ext hval)
      exact congrArg Prod.fst hh)
    (by
      intro z
      rcases Finset.mem_union.mp z.property with hz | hz
      · obtain ⟨⟨s,i⟩, _, hz⟩ := Finset.mem_image.mp hz
        cases s
        · exact Or.inl ⟨i,Subtype.ext hz.symm⟩
        · exact Or.inr (Or.inl ⟨i,Subtype.ext hz.symm⟩)
      · obtain ⟨⟨i,j⟩, _, hz⟩ := Finset.mem_image.mp hz
        exact Or.inr (Or.inr ⟨i,j,Subtype.ext hz.symm⟩))
  have hnear (i : Fin 3) : (diff (v 2).val.val ((Labels.M l) i i).val).card ≤ 2 := by
    let diag : Fin 3 → Fin 8 := ![0,6,4]
    let bridge : Fin 3 → Fin 12 := ![6,7,8]
    have hdiag : middle (i,i) = (v (diag i)).val := by fin_cases i <;> rfl
    have hp : G.Adj (v 2).val (e (bridge i)) := (hinc _ _).mpr (by
      fin_cases i <;> decide)
    have hq : G.Adj (v (diag i)).val (e (bridge i)) := (hinc _ _).mpr (by
      fin_cases i <;> decide)
    have h1 : (diff (v 2).val.val (e (bridge i)).val).card = 1 := hp
    have h2 : (diff (v (diag i)).val.val (e (bridge i)).val).card = 1 := hq
    have ht := diff_triangle_card (v 2).val.val (v (diag i)).val.val (e (bridge i)).val
    change (diff (v 2).val.val (middle (i,i)).val).card ≤ 2
    rw [hdiag]
    omega
  exact labelled_matching_obstruction hKS l (v 2).val
    (hr _ (Finset.mem_filter.mp (v 2).property).1) hnear

private theorem twelve_impossible {C : Finset (Q 9)}
    {L R : Finset (C : Set (Q 9))}
    (hb : ((hypercube 9).induce (C : Set (Q 9))).IsBipartiteWith (L : Set _) (R : Set _))
    (hd : ∀ x ∈ L, ((hypercube 9).induce (C : Set (Q 9))).degree x = 3)
    (hr : ∀ y ∈ R, ((hypercube 9).induce (C : Set (Q 9))).degree y ≤ 3)
    (hg : (8 : ℕ∞) ≤ ((hypercube 9).induce (C : Set (Q 9))).egirth)
    (hL : L.card = 12) (hR : R.card = 14) : False := by
  obtain ⟨hr23, hn3, _, hleft⟩ := twelve_side_structure hb hd hr hg hL hR
  have hdegree := (twelve_core_data hb hg hleft).2
  obtain ⟨v, hv, hN⟩ := cube_eight_labeling (by simpa using hn3) hdegree
    (side_core_triangle_free hb hg) (twelve_core_partners hb hg hd hr23 hleft)
  obtain ⟨e, he, heL, hecover, hinc⟩ := cube_edge_labels hb hleft hL v hv hN
  obtain ⟨m, hm, hmN⟩ := cube_low_middles hb hg hd hr23 hleft v hv hN e heL hecover hinc
  exact cubical_ring_obstruction hb hr v hv e he heL hinc m hm hmN

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap
