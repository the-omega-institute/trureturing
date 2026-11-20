/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4NoSingletonCase
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4NoSingletonCase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The zero-singleton obstruction for the normalized ten-point K4 projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The balanced suffix graph in the zero-singleton case of the K4 residual. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4NoSingletonCase

open Finset
open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open Q9SignedProjection (join fiber signedRow)
open Q9TenPatternIncidence (tenProjection vertexCode midpointCode endpoints
  midpoint_cut exterior_constraints)
open Q9K4CutBalance (occupied evenLabel evenCount oddCount)
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private mem_leftProjection from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
open private transpose_mulVec signed_row_blocks from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence
open private flip_join_left flip_join_right sign_join_left sign_join_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private pattern_parities nonzero_iff_mem label_values selected_term
  occupied_eq_indicator ternary exists_ternary from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private directions_card flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

private def midpointPattern (e : Fin 6) : Q 4 := pattern (midpointCode e)

private def midpoint (z : Q 9 → ℤ) (y : Q 5) (e : Fin 6) : ℤ :=
  fiber z y (midpointPattern e)

private def cutValue (s : Fin 4 → Bool) (e : Fin 6) : ℤ :=
  (if s (endpoints e).1 then 1 else 0) - (if s (endpoints e).2 then 1 else 0)

private def crossingSet (s : Fin 4 → Bool) : Finset (Fin 6) :=
  univ.filter fun e => cutValue s e ≠ 0

private theorem cut_table : ∀ s t : Fin 4 → Bool, ∀ b : Bool,
    (crossingSet s).card = 4 → (crossingSet t).card = 4 →
    (∀ e, e ∈ crossingSet s → e ∈ crossingSet t →
      cutValue s e * ((if b then 1 else -1) * cutValue t e) = 1) →
    crossingSet s = crossingSet t := by
  decide +kernel

private theorem midpoint_in_projection : ∀ e : Fin 6, midpointPattern e ∈ tenProjection := by
  decide +kernel

open Classical in
private theorem fiber_cuts {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5) :
    ∃ s : Fin 4 → Bool, (∀ e, midpoint z y e = cutValue s e) ∧
      (crossingSet s).card = oddCount z y := by
  have hs (x : Q 4) (hx : x ∉ tenProjection) :=
    fiber_and_signedRow_supported hz hrow y (hP.symm ▸ hx)
  have hunit (e : Fin 6) : |midpoint z y e| ≤ 1 := by
    rcases label_values hu hz (join (midpointPattern e) y) with h | h | h <;>
      change |z (join (midpointPattern e) y)| ≤ 1 <;> norm_num [h]
  obtain ⟨hm, _, level, s, hlevel, _⟩ :=
    midpoint_cut (fun x hx => (hs x hx).1) (fun x hx => (hs x hx).2) hunit
  have hval (e : Fin 6) : midpoint z y e = cutValue s e := by
    have he := congrFun hm e
    rw [transpose_mulVec, hlevel, hlevel] at he
    change midpoint z y e = _ at he
    unfold cutValue
    omega
  refine ⟨s, hval, ?_⟩
  change ((crossingSet s).card : ℤ) = ∑ e, occupied (midpoint z y e)
  simp only [hval, occupied, crossingSet, card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro e _
  by_cases h : cutValue s e = 0 <;> simp [h]

open Classical in
private theorem adjacent_partitions {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    {y : Q 5} {s t : Fin 4 → Bool} (d : Fin 5)
    (hs : ∀ e, midpoint z y e = cutValue s e)
    (ht : ∀ e, midpoint z (flip y d) e = cutValue t e)
    (hsc : (crossingSet s).card = 4) (htc : (crossingSet t).card = 4) :
    crossingSet s = crossingSet t := by
  have hsign : -(truePrefixSign y d) = 1 ∨ -(truePrefixSign y d) = -1 := by
    have h : truePrefixSign y d = 1 ∨ truePrefixSign y d = -1 := by
      unfold truePrefixSign
      exact neg_one_pow_eq_or _ _
    rcases h with h | h <;> simp [h]
  obtain ⟨b, hb⟩ : ∃ b : Bool, -(truePrefixSign y d) = if b then 1 else -1 := by
    rcases hsign with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  refine cut_table s t b hsc htc (fun e he he' => ?_)
  have hne : cutValue s e ≠ 0 := (mem_filter.mp he).2
  have hne' : cutValue t e ≠ 0 := (mem_filter.mp he').2
  have hmem : join (midpointPattern e) y ∈ C :=
    (nonzero_iff_mem hu hz _).mp (show midpoint z y e ≠ 0 by rwa [hs])
  have hh := selected_term hreg hu hz hrow hmem (d.natAdd 4)
  have hpar : Q9SignedProjection.leftParitySign (midpointPattern e) = -1 :=
    pattern_parities.2 e
  rw [flip_join_right, sign_join_right, hpar, neg_one_mul] at hh
  change midpoint z y e * (-truePrefixSign y d * midpoint z (flip y d) e) =
    occupied (midpoint z (flip y d) e) at hh
  simpa only [hs, ht, hb, occupied, ite_eq_right hne'] using hh

private theorem horizontal_neighbors : ∀ e : Fin 6,
    ((univ.filter fun d : Fin 4 => flip (midpointPattern e) d ∈ tenProjection).image
      (flip (midpointPattern e))) =
      {pattern (vertexCode (endpoints e).1), pattern (vertexCode (endpoints e).2)} ∧
    pattern (vertexCode (endpoints e).1) ≠ pattern (vertexCode (endpoints e).2) := by
  decide +kernel

private theorem horizontal_degree {z : Q 9 → ℤ} {y : Q 5} (e : Fin 6)
    (hz : ∀ x ∉ tenProjection, fiber z y x = 0) :
    (∑ d : Fin 4, occupied (fiber z y (flip (midpointPattern e) d))) =
      occupied (evenLabel z (endpoints e).1 y) + occupied (evenLabel z (endpoints e).2 y) := by
  let D := univ.filter fun d : Fin 4 => flip (midpointPattern e) d ∈ tenProjection
  rw [← sum_subset (filter_subset _ _) (s₁ := D) (fun d _ hd => by
    have hn : flip (midpointPattern e) d ∉ tenProjection :=
      fun h => hd (mem_filter.mpr ⟨mem_univ _, h⟩)
    simp [hz _ hn, occupied])]
  have himage := sum_image (s := D) (g := flip (midpointPattern e))
    (f := fun x => occupied (fiber z y x)) (flip_injective _).injOn
  rw [← himage]
  change (∑ x ∈ (univ.filter fun d : Fin 4 => flip (midpointPattern e) d ∈ tenProjection).image
    (flip (midpointPattern e)), occupied (fiber z y x)) = _
  rw [(horizontal_neighbors e).1]
  rw [sum_insert (by simpa using (horizontal_neighbors e).2), sum_singleton]
  rfl

open Classical in
private theorem midpoint_degrees {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) {y : Q 5} {e : Fin 6}
    (hm : join (midpointPattern e) y ∈ C)
    (hout : ∀ x ∉ tenProjection, fiber z y x = 0) :
    let a := fun i => evenLabel z i y
    let hor := occupied (a (endpoints e).1) + occupied (a (endpoints e).2)
    (hor + ∑ d : Fin 5, occupied (midpoint z (flip y d) e)) = 3 ∧
      midpoint z y e * (a (endpoints e).1 - a (endpoints e).2) = hor := by
  dsimp only
  have hdeg : (∑ d : Fin 9, occupied (z (flip (join (midpointPattern e) y) d))) = 3 := by
    simp only [occupied_eq_indicator hu hz, sum_boole]
    change ((directions C (join (midpointPattern e) y)).card : ℤ) = 3
    rw [regular_directions C hreg hm]
    rfl
  rw [Fin.sum_univ_add (a := 4) (b := 5)] at hdeg
  simp only [flip_join_left, flip_join_right] at hdeg
  change (∑ d : Fin 4, occupied (fiber z y (flip (midpointPattern e) d))) +
    ∑ d : Fin 5, occupied (midpoint z (flip y d) e) = 3 at hdeg
  rw [horizontal_degree e hout] at hdeg
  refine ⟨hdeg, ?_⟩
  have hhor := congrFun (signed_row_blocks hout).2 e
  rw [transpose_mulVec] at hhor
  change signedRow (fiber z y) (midpointPattern e) =
    evenLabel z (endpoints e).1 y - evenLabel z (endpoints e).2 y at hhor
  rw [← hhor, signedRow, mul_sum, ← horizontal_degree e hout]
  refine sum_congr rfl (fun d _ => ?_)
  have hh := selected_term hreg hu hz hrow hm (d.castAdd 5)
  rw [flip_join_left, sign_join_left] at hh
  exact hh

private theorem occupation_table : ∀ (s : Fin 4 → Bool) (a : Fin 4 → Fin 3) (n : Fin 4),
    let v := fun i => ternary (a i)
    (crossingSet s).card = 4 → (∑ i, v i) = 0 →
    (∀ e ∈ crossingSet s,
      let h := occupied (v (endpoints e).1) + occupied (v (endpoints e).2)
      h + (n.val : ℤ) = 3 ∧ cutValue s e * (v (endpoints e).1 - v (endpoints e).2) = h) →
    (evenCount v = 0 ∧ n = 3) ∨ (evenCount v = 4 ∧ n = 1) := by
  decide +kernel

open Classical in
private theorem fiber_occupation {a : Fin 4 → ℤ} {s : Fin 4 → Bool} {n : ℤ}
    (ha : ∀ i, a i = 0 ∨ a i = 1 ∨ a i = -1) (hs : (∑ i, a i) = 0)
    (hsc : (crossingSet s).card = 4) (hn : 0 ≤ n)
    (hdeg : ∀ e ∈ crossingSet s,
      let h := occupied (a (endpoints e).1) + occupied (a (endpoints e).2)
      h + n = 3 ∧ cutValue s e * (a (endpoints e).1 - a (endpoints e).2) = h) :
    (evenCount a = 0 ∧ n = 3) ∨ (evenCount a = 4 ∧ n = 1) := by
  choose t ht using fun i => exists_ternary (ha i)
  have hu (k : ℤ) : 0 ≤ occupied k := by unfold occupied; split <;> omega
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (crossingSet s).card by omega)
  have hle : n < 4 := by
    have hh := (hdeg e he).1
    linarith [hu (a (endpoints e).1), hu (a (endpoints e).2)]
  let k : Fin 4 := ⟨n.toNat, by omega⟩
  have hk : (k.val : ℤ) = n := Int.toNat_of_nonneg hn
  have h := occupation_table s t k
  simp only [ht, hk] at h
  rcases h hsc hs hdeg with ⟨hzero, h3⟩ | ⟨hfull, h1⟩
  · exact Or.inl ⟨hzero, by simpa [h3] using hk.symm⟩
  · exact Or.inr ⟨hfull, by simpa [h1] using hk.symm⟩

open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open SimpleGraph

private theorem reachable_partition {V : Type} {G : SimpleGraph V} {α : Type}
    (p : V → α) (h : ∀ {v w}, G.Adj v w → p v = p w)
    {v w : V} (hw : G.Reachable v w) : p v = p w := by
  obtain ⟨walk⟩ := hw
  induction walk with
  | nil => rfl
  | cons hadj _ ih => exact (h hadj).trans ih

private theorem join_right_injective (x : Q 4) : Function.Injective (join x) := by
  intro y w h
  exact funext fun d => by simpa [join] using congrFun h (d.natAdd 4)

private theorem join_right_adj (x : Q 4) {y w : Q 5}
    (h : (hypercube 5).Adj y w) : (hypercube 9).Adj (join x y) (join x w) := by
  obtain ⟨d, rfl⟩ := adjacent_exists_flip h
  rw [← flip_join_right]
  exact BalancedCriticalSpectrum.flip_adj _ _

open Classical in
private theorem suffix_degree (T : Finset (Q 5)) (y : (T : Set (Q 5))) :
    (((hypercube 5).induce (T : Set (Q 5))).degree y : ℤ) =
      ∑ d : Fin 5, if flip y.val d ∈ T then 1 else 0 := by
  rw [sum_boole]
  change (_ : ℤ) = ((directions T y.val).card : ℤ)
  rw [directions_card]
  congr 1
  apply Finset.card_bij (fun w _ => w.val)
  · intro w hw
    have hadj := (SimpleGraph.mem_neighborFinset
      ((hypercube 5).induce (T : Set (Q 5))) y w).mp hw
    exact mem_filter.mpr ⟨w.property, hadj⟩
  · intro w _ w' _ h
    exact Subtype.ext h
  · intro w hw
    obtain ⟨hwT, hadj⟩ := mem_filter.mp hw
    exact ⟨⟨w, hwT⟩, (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj, rfl⟩

open Classical in
private theorem degree_three_of_cycle_vertex {V : Type} [Fintype V] {G : SimpleGraph V}
    (hdeg : ∀ v, G.degree v = 1 ∨ G.degree v = 3)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    G.degree v = 3 := by
  rcases hdeg v with h1 | h3
  · have h := hp.rotate hv
    obtain ⟨w, _, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp h1
    exact (h.snd_ne_penultimate
      ((huniq _ (Walk.adj_snd h.not_nil)).trans
        (huniq _ (Walk.adj_penultimate h.not_nil).symm).symm)).elim
  · exact h3

open Classical in
private theorem suffix_forest {C : Finset (Q 9)} (hb : IsBalanced C) (T : Finset (Q 5))
    (P : ↥(T : Set (Q 5)) → Finset (Fin 6))
    (hP : ∀ v, (P v).card = 4)
    (hmem : ∀ v e, e ∈ P v → join (midpointPattern e) v.val ∈ C)
    (hstep : ∀ {v w}, ((hypercube 5).induce (T : Set (Q 5))).Adj v w → P v = P w)
    (hdeg : ∀ v, ((hypercube 5).induce (T : Set (Q 5))).degree v = 1 ∨
      ((hypercube 5).induce (T : Set (Q 5))).degree v = 3)
    (hfour : (univ.filter fun v =>
      ((hypercube 5).induce (T : Set (Q 5))).degree v = 3).card = 4) :
    ((hypercube 5).induce (T : Set (Q 5))).IsAcyclic := by
  let G := (hypercube 5).induce (T : Set (Q 5))
  intro u p hp
  have hbound : p.length ≤ 4 := by
    let f : Fin p.length ↪ {v // G.degree v = 3} :=
      ⟨fun i => ⟨p.getVert i, degree_three_of_cycle_vertex hdeg hp (p.getVert_mem_support i)⟩,
        fun i j hij => Fin.ext (hp.getVert_injOn'
          (by exact Nat.le_sub_one_of_lt i.isLt) (by exact Nat.le_sub_one_of_lt j.isLt)
          (congrArg Subtype.val hij))⟩
    have h := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin, Fintype.card_subtype] at h
    change p.length ≤ (univ.filter fun v => G.degree v = 3).card at h
    exact h.trans_eq hfour
  let color : G.Coloring Bool :=
    Coloring.mk (fun v => cubeParity v.val) (fun h => cubeParity_ne_of_adj h)
  have heven : Even p.length := (color.even_length_iff_congr p).mpr Iff.rfl
  have hlen : p.length = 4 := by obtain ⟨k, hk⟩ := heven; have := hp.three_le_length; omega
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (P u).card by rw [hP]; decide)
  let S : Set (T : Set (Q 5)) := {v | G.Reachable u v}
  have hcontains (v : (T : Set (Q 5))) (hv : v ∈ p.support) : v ∈ S := by
    exact ⟨p.takeUntil v hv⟩
  let q := p.induce S hcontains
  have hqmap : q.map (SimpleGraph.Embedding.induce S).toHom = p := Walk.map_induce p hcontains
  have hq : q.IsCycle := Walk.IsCycle.of_map (hqmap.symm ▸ hp)
  have hlenEq := congrArg (fun w : G.Walk u u => w.length) hqmap
  have hqlen : q.length = 4 := by
    exact (Walk.length_map (SimpleGraph.Embedding.induce S).toHom q).symm.trans
      (hlenEq.trans hlen)
  let m : G.induce S →g (hypercube 9).induce (C : Set (Q 9)) :=
    ⟨fun v => ⟨join (midpointPattern e) v.val.val,
      hmem v.val e (reachable_partition P hstep (show G.Reachable u v.val from v.property) ▸ he)⟩,
      fun h => join_right_adj _ h⟩
  have hm : Function.Injective m := fun _ _ h =>
    Subtype.ext (Subtype.ext (join_right_injective _ (congrArg Subtype.val h)))
  apply BalancedCubeGirth.no_four_cycle hb (q.map m) (hq.map hm)
  exact (Walk.length_map m q).trans hqlen

open Classical in
private theorem connected_of_forest {V : Type} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : G.IsAcyclic)
    (hcard : G.edgeFinset.card + 1 = Fintype.card V) : G.Connected := by
  have htop : (⊤ : SimpleGraph V).Connected := connected_top
  obtain ⟨F, hGF, _, hF⟩ := htop.exists_isTree_le_of_le_of_isAcyclic le_top hG
  have heq : G.edgeFinset = F.edgeFinset :=
    Finset.eq_of_subset_of_card_le (fun _ h => by
      simpa only [mem_edgeFinset] using edgeSet_mono hGF (mem_edgeFinset.mp h))
      (by have := hF.card_edgeFinset; omega)
  have hgraphs : G = F := by
    apply edgeSet_injective
    ext e
    simp only [← mem_edgeFinset, heq]
  exact hgraphs ▸ hF.connected

open Classical in
/-- An actual cubic balanced support with the exact K4 projection cannot have zero
singleton cuts, 40 odd occupations, and 24 even occupations at its nonzero cuts. -/
theorem no_zero_singleton_case {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hcuts : ∀ y, oddCount z y = 0 ∨ oddCount z y = 4)
    (hodd : (∑ y : Q 5, oddCount z y) = 40)
    (heven : (∑ y ∈ univ.filter (fun y : Q 5 => oddCount z y = 4),
      evenCount (fun i => evenLabel z i y)) = 24) : False := by
  let T := univ.filter fun y : Q 5 => oddCount z y = 4
  let G := (hypercube 5).induce (T : Set (Q 5))
  choose side hval hcard using fiber_cuts hP hu hz hrow
  have hT (y : Q 5) : y ∈ T ↔ oddCount z y = 4 := by simp [T]
  have h4 (y : Q 5) (hy : y ∈ T) : (crossingSet (side y)).card = 4 := by
    have h := hcard y
    rw [(hT y).mp hy] at h
    exact_mod_cast h
  have hsame (y : Q 5) (d : Fin 5) (hy : y ∈ T) (hy' : flip y d ∈ T) :
      crossingSet (side y) = crossingSet (side (flip y d)) :=
    adjacent_partitions hreg hu hz hrow d (hval y) (hval _) (h4 y hy) (h4 _ hy')
  have hpicked (y : Q 5) (e : Fin 6) :
      join (midpointPattern e) y ∈ C ↔ e ∈ crossingSet (side y) := by
    rw [← nonzero_iff_mem hu hz _]
    change midpoint z y e ≠ 0 ↔ _
    simp [hval, crossingSet]
  have hstep {v w : (T : Set (Q 5))} (h : G.Adj v w) :
      crossingSet (side v.val) = crossingSet (side w.val) := by
    obtain ⟨d, hd⟩ := adjacent_exists_flip (show (hypercube 5).Adj v.val w.val from h)
    exact hd.symm ▸ hsame v.val d v.property (hd ▸ w.property)
  have hlocal (v : (T : Set (Q 5))) :
      (evenCount (fun i => evenLabel z i v.val) = 0 ∧ G.degree v = 3) ∨
      (evenCount (fun i => evenLabel z i v.val) = 4 ∧ G.degree v = 1) := by
    have hsupport (x : Q 4) (hx : x ∉ tenProjection) :=
      fiber_and_signedRow_supported hz hrow v.val (hP.symm ▸ hx)
    have hs := (exterior_constraints (fun x hx => (hsupport x hx).1)
      (fun x hx => (hsupport x hx).2)).2.2.2
    have hsum : (∑ i, evenLabel z i v.val) = 0 := by
      simpa [evenLabel, Fin.sum_univ_succ, vertexCode, add_assoc] using hs
    have hh (e : Fin 6) (he : e ∈ crossingSet (side v.val)) (d : Fin 5) :
        occupied (midpoint z (flip v.val d) e) = if flip v.val d ∈ T then 1 else 0 := by
      split
      next hw =>
        have he' : e ∈ crossingSet (side (flip v.val d)) :=
          hsame _ d v.property hw ▸ he
        have hn : cutValue (side (flip v.val d)) e ≠ 0 := (mem_filter.mp he').2
        simp [hval, occupied, hn]
      next hw =>
        have hc : (crossingSet (side (flip v.val d))).card = 0 := by
          have hh := hcard (flip v.val d)
          rcases hcuts (flip v.val d) with h | h
          · rw [h] at hh
            exact_mod_cast hh
          · exact (hw ((hT _).mpr h)).elim
        have hzero : cutValue (side (flip v.val d)) e = 0 := by
          by_contra hne
          have hm : e ∈ crossingSet (side (flip v.val d)) := mem_filter.mpr ⟨mem_univ _, hne⟩
          rw [card_eq_zero.mp hc] at hm
          exact notMem_empty _ hm
        simp [hval, occupied, hzero]
    have h := fiber_occupation (a := fun i => evenLabel z i v.val)
      (fun i => label_values hu hz (join (pattern (vertexCode i)) v.val))
      hsum (h4 _ v.property) (n := (G.degree v : ℤ)) (by positivity) (fun e he => by
        have hd := midpoint_degrees hreg hu hz hrow ((hpicked _ _).mpr he)
          (fun x hx => (hsupport x hx).1)
        simp only [hh e he] at hd
        rw [← suffix_degree T v] at hd
        rw [hval] at hd
        exact hd)
    rcases h with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · exact Or.inl ⟨ha, by exact_mod_cast hd⟩
    · exact Or.inr ⟨ha, by exact_mod_cast hd⟩
  have hten : T.card = 10 := by
    have hw (y : Q 5) : oddCount z y = if y ∈ T then 4 else 0 := by
      rcases hcuts y with h | h <;> simp [T, h]
    have hh := hodd
    simp only [hw, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul] at hh
    rw [show (univ.filter fun y => y ∈ T) = T by ext; simp] at hh
    omega
  have hverts : Fintype.card (T : Set (Q 5)) = 10 := by simpa using hten
  have hsumEven : (∑ v : (T : Set (Q 5)), evenCount (fun i => evenLabel z i v.val)) = 24 := by
    exact (Finset.sum_finset_coe (fun y => evenCount (fun i => evenLabel z i y)) T).trans heven
  let leaves := univ.filter fun v : (T : Set (Q 5)) => G.degree v = 1
  have hsumLeaves : (∑ v : (T : Set (Q 5)), evenCount (fun i => evenLabel z i v.val)) =
      (leaves.card : ℤ) * 4 := by
    have h (v : (T : Set (Q 5))) :
        evenCount (fun i => evenLabel z i v.val) = if G.degree v = 1 then 4 else 0 := by
      rcases hlocal v with ⟨ha, hd⟩ | ⟨ha, hd⟩ <;> simp [ha, hd]
    simp [h, leaves, sum_ite]
  have hsix : leaves.card = 6 := by omega
  have hfour : (univ.filter fun v => G.degree v = 3).card = 4 := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (T : Set (Q 5))))
      (fun v => G.degree v = 1)
    have heq : (univ.filter fun v => ¬ G.degree v = 1) =
        univ.filter fun v => G.degree v = 3 := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      rcases hlocal v with ⟨_, hv⟩ | ⟨_, hv⟩ <;> simp [hv]
    rw [heq, card_univ, hverts] at h
    change leaves.card + _ = 10 at h
    omega
  have hacyc := suffix_forest hb T (fun v => crossingSet (side v.val))
    (fun v => h4 _ v.property) (fun v e => (hpicked _ e).mpr) hstep
    (fun v => (hlocal v).imp And.right And.right |>.symm) hfour
  have hedge : G.edgeFinset.card + 1 = Fintype.card (T : Set (Q 5)) := by
    have h := G.sum_degrees_eq_twice_card_edges
    have hd (v : (T : Set (Q 5))) : G.degree v = if G.degree v = 1 then 1 else 3 := by
      rcases hlocal v with ⟨_, hv⟩ | ⟨_, hv⟩ <;> simp [hv]
    conv at h => lhs; arg 2; ext v; rw [hd v]
    rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at h
    have hpart := card_filter_add_card_filter_not (s := (univ : Finset (T : Set (Q 5))))
      (fun v => G.degree v = 1)
    change leaves.card + _ = _ at hpart
    simp only [card_univ, hverts] at hpart
    change leaves.card * 1 + _ * 3 = _ at h
    rw [hverts]
    omega
  have : Nonempty (T : Set (Q 5)) := Fintype.card_pos_iff.mp (by omega)
  have hconn := connected_of_forest hacyc hedge
  let v : (T : Set (Q 5)) := Classical.choice inferInstance
  have hall (e : Fin 6) : e ∈ crossingSet (side v.val) := by
    obtain ⟨y, hy⟩ := mem_leftProjection.mp (hP.symm ▸ midpoint_in_projection e)
    have he := (hpicked y e).mp hy
    have hyT : y ∈ T := by
      apply (hT y).mpr
      rcases hcuts y with h | h
      · have hh := hcard y
        rw [h] at hh
        have hzero : (crossingSet (side y)).card = 0 := by exact_mod_cast hh
        exact (notMem_empty e (card_eq_zero.mp hzero ▸ he)).elim
      · exact h
    have hsame' := reachable_partition (fun w : (T : Set (Q 5)) => crossingSet (side w.val))
      hstep (hconn.preconnected ⟨y, hyT⟩ v)
    exact hsame' ▸ he
  have huniv : crossingSet (side v.val) = univ := eq_univ_of_forall hall
  have h := h4 _ v.property
  rw [huniv, card_univ, Fintype.card_fin] at h
  omega

#check no_zero_singleton_case
#print axioms no_zero_singleton_case

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4NoSingletonCase
