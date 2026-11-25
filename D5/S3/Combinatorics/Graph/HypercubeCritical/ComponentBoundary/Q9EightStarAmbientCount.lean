/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An occupied eight-star forces thirty-two vertices of one projected parity and at least ten paired fibres. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

/-!
# Ambient vertex count for an eight-spoke Q9 star

For Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2. Sixteen mixed corners
force sixteen distinct third neighbors in the projected parity of the
sixteen lifted spokes. The count is on actual Q9 vertices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarAmbientCount

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCriticalSpectrum (Q flip_adj IsBalanced directionEdges)
open BalancedCubeComponentBoundary (directions directions_card mem_directions regular_directions
  flip_injective)
open BalancedCubeGirth (flip_comm no_selected_square)
open Q9FoldedIncidence (restrictCoordinates)
open Q9OccupiedFibreParity (doubleFibres occupied_fibre_identity)
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private liftVertex drop_insert flip_insert parity_flip projectedVertices
  card_projectedVertices doubleFibres_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
open private diff diff_symm diff_double_flip diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap
open private square_of_shared_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift
open private two_step_first_direction_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

attribute [local instance] Classical.propDecidable

private abbrev dropAxis (i : Fin 9) :=
  restrictCoordinates (Fin.succAboveEmb i)

private abbrev corner (r : Q 8) (j k : Fin 8) : Q 8 :=
  flip (flip r j) k

private theorem flip_lift_transverse (i : Fin 9) (t : Bool) (q : Q 8) (j : Fin 8) :
    flip (liftVertex i t q) (i.succAbove j) = liftVertex i t (flip q j) := by
  simpa only [BalancedCriticalSpectrum.flip, liftVertex, Fin.insertNth_apply_succAbove] using
    (Fin.insertNth_update (α := fun _ => Bool) i t j (!q j) q).symm

private theorem corner_back_first (r : Q 8) (j k : Fin 8) :
    flip (corner r j k) j = flip r k := by
  rw [show corner r j k = flip (flip r k) j from flip_comm r j k, BalancedCriticalSpectrum.flip_flip]

private theorem diff_flip_right (r q : Q 8) (j : Fin 8) :
    diff r (flip q j) =
      if j ∈ diff r q then (diff r q).erase j else insert j (diff r q) := by
  have h : diff (flip q j) r =
      if j ∈ diff q r then (diff q r).erase j else insert j (diff q r) :=
    diff_flip q r j
  simpa only [diff_symm (flip q j) r, diff_symm q r] using h

private theorem diff_spoke (r : Q 8) (j : Fin 8) : diff r (flip r j) = {j} := by
  have h : diff r r = ∅ := by simp [diff]
  simp [diff_flip_right, h]

private theorem diff_third (r : Q 8) {j k d : Fin 8}
    (hjk : j ≠ k) (hdj : d ≠ j) (hdk : d ≠ k) :
    diff r (flip (corner r j k) d) = {d, j, k} := by
  rw [diff_flip_right, show diff r (corner r j k) = {j, k} from diff_double_flip r hjk] <;>
    simp [hdj, hdk]

private theorem third_ne_spoke (r : Q 8) {j k d a : Fin 8}
    (hjk : j ≠ k) (hdj : d ≠ j) (hdk : d ≠ k) :
    flip (corner r j k) d ≠ flip r a := by
  intro h
  have he := congrArg (diff r) h
  rw [diff_third r hjk hdj hdk, diff_spoke] at he
  have hc := congrArg Finset.card he
  have hn : d ∉ ({j, k} : Finset (Fin 8)) := by simp [hdj, hdk]
  rw [card_insert_of_notMem hn, card_pair hjk, card_singleton] at hc
  omega

private theorem direction_to_shared_spoke (r : Q 8) {a j k d : Fin 8}
    (ha : a ∈ ({j, k} : Finset (Fin 8))) (hdj : d ≠ j) (hdk : d ≠ k) :
    ∃ l : Fin 8, l ≠ d ∧ flip (flip r a) l = corner r j k := by
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with h | h
  · subst a
    exact ⟨k, hdk.symm, rfl⟩
  · subst a
    exact ⟨j, hdj.symm, flip_comm r k j⟩

private theorem mixed_corner_third {C : Finset (Q 9)} {i : Fin 9} {r : Q 8} {j k : Fin 8}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hjk : j ≠ k)
    (hspoke : ∀ a t, liftVertex i t (flip r a) ∈ C)
    (hoccupied : ∃ t, liftVertex i t (corner r j k) ∈ C) :
    ∃ (t : Bool) (d : Fin 8),
      liftVertex i t (corner r j k) ∈ C ∧ liftVertex i (!t) (corner r j k) ∉ C ∧
      d ≠ j ∧ d ≠ k ∧ liftVertex i t (flip (corner r j k) d) ∈ C := by
  obtain ⟨t, ht⟩ := hoccupied
  have hsingle : liftVertex i (!t) (corner r j k) ∉ C := by
    intro h
    exact no_selected_square hb (Fin.succAbove_ne i k).symm (hspoke j t)
      (by simpa only [flip_insert] using hspoke j (!t))
      (by simpa only [flip_lift_transverse] using ht)
      (by simpa only [flip_insert, flip_lift_transverse] using h)
  let N := directions C (liftVertex i t (corner r j k))
  have hN : N.card = 3 := regular_directions C hr ht
  have hj : i.succAbove j ∈ N := (mem_directions _ _ _).mpr (by
    simpa only [flip_lift_transverse, corner_back_first] using hspoke k t)
  have hk : i.succAbove k ∈ N := (mem_directions _ _ _).mpr (by
    simpa only [flip_lift_transverse, BalancedCriticalSpectrum.flip_flip] using hspoke j t)
  have hAxes : i.succAbove j ≠ i.succAbove k :=
    fun h => hjk (Fin.succAbove_right_injective h)
  have hk' : i.succAbove k ∈ N.erase (i.succAbove j) := mem_erase.mpr ⟨hAxes.symm, hk⟩
  have hrest : ((N.erase (i.succAbove j)).erase (i.succAbove k)).card = 1 := by
    rw [card_erase_of_mem hk', card_erase_of_mem hj, hN]
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < ((N.erase (i.succAbove j)).erase
    (i.succAbove k)).card by rw [hrest] <;> decide)
  obtain ⟨hak, ha'⟩ := mem_erase.mp ha
  obtain ⟨haj, haN⟩ := mem_erase.mp ha'
  have haz : flip (liftVertex i t (corner r j k)) a ∈ C :=
    (mem_directions _ _ _).mp haN
  have hai : a ≠ i := by
    intro h
    subst a
    exact hsingle (by simpa only [flip_insert] using haz)
  obtain ⟨d, rfl⟩ := Fin.exists_succAbove_eq hai
  exact ⟨t, d, ht, hsingle, fun h => haj (congrArg (Fin.succAbove i) h),
    fun h => hak (congrArg (Fin.succAbove i) h),
    by simpa only [flip_lift_transverse] using haz⟩

/-- The two disjoint families in the spoke parity have exactly sixteen actual
vertices each. The first consists of all lifted spokes. The second consists
of the third neighbors of the sixteen selected mixed corners. -/
theorem eight_star_ambient_count {C : Finset (Q 9)} {i : Fin 9} {r : Q 8}
    {A B : Finset (Fin 8)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hA : A.card = 4) (hB : B.card = 4) (hAB : Disjoint A B)
    (hspoke : ∀ a t, liftVertex i t (flip r a) ∈ C)
    (hmixed : ∀ j ∈ A, ∀ k ∈ B, ∃ t, liftVertex i t (corner r j k) ∈ C) :
    ∃ (layer : (↥A × ↥B) → Bool) (extra : (↥A × ↥B) → Fin 8),
      (∀ x : ↥A × ↥B,
        liftVertex i (layer x) (corner r x.1 x.2) ∈ C ∧
        liftVertex i (!(layer x)) (corner r x.1 x.2) ∉ C ∧
        extra x ≠ (x.1 : Fin 8) ∧ extra x ≠ (x.2 : Fin 8) ∧
        liftVertex i (layer x) (flip (corner r x.1 x.2) (extra x)) ∈ C) ∧
      ∃ L T : Finset (Q 9),
        L = univ.image (fun x : Bool × Fin 8 => liftVertex i x.1 (flip r x.2)) ∧
        T = univ.image (fun x : ↥A × ↥B =>
          liftVertex i (layer x) (flip (corner r x.1 x.2) (extra x))) ∧
        L.card = 16 ∧ T.card = 16 ∧ Disjoint L T ∧
        L ∪ T ⊆ projectedVertices C i (!cubeParity r) ∧
        32 ≤ (projectedVertices C i (!cubeParity r)).card := by
  classical
  let q (x : ↥A × ↥B) := corner r x.1 x.2
  have hne (x : ↥A × ↥B) : (x.1 : Fin 8) ≠ (x.2 : Fin 8) := by
    intro h
    exact Finset.disjoint_left.mp hAB x.1.property (h.symm ▸ x.2.property)
  have hlabel (x : ↥A × ↥B) : diff r (q x) = {↑x.1, ↑x.2} :=
    diff_double_flip r (hne x)
  have hq : Function.Injective q := by
    intro x y he
    have hlabels : ({↑x.1, ↑x.2} : Finset (Fin 8)) = {↑y.1, ↑y.2} := by
      rw [← hlabel x, ← hlabel y, he]
    have hleft : (x.1 : Fin 8) = (y.1 : Fin 8) := by
      have hm : (x.1 : Fin 8) ∈ ({↑y.1, ↑y.2} : Finset (Fin 8)) := by
        rw [← hlabels] <;> simp
      simp only [mem_insert, mem_singleton] at hm
      exact hm.elim id (fun h => (Finset.disjoint_left.mp hAB
        x.1.property (h.symm ▸ y.2.property)).elim)
    have hright : (x.2 : Fin 8) = (y.2 : Fin 8) := by
      have hm : (x.2 : Fin 8) ∈ ({↑y.1, ↑y.2} : Finset (Fin 8)) := by
        rw [← hlabels] <;> simp
      simp only [mem_insert, mem_singleton] at hm
      exact hm.elim (fun h => (Finset.disjoint_left.mp hAB
        y.1.property (h ▸ x.2.property)).elim) id
    exact Prod.ext (Subtype.ext hleft) (Subtype.ext hright)
  have hthird (x : ↥A × ↥B) : ∃ (t : Bool) (d : Fin 8),
      liftVertex i t (q x) ∈ C ∧ liftVertex i (!t) (q x) ∉ C ∧
      d ≠ (x.1 : Fin 8) ∧ d ≠ (x.2 : Fin 8) ∧
      liftVertex i t (flip (q x) d) ∈ C :=
    mixed_corner_third hr hb (hne x) hspoke (hmixed x.1 x.1.property x.2 x.2.property)
  choose layer extra hx hsingle hextraA hextraB hz using hthird
  let spoke (x : Bool × Fin 8) := liftVertex i x.1 (flip r x.2)
  let third (x : ↥A × ↥B) := liftVertex i (layer x) (flip (q x) (extra x))
  have hspoke_inj : Function.Injective spoke := by
    intro x y he
    have hLayer : x.1 = y.1 := by
      simpa only [spoke, liftVertex, Fin.insertNth_apply_same] using
        congrArg (fun v : Q 9 => v i) he
    have hProj : flip r x.2 = flip r y.2 := by
      simpa only [spoke, drop_insert] using congrArg (dropAxis i) he
    exact Prod.ext hLayer (flip_injective r hProj)
  have hthird_inj : Function.Injective third := by
    intro x y he
    by_contra hxy
    have hLayer : layer x = layer y := by
      simpa only [third, liftVertex, Fin.insertNth_apply_same] using
        congrArg (fun v : Q 9 => v i) he
    have hProj : flip (q x) (extra x) = flip (q y) (extra y) := by
      simpa only [third, drop_insert] using congrArg (dropAxis i) he
    have hqne : q x ≠ q y := fun h => hxy (hq h)
    obtain ⟨hExtra, hOpp, _⟩ := square_of_shared_row hqne hProj
    have hDist : (diff (q x) (q y)).card = 2 := by
      rw [← hOpp, diff_double_flip _ hExtra, card_pair hExtra]
    have hIntersection := diff_triangle_card (q x) (q y) r
    rw [hDist, diff_symm (q x) r, diff_symm (q y) r, hlabel x, hlabel y,
      card_pair (hne x), card_pair (hne y)] at hIntersection
    obtain ⟨a, ha⟩ := card_pos.mp (show
      0 < (({↑x.1, ↑x.2} : Finset (Fin 8)) ∩ {↑y.1, ↑y.2}).card by omega)
    obtain ⟨ax, hax, hqx⟩ := direction_to_shared_spoke r (mem_inter.mp ha).1
      (hextraA x) (hextraB x)
    obtain ⟨ay, hay, hqy⟩ := direction_to_shared_spoke r (mem_inter.mp ha).2
      (hextraA y) (hextraB y)
    have hsx : flip (flip r a) ax = q x := hqx
    have hsy : flip (flip r a) ay = q y := hqy
    let s := liftVertex i (layer x) (flip r a)
    have hx' : flip s (i.succAbove ax) ∈ C := by
      simpa only [s, flip_lift_transverse, hsx] using hx x
    have hy' : flip s (i.succAbove ay) ∈ C := by
      simpa only [s, flip_lift_transverse, hsy, hLayer] using hx y
    have hz' : flip (flip s (i.succAbove ax)) (i.succAbove (extra x)) ∈ C := by
      simpa only [s, flip_lift_transverse, hsx] using hz x
    have hPaths : flip (flip s (i.succAbove ax)) (i.succAbove (extra x)) =
        flip (flip s (i.succAbove ay)) (i.succAbove (extra y)) := by
      simp only [s, flip_lift_transverse, hsx, hsy, hProj]
    have hSame := two_step_first_direction_eq hb
      (fun h => hax (Fin.succAbove_right_injective h))
      (fun h => hay (Fin.succAbove_right_injective h))
      (hspoke a (layer x)) hx' hz' hy' hPaths
    exact hqne (hsx.symm.trans ((congrArg (flip (flip r a))
      (Fin.succAbove_right_injective hSame)).trans hsy))
  let L := univ.image spoke
  let T := univ.image third
  have hL : L.card = 16 := by
    simp only [L, card_image_of_injective _ hspoke_inj, card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin]
  have hT : T.card = 16 := by
    simp only [T, card_image_of_injective _ hthird_inj, card_univ, Fintype.card_prod,
      Fintype.card_coe, hA, hB]
  have hDisjoint : Disjoint L T := by
    apply Finset.disjoint_left.mpr
    intro v hvL hvT
    obtain ⟨x, _, hxv⟩ := mem_image.mp hvL
    obtain ⟨y, _, hyv⟩ := mem_image.mp hvT
    have he : flip (q y) (extra y) = flip r x.2 := by
      simpa only [spoke, third, drop_insert] using
        congrArg (dropAxis i) (hyv.trans hxv.symm)
    exact third_ne_spoke r (hne y) (hextraA y) (hextraB y) he
  have hSub : L ∪ T ⊆ projectedVertices C i (!cubeParity r) := by
    intro v hv
    simp only [projectedVertices, mem_filter]
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨x, _, rfl⟩ := mem_image.mp hv
      exact ⟨hspoke x.2 x.1, by
        simpa only [spoke, drop_insert, cubeParity] using parity_flip r x.2⟩
    · obtain ⟨x, _, rfl⟩ := mem_image.mp hv
      refine ⟨hz x, ?_⟩
      change cubeParity (dropAxis i (third x)) = !cubeParity r
      simp only [cubeParity, third, drop_insert, q, parity_flip, Bool.not_not]
  have h32 := card_le_card hSub
  rw [card_union_of_disjoint hDisjoint, hL, hT] at h32
  exact ⟨layer, extra, fun x => ⟨hx x, hsingle x, hextraA x, hextraB x, hz x⟩,
    L, T, rfl, rfl, hL, hT, hDisjoint, hSub, h32⟩

/-- The ambient eight-star count forces at least ten paired fibres on the
actual axial direction. -/
theorem directionEdges_ge_ten_of_eight_star {C : Finset (Q 9)} {i : Fin 9} {r : Q 8}
    {A B : Finset (Fin 8)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hA : A.card = 4) (hB : B.card = 4) (hAB : Disjoint A B)
    (hspoke : ∀ a t, liftVertex i t (flip r a) ∈ C)
    (hmixed : ∀ j ∈ A, ∀ k ∈ B, ∃ t, liftVertex i t (corner r j k) ∈ C) :
    10 ≤ directionEdges C i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h32⟩ :=
    eight_star_ambient_count hr hb hA hB hAB hspoke hmixed
  let p := !cubeParity r
  change 32 ≤ (projectedVertices C i p).card at h32
  have hVertices := card_projectedVertices C i p
  have hPartition := doubleFibres_partition C i p
  have hOccupied := occupied_fibre_identity hr hb i p
  have hParity : 3 * (projectedVertices C i p).card =
      8 * directionEdges C i + 2 * (doubleFibres C i p).card := by omega
  have hUpper : 3 * (projectedVertices C i p).card ≤ 10 * directionEdges C i := by omega
  omega

/-- Apply the ambient bound to the equality certificate from
Q9PositiveSpectrumApplication.positive_component_eight_star. Here K is
its projected component and occupied is its actual projected occupancy. -/
theorem directionEdges_ge_ten_of_star_certificate {C : Finset (Q 9)} {i : Fin 9}
    {K : Finset (Q 8)} {occupied : Q 8 → Bool}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hpaired : ∀ q ∈ K, ∀ t, liftVertex i t q ∈ C)
    (hoccupied : ∀ q, occupied q = true ↔
      liftVertex i false q ∈ C ∨ liftVertex i true q ∈ C)
    (hstar : ∃ A B : Finset (Q 8), A.card = 4 ∧ B.card = 4 ∧ Disjoint A B ∧
      A ∪ B = K ∧
      ∃! r : Q 8, occupied r = false ∧
        (∀ q, q ∈ K ↔ (hypercube 8).Adj r q) ∧
        (∀ j k : Fin 8, j ≠ k →
          (occupied (corner r j k) = true ↔
            (flip r j ∈ A ∧ flip r k ∈ B) ∨ (flip r j ∈ B ∧ flip r k ∈ A)))) :
    10 ≤ directionEdges C i := by
  obtain ⟨A, B, hA, hB, hAB, hUnion, r, ⟨_, hSpokes, hCorners⟩, _⟩ := hstar
  have hDirCard (P : Finset (Q 8)) (hP : P ⊆ K) : (directions P r).card = P.card := by
    rw [directions_card]
    congr 1
    ext q
    simp only [mem_filter]
    exact ⟨And.left, fun hq => ⟨hq, (hSpokes q).mp (hP hq)⟩⟩
  have hAd : (directions A r).card = 4 :=
    (hDirCard A (by intro q hq; exact hUnion ▸ mem_union_left B hq)).trans hA
  have hBd : (directions B r).card = 4 :=
    (hDirCard B (by intro q hq; exact hUnion ▸ mem_union_right A hq)).trans hB
  have hDisj : Disjoint (directions A r) (directions B r) :=
    Finset.disjoint_left.mpr fun {j} hj hk =>
      Finset.disjoint_left.mp hAB ((mem_directions A r j).mp hj) ((mem_directions B r j).mp hk)
  apply directionEdges_ge_ten_of_eight_star (r := r) hr hb hAd hBd hDisj
  · intro j t
    exact hpaired _ ((hSpokes _).mpr (flip_adj r j)) t
  · intro j hj k hk
    have hjA := (mem_directions A r j).mp hj
    have hkB := (mem_directions B r k).mp hk
    have hjk : j ≠ k := fun h => Finset.disjoint_left.mp hAB hjA (h.symm ▸ hkB)
    rcases (hoccupied _).mp ((hCorners j k hjk).mpr (Or.inl ⟨hjA, hkB⟩)) with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarAmbientCount
