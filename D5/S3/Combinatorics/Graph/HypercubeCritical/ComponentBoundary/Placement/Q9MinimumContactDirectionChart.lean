/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumContactDirectionChart
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumContactDirectionChart
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A fixed translation class of unshared distance-three endpoints contains at least eighteen vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.DistanceThreeTripleFamilyBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedDirections

/-! Counting the near endpoints in an orbit chart of the nine-cube. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumContactDirectionChart

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9TriplePartitions (IsTriplePartition neighborPartition)
open Q9DistanceThreeUnsharedDirections (directionOrigin unsharedContactAxes
  axes_and_partition_of_unshared_contacts unshared_two_step_preserves_direction_origin)
open DistanceThreeTripleFamilyBound (codegree card_ge_eighteen)
open private differingAxes foldl_flip_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private directions_subset_agreement from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
open private mem_diff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private extensions mem_extensions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
open private exists_erase_eq card_extensions_eq_codegree freshExtensions
  mem_freshExtensions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.DistanceThreeTripleFamilyBound

private noncomputable def point (o : Q 9) (S : Finset (Fin 9)) : Q 9 :=
  S.toList.foldl flip o

private theorem point_flip_insert (o : Q 9) {S : Finset (Fin 9)} {i : Fin 9} (hi : i ∉ S) :
    flip (point o S) i = point o (insert i S) := by
  funext j
  have hs (T : Finset (Fin 9)) : point o T j = if j ∈ T then !o j else o j := by
    rw [point, foldl_flip_apply _ (nodup_toList _)]
    simp only [mem_toList]
  by_cases hji : j = i
  · subst j
    rw [BalancedCriticalSpectrum.flip_apply_same, hs, hs, ite_eq_right hi,
      ite_eq_left (mem_insert_self _ _)]
  · simp only [BalancedCriticalSpectrum.flip, Function.update_of_ne hji, hs, mem_insert,
      hji, false_or]

private theorem point_origin (D : Finset (Q 9)) (y : Q 9) :
    point (directionOrigin D y) (directions D y) = y := by
  funext i
  simp only [point, directionOrigin, foldl_flip_apply _ (nodup_toList _), mem_toList]
  by_cases h : i ∈ directions D y <;> simp [h]

open Classical in
/-- For two balanced cubic supports at separation three, if all closest
contacts have disjoint occupied directions then every nonempty class of
near endpoints with fixed translated vertex has at least eighteen elements. -/
theorem eighteen_endpoints_of_fixed_direction_origin
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 3 ≤ hammingDist u v)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    (o : Q 9)
    (hne : ∃ y ∈ D, directionOrigin D y = o ∧ ∃ x ∈ C, hammingDist x y = 3) :
    18 ≤ (D.filter fun y => directionOrigin D y = o ∧ ∃ x ∈ C, hammingDist x y = 3).card := by
  let Y := D.filter fun y => directionOrigin D y = o ∧ ∃ x ∈ C, hammingDist x y = 3
  let H := Y.image (directions D)
  have hy {y : Q 9} (hy : y ∈ Y) :
      y ∈ D ∧ directionOrigin D y = o ∧ ∃ x ∈ C, hammingDist x y = 3 := mem_filter.mp hy
  have hpoint {y : Q 9} (hy' : y ∈ Y) : point o (directions D y) = y := by
    rw [← (hy hy').2.1]
    exact point_origin D y
  have hsize {T : Finset (Fin 9)} (hT : T ∈ H) : T.card = 3 := by
    obtain ⟨y, hy', rfl⟩ := mem_image.mp hT
    exact regular_directions D hrD (hy hy').1
  have hpivot {y : Q 9} (hy' : y ∈ Y) {e : Fin 9} (he : e ∈ directions D y) :
      point o ((directions D y).erase e) = flip y e := by
    have h := point_flip_insert o (notMem_erase e (directions D y))
    rw [insert_erase he, hpoint hy'] at h
    simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun z : Q 9 => BalancedCriticalSpectrum.flip z e) h
  have hsub {T : Finset (Fin 9)} (e : Fin 9) :
      extensions H (T.erase e) ⊆ directions D (point o (T.erase e)) := by
    intro p hp
    obtain ⟨hpe, hH⟩ := mem_extensions.mp hp
    obtain ⟨v, hv, hdir⟩ := mem_image.mp hH
    apply (mem_directions D _ p).mpr
    rw [point_flip_insert o hpe, ← hdir, hpoint hv]
    exact (hy hv).1
  have hcdeg {T : Finset (Fin 9)} (hT : T ∈ H) {e : Fin 9} (he : e ∈ T) :
      (freshExtensions H T e).card + 1 = codegree H (T.erase e) := by
    have hex : e ∈ extensions H (T.erase e) := mem_extensions.mpr
      ⟨notMem_erase _ _, by rwa [insert_erase he]⟩
    rw [freshExtensions, card_erase_add_one hex]
    apply card_extensions_eq_codegree
    intro V hV
    rw [hsize hV, card_erase_of_mem he, hsize hT]
  have hupper {T : Finset (Fin 9)} (hT : T ∈ H) {e : Fin 9} (he : e ∈ T) :
      (freshExtensions H T e).card ≤ 2 := by
    have hcard := hcdeg hT he
    have hcap := card_le_card (hsub (T := T) e)
    rw [card_extensions_eq_codegree (fun V hV => by rw [hsize hV, card_erase_of_mem he, hsize hT])] at hcap
    obtain ⟨y, hy', rfl⟩ := mem_image.mp hT
    rw [hpivot hy' he, regular_directions D hrD ((mem_directions D y e).mp he)] at hcap
    omega
  have haxes {T : Finset (Fin 9)} (hT : T ∈ H) :
      5 ≤ ∑ e ∈ T, (freshExtensions H T e).card := by
    obtain ⟨y, hy', rfl⟩ := mem_image.mp hT
    obtain ⟨hyD, hyo, hyn⟩ := hy hy'
    obtain ⟨hcard, _⟩ := axes_and_partition_of_unshared_contacts hrC hrD hbC hbD hsep hyD
      hyn (fun x hx hd => hdis x hx y hyD hd)
    suffices hs : unsharedContactAxes C y ⊆ (directions D y).biUnion (freshExtensions H (directions D y)) from
      (hcard.trans (card_le_card hs)).trans card_biUnion_le
    intro p hp
    unfold unsharedContactAxes at hp
    obtain ⟨x, hx, hp⟩ := mem_biUnion.mp hp
    obtain ⟨hxC, hdist⟩ := mem_filter.mp hx
    obtain ⟨e, he, hzD, hzDist, hzDir, hzO⟩ :=
      unshared_two_step_preserves_direction_origin hrC hrD hbC hbD hsep hdis hxC hyD hdist
        ((mem_diff x y p).mp hp)
    let z := flip (flip y e) p
    have hz : z ∈ Y := mem_filter.mpr ⟨hzD, hzO.trans hyo, x, hxC, hzDist⟩
    have hpE : p ∉ directions D y := by
      intro hpE
      have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
          hammingDist y x ≤ hammingDist v u := by
        rw [hammingDist_comm y x, hammingDist_comm v u, hdist]
        exact hsep u hu v hv
      have hsub := directions_subset_agreement hxC (C := D) (D := C) (x := y)
        (fun u hu v hv => hm v hv u hu)
      exact (mem_diff x y p).mp hp (mem_filter.mp (hsub hpE)).2.symm
    refine mem_biUnion.mpr ⟨e, he, mem_erase.mpr ⟨fun h => hpE (h.symm ▸ he), ?_⟩⟩
    refine mem_extensions.mpr ⟨fun h => hpE (mem_of_mem_erase h), ?_⟩
    exact mem_image.mpr ⟨z, hz, hzDir⟩
  have hcodegree {T : Finset (Fin 9)} (hT : T ∈ H) {e : Fin 9} (he : e ∈ T) :
      2 ≤ codegree H (T.erase e) ∧ codegree H (T.erase e) ≤ 3 := by
    have hc := hcdeg hT he
    have hu := hupper hT he
    have hs := haxes hT
    have hrest : ∑ i ∈ T.erase e, (freshExtensions H T i).card ≤ 4 := by
      calc
        _ ≤ ∑ _i ∈ T.erase e, (2 : ℕ) := sum_le_sum fun i hi => hupper hT (mem_of_mem_erase hi)
        _ = _ := by simp [card_erase_of_mem he, hsize hT]
    have hsplit := sum_erase_add T (fun i => (freshExtensions H T i).card) he
    omega
  have hlow {T : Finset (Fin 9)} (hT : T ∈ H) :
      (T.filter fun i => codegree H (T.erase i) = 2).card ≤ 1 := by
    let L := T.filter fun i => codegree H (T.erase i) = 2
    have hL : L ⊆ T := filter_subset _ _
    have hcard := card_sdiff_of_subset hL
    have hsumL : ∑ i ∈ L, (freshExtensions H T i).card = L.card := by
      rw [sum_const_nat (m := 1) (fun i hi => by
        obtain ⟨hiT, hiD⟩ := mem_filter.mp hi
        have h := hcdeg hT hiT
        omega), Nat.mul_one]
    have hsumH : ∑ i ∈ T \ L, (freshExtensions H T i).card ≤ 2 * (T \ L).card := by
      calc
        _ ≤ ∑ _i ∈ T \ L, (2 : ℕ) :=
          sum_le_sum fun _ hi => hupper hT (mem_sdiff.mp hi).1
        _ = _ := by simp [Nat.mul_comm]
    have hs := sum_sdiff (f := fun i => (freshExtensions H T i).card) hL
    rw [hsize hT] at hcard
    have hl : 5 ≤ 2 * (3 - L.card) + L.card := by
      calc
        5 ≤ ∑ i ∈ T, (freshExtensions H T i).card := haxes hT
        _ = (∑ i ∈ T \ L, (freshExtensions H T i).card) +
            ∑ i ∈ L, (freshExtensions H T i).card := hs.symm
        _ ≤ 2 * (T \ L).card + L.card := Nat.add_le_add hsumH (le_of_eq hsumL)
        _ = _ := by rw [hcard]
    have hLcap : L.card ≤ 3 := (card_le_card hL).trans_eq (hsize hT)
    change L.card ≤ 1
    omega
  have hfreshDisj {T : Finset (Fin 9)} (hT : T ∈ H) {e f : Fin 9} (he : e ∈ T)
      (hf : f ∈ T) (hef : e ≠ f) : Disjoint (freshExtensions H T e) (freshExtensions H T f) := by
    obtain ⟨y, hy', rfl⟩ := mem_image.mp hT
    obtain ⟨hyD, _, hyn⟩ := hy hy'
    obtain ⟨_, hp⟩ := axes_and_partition_of_unshared_contacts hrC hrD hbC hbD hsep hyD
      hyn (fun x hx hd => hdis x hx y hyD hd)
    let B (e : Fin 9) := directions D (flip y e)
    have hB (e : Fin 9) (he : e ∈ directions D y) : B e ∈ neighborPartition D y :=
      mem_image.mpr ⟨e, he, rfl⟩
    have hinj : Set.InjOn B (directions D y : Set (Fin 9)) := by
      apply card_image_iff.mp
      exact hp.card_eq.trans (regular_directions D hrD hyD).symm
    have hd := hp.disjoint_blocks (hB e he) (hB f hf) (fun h => hef (hinj he hf h))
    refine hd.mono ?_ ?_
    · simpa only [freshExtensions, B, hpivot hy' he] using (erase_subset e _).trans (hsub (T := directions D y) e)
    · simpa only [freshExtensions, B, hpivot hy' hf] using (erase_subset f _).trans (hsub (T := directions D y) f)
  have hfour (W : Finset (Fin 9)) (hW : W.card = 4) : (H.filter fun T => T ⊆ W).card ≤ 2 := by
    let Hw := H.filter fun T => T ⊆ W
    change Hw.card ≤ 2
    by_cases hn : Hw.Nonempty
    · obtain ⟨T, hTw⟩ := hn
      obtain ⟨hT, hTW⟩ := mem_filter.mp hTw
      obtain ⟨p, hpW, heW⟩ := exists_erase_eq hTW (by rw [hW, hsize hT])
      have hpT : p ∉ T := fun h => notMem_erase p W (heW.symm ▸ h)
      have hWT : insert p T = W := by rw [← heW, insert_erase hpW]
      have hother {V : Finset (Fin 9)} (hVw : V ∈ Hw) (hVT : V ≠ T) :
          ∃ e ∈ T, p ∈ freshExtensions H T e ∧ V = insert p (T.erase e) := by
        obtain ⟨hV, hVW⟩ := mem_filter.mp hVw
        obtain ⟨e, heW, heV⟩ := exists_erase_eq hVW (by rw [hW, hsize hV])
        rw [← hWT] at heW heV
        have hep : e ≠ p := by
          intro h
          subst e
          exact hVT (heV.symm.trans (erase_insert hpT))
        have he := (mem_insert.mp heW).resolve_left hep
        rw [erase_insert_of_ne hep.symm] at heV
        exact ⟨e, he, mem_erase.mpr ⟨hep.symm,
          mem_extensions.mpr ⟨fun h => hpT (mem_of_mem_erase h), heV.symm ▸ hV⟩⟩, heV.symm⟩
      have hsame {V U : Finset (Fin 9)} (hVw : V ∈ Hw) (hUw : U ∈ Hw)
          (hVT : V ≠ T) (hUT : U ≠ T) : V = U := by
        obtain ⟨e, he, hpE, rfl⟩ := hother hVw hVT
        obtain ⟨f, hf, hpF, rfl⟩ := hother hUw hUT
        have hef : e = f := by
          by_contra h
          exact disjoint_left.mp (hfreshDisj hT he hf h) hpE hpF
        rw [hef]
      rw [← Fintype.card_bool, ← card_univ]
      apply card_le_card_of_injOn (fun V => decide (V = T)) (fun V _ => mem_univ _)
      intro V hV U hU heq
      by_cases hVT : V = T
      · subst V
        simp at heq
        exact heq.symm
      · apply hsame hV hU hVT
        simp [hVT] at heq
        exact heq
    · simp [not_nonempty_iff_eq_empty.mp hn]
  have hHne : H.Nonempty := by
    obtain ⟨y, hy, ho, hn⟩ := hne
    exact ⟨directions D y, mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, ho, hn⟩, rfl⟩⟩
  exact (card_ge_eighteen H hHne (fun _ => hsize) (fun _ hT _ => hcodegree hT)
    (fun _ => hlow) hfour).trans card_image_le

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumContactDirectionChart
