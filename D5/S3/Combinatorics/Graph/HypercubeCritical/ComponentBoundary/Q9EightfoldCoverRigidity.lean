/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Sign rigidity at distance four for eightfold exterior covers in Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation

/-! The geometry of the two closest layers of distinct distance-four eightfold covers. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverRigidity

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsSwitching)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9EightfoldCoverLocal
  (eightfold_corner_rule selectedCorners transverseSign card_transverse_signs)
open Q9EightfoldCoverSeparation (EightfoldCover firstShell eightfold_cover_distance_ge_four
  eightfold_cover_shells_disjoint)
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_symm flip_decreases_distance eq_double_flip mem_firstShell cover_at_endpoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverSeparation
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private transverseSign_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverLocal

attribute [local instance] Classical.propDecidable

variable {C : Finset (Q 9)} {sigma : Q 9 → ℝ} {x y : Q 9} {k l : Fin 9}

/-- At distance four the closest endpoints agree on the two cover axes. -/
theorem distance_four_agree_on_axes
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    (hd : hammingDist x y = 4) : x k = y k ∧ x l = y l := by
  have hx' := eightfold_cover_distance_ge_four hr hs hx hy hne
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self (flip x k)))
    (Finset.mem_insert_self y {flip y l})
  have hy' := eightfold_cover_distance_ge_four hr hs hy hx hne.symm
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self (flip y l)))
    (Finset.mem_insert_self x {flip x k})
  constructor
  · by_contra hn
    have h := flip_decreases_distance (show k ∈ diff x y from Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hn⟩)
    omega
  · by_contra hn
    have h := flip_decreases_distance (show l ∈ diff y x from Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Ne.symm hn⟩)
    rw [hammingDist_comm y x] at h
    omega

private theorem axes_not_mem_diff (h : x k = y k ∧ x l = y l) :
    k ∉ diff x y ∧ l ∉ diff x y :=
  ⟨fun hk => (Finset.mem_filter.mp hk).2 h.1, fun hl => (Finset.mem_filter.mp hl).2 h.2⟩

private theorem complementary_flips {i j t u : Fin 9}
    (hd : hammingDist x y = 4)
    (hi : i ∈ diff x y) (hj : j ∈ diff x y) (ht : t ∈ diff x y) (hu : u ∈ diff x y)
    (hij : i ≠ j) (hit : i ≠ t) (hiu : i ≠ u) (hjt : j ≠ t) (hju : j ≠ u) (htu : t ≠ u) :
    flip (flip x i) j = flip (flip y t) u := by
  have hR : diff x y = {i, j, t, u} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact ht
      · exact hu
    · change (diff x y).card = 4 at hd
      rw [hd]
      simp [Finset.card_insert_of_notMem, hij, hit, hiu, hjt, hju, htu]
  apply (eq_double_flip hij ?_).symm
  rw [diff_symm x, diff_flip, diff_flip, ← diff_symm x y, hR]
  ext a
  simp [Ne.symm hit, Ne.symm hjt, Ne.symm hiu, Ne.symm hju, htu,
    Ne.symm htu]
  grind

private theorem corner_mem {i j : Fin 9} (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j)
    (hp : flip (flip x i) j ∈ C) : flip (flip x i) j ∈ selectedCorners C x k :=
  Finset.mem_filter.mpr ⟨hp, i, j, hik, hjk, hij, Or.inl rfl⟩

private theorem first_neighbor_mem_shell {t a : Fin 9} (hy : EightfoldCover C y l)
    (htl : t ≠ l) (hp : flip (flip y t) a ∈ C) :
    flip (flip y t) a ∈ firstShell y l ∪ selectedCorners C y l := by
  by_cases hal : a = l
  · subst a
    apply Finset.mem_union_left
    exact mem_firstShell.mpr ⟨flip y l, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
      t, htl, flip_comm y l t⟩
  · have hta : t ≠ a := by
      rintro rfl
      exact hy.1 (by simpa only [BalancedCriticalSpectrum.flip_flip] using hp)
    exact Finset.mem_union_right _ (corner_mem htl hal hta hp)

/-- The four differing coordinates span no corner in the first cover's closest layer. -/
theorem distance_four_near_corner_excluded
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    (hd : hammingDist x y = 4) {i j : Fin 9}
    (hi : x i ≠ y i) (hj : x j ≠ y j) (hij : i ≠ j) : flip (flip x i) j ∉ C := by
  obtain ⟨hk, hl⟩ := axes_not_mem_diff (distance_four_agree_on_axes hr hs hx hy hne hd)
  have hi' : i ∈ diff x y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hj' : j ∈ diff x y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hjErase : j ∈ (diff x y).erase i := Finset.mem_erase.mpr ⟨hij.symm, hj'⟩
  have hcard : (((diff x y).erase i).erase j).card = 2 := by
    rw [Finset.card_erase_of_mem hjErase, Finset.card_erase_of_mem hi']
    exact congrArg (fun n : ℕ => n - 1 - 1) hd
  obtain ⟨t, u, htu, hrest⟩ := Finset.card_eq_two.mp hcard
  have remaining (a : Fin 9) (ha : a ∈ ({t, u} : Finset (Fin 9))) :
      a ≠ j ∧ a ≠ i ∧ a ∈ diff x y := by
    rw [← hrest] at ha
    exact ⟨(Finset.mem_erase.mp ha).1, Finset.mem_erase.mp (Finset.mem_erase.mp ha).2⟩
  obtain ⟨htj, hti, ht⟩ := remaining t (Finset.mem_insert_self _ _)
  obtain ⟨huj, hui, hu⟩ := remaining u
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hpEq := complementary_flips hd hi' hj' ht hu hij hti.symm hui.symm htj.symm huj.symm htu
  intro hp
  have hik : i ≠ k := fun h => hk (h ▸ hi')
  have hjk : j ≠ k := fun h => hk (h ▸ hj')
  have hpx := corner_mem hik hjk hij hp
  have htl : t ≠ l := fun h => hl (h ▸ ht)
  have hpy := first_neighbor_mem_shell hy htl (show flip (flip y t) u ∈ C from hpEq ▸ hp)
  exact Finset.disjoint_left.mp (eightfold_cover_shells_disjoint hr hs hx hy hne)
    (Finset.mem_union_right _ hpx) (hpEq.symm ▸ hpy)

private def nearDirections (C : Finset (Q 9)) (x : Q 9) (k i : Fin 9) :
    Finset (Fin 9) :=
  (directions C (flip x i)).erase k

private theorem mem_nearDirections {i j : Fin 9} :
    j ∈ nearDirections C x k i ↔ j ≠ k ∧ flip (flip x i) j ∈ C := by
  rw [nearDirections, Finset.mem_erase, mem_directions]

private theorem card_nearDirections
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hx : EightfoldCover C x k) {i : Fin 9} (hik : i ≠ k) :
    (nearDirections C x k i).card = 2 := by
  have hm : k ∈ directions C (flip x i) := by
    rw [mem_directions, flip_comm x i k]
    exact (hx.2.2 i hik).2
  rw [nearDirections, Finset.card_erase_of_mem hm, regular_directions C hr (hx.2.2 i hik).1]

-- Count the edges between the independent four-set and its complement in both directions.
private theorem nearDirections_cross
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hx : EightfoldCover C x k) {R : Finset (Fin 9)}
    (hR : R.card = 4) (hk : k ∉ R)
    (hind : ∀ i ∈ R, ∀ j ∈ R, flip (flip x i) j ∉ C)
    {a : Fin 9} (hak : a ≠ k) (haR : a ∉ R) :
    nearDirections C x k a ⊆ R := by
  let U := Finset.univ.erase k
  let T := U \ R
  let N := nearDirections C x k
  have hU : U.card = 8 := by simp [U, Finset.card_erase_of_mem (Finset.mem_univ k)]
  have hsub : R ⊆ U :=
    fun i hi => Finset.mem_erase.mpr ⟨fun h => hk (h ▸ hi), Finset.mem_univ _⟩
  have hT : T.card = 4 := by rw [Finset.card_sdiff_of_subset hsub, hU, hR]
  have hN {i : Fin 9} (hi : i ∈ U) : (N i).card = 2 :=
    card_nearDirections hr hx (Finset.mem_erase.mp hi).1
  have hNT {i : Fin 9} (hi : i ∈ R) : N i ⊆ T := by
    intro j hj
    obtain ⟨hjk, hc⟩ := mem_nearDirections.mp hj
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩, fun hjR => hind i hi j hjR hc⟩
  have hsum : ∑ i ∈ T, (R.filter fun j => j ∈ N i).card = T.card * 2 := by
    calc
      _ = ∑ i ∈ T, ∑ j ∈ R, if j ∈ N i then (1 : ℕ) else 0 := by
        simp only [Finset.sum_boole, Nat.cast_id]
      _ = ∑ j ∈ R, ∑ i ∈ T, if j ∈ N i then (1 : ℕ) else 0 :=
        Finset.sum_comm
      _ = ∑ j ∈ R, ∑ i ∈ T, if i ∈ N j then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        have hjk : j ≠ k := (Finset.mem_erase.mp (hsub hj)).1
        have hik : i ≠ k := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).1
        have hji : j ∈ N i ↔ i ∈ N j := by
          rw [mem_nearDirections, mem_nearDirections, flip_comm x i j]
          exact ⟨fun h => ⟨hik, h.2⟩, fun h => ⟨hjk, h.2⟩⟩
        simp only [hji]
      _ = ∑ j ∈ R, (N j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.card_eq_sum_ite (hNT hj)).symm
      _ = T.card * 2 := by
        rw [Finset.sum_congr rfl (fun j hj => hN (hsub hj))]
        simp [hR, hT]
  have hfilter (i : Fin 9) : R.filter (fun j => j ∈ N i) ⊆ N i :=
    fun _ h => (Finset.mem_filter.mp h).2
  have ha : a ∈ T :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hak, Finset.mem_univ a⟩, haR⟩
  have heq : R.filter (fun j => j ∈ N a) = N a := by
    apply Finset.eq_of_subset_of_card_le (hfilter a)
    by_contra! hlt
    have hlt' : (R.filter fun j => j ∈ N a).card < 2 := by
      rwa [← hN (Finset.mem_sdiff.mp ha).1]
    have h := Finset.sum_lt_sum (s := T)
      (f := fun i => (R.filter fun j => j ∈ N i).card) (g := fun _ => 2)
      (fun i hi => (Finset.card_le_card (hfilter i)).trans (hN (Finset.mem_sdiff.mp hi).1).le)
      ⟨a, ha, hlt'⟩
    simp [hsum] at h
  intro i hi
  change i ∈ N a at hi
  rw [← heq] at hi
  exact (Finset.mem_filter.mp hi).1

private theorem far_corner_of_sign_ne
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k)
    {i j : Fin 9} (hik : i ≠ k) (hjk : j ≠ k)
    (hout : flip (flip x i) j ∉ C) (hsgn : transverseSign sigma x i ≠ transverseSign sigma x j) :
    flip (flip (flip x i) j) k ∈ C := by
  by_contra h
  exact hsgn ((eightfold_corner_rule hr hs hx.1 hx.2.1 hx.2.2 hik hjk).1.mpr ⟨hout, h⟩)

private theorem mixed_far_neighbors
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k)
    {R : Finset (Fin 9)} (hR : R.card = 4) (hk : k ∉ R)
    (hind : ∀ i ∈ R, ∀ j ∈ R, flip (flip x i) j ∉ C)
    {a w : Fin 9} (ha : a ∈ R) (hw : w ∈ R)
    (hwa : transverseSign sigma x w ≠ transverseSign sigma x a) :
    ∃ b ∈ R, ∃ c ∈ R, ∃ d ∈ R, b ≠ a ∧ c ≠ a ∧ d ≠ a ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      flip (flip (flip x b) c) k ∈ C ∧ flip (flip (flip x b) d) k ∈ C := by
  let s := transverseSign sigma x
  have htrans {i : Fin 9} (hi : i ∈ R) : i ≠ k := fun h => hk (h ▸ hi)
  have hfar {i j : Fin 9} (hi : i ∈ R) (hj : j ∈ R) (hne : s i ≠ s j) :
      flip (flip (flip x i) j) k ∈ C :=
    far_corner_of_sign_ne hr hs hx (htrans hi) (htrans hj) (hind i hi j hj) hne
  have hcard {i : Fin 9} (hi : i ∈ R) : (R.filter fun j => s j ≠ s i).card ≤ 2 := by
    have hx' : EightfoldCover C (flip x k) k :=
      (cover_at_endpoint hx (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).1
    rw [← card_nearDirections hr hx' (htrans hi)]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hjR, hjn⟩ := Finset.mem_filter.mp hj
    apply mem_nearDirections.mpr
    refine ⟨htrans hjR, ?_⟩
    rw [flip_comm x k i, flip_comm (flip x i) k j]
    exact hfar hi hjR (Ne.symm hjn)
  let A := R.filter fun j => s j = s a
  let B := R.filter fun j => s j ≠ s a
  have hA : A.card ≤ 2 :=
    (Finset.card_le_card (show A ⊆ R.filter (fun j => s j ≠ s w) by
      intro j hj
      obtain ⟨hjR, hjA⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjR, fun h => hwa (h.symm.trans hjA)⟩)).trans (hcard hw)
  have hB : B.card ≤ 2 := hcard ha
  have hsum : A.card + B.card = 4 :=
    (Finset.card_filter_add_card_filter_not (s := R) (fun j => s j = s a)).trans hR
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (show 1 < A.card by omega) a
  obtain ⟨c, d, hcd, hBpair⟩ := Finset.card_eq_two.mp (show B.card = 2 by omega)
  have hc : c ∈ B := by simp [hBpair]
  have hd : d ∈ B := by simp [hBpair]
  obtain ⟨hbR, hbs⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcR, hcs⟩ := Finset.mem_filter.mp hc
  obtain ⟨hdR, hds⟩ := Finset.mem_filter.mp hd
  have hbc : s b ≠ s c := fun h => hcs (h.symm.trans hbs)
  have hbd : s b ≠ s d := fun h => hds (h.symm.trans hbs)
  exact ⟨b, hbR, c, hcR, d, hdR, hba, fun h => hcs (congrArg s h),
    fun h => hds (congrArg s h), fun h => hbc (congrArg s h), fun h => hbd (congrArg s h),
    hcd, hfar hbR hcR hbc, hfar hbR hdR hbd⟩

private theorem distance_four_sign_constant
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    (hd : hammingDist x y = 4) :
    ∀ i ∈ diff x y, ∀ j ∈ diff x y, transverseSign sigma x i = transverseSign sigma x j := by
  let R := diff x y
  have hR : R.card = 4 := hd
  obtain ⟨hk, hl⟩ := axes_not_mem_diff (distance_four_agree_on_axes hr hs hx hy hne hd)
  have hxind (i : Fin 9) (hi : i ∈ R) (j : Fin 9) (hj : j ∈ R) :
      flip (flip x i) j ∉ C := by
    by_cases hij : i = j
    · simpa only [hij, BalancedCriticalSpectrum.flip_flip] using hx.1
    · exact distance_four_near_corner_excluded hr hs hx hy hne hd
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij
  have hyind (i : Fin 9) (hi : i ∈ R) (j : Fin 9) (hj : j ∈ R) :
      flip (flip y i) j ∉ C := by
    by_cases hij : i = j
    · simpa only [hij, BalancedCriticalSpectrum.flip_flip] using hy.1
    · exact distance_four_near_corner_excluded hr hs hy hx hne.symm
        ((hammingDist_comm y x).trans hd)
        (Ne.symm (Finset.mem_filter.mp hi).2) (Ne.symm (Finset.mem_filter.mp hj).2) hij
  intro i hi j hj
  by_contra hij
  have witnesses (a : Fin 9) (ha : a ∈ R) :
      ∃ b ∈ R, ∃ c ∈ R, ∃ d ∈ R, b ≠ a ∧ c ≠ a ∧ d ≠ a ∧
        b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        flip (flip (flip x b) c) k ∈ C ∧ flip (flip (flip x b) d) k ∈ C := by
    by_cases h : transverseSign sigma x i = transverseSign sigma x a
    · exact mixed_far_neighbors hr hs hx hR hk hxind ha hj (fun he => hij (h.trans he.symm))
    · exact mixed_far_neighbors hr hs hx hR hk hxind ha hi h
  have hxk {a : Fin 9} (ha : a ∈ R) : a ≠ k := fun he => hk (he ▸ ha)
  have hyl {a : Fin 9} (ha : a ∈ R) : a ≠ l := fun he => hl (he ▸ ha)
  by_cases hkl : k = l
  · -- Parallel covers share a far corner as soon as a mixed pair occurs.
    obtain ⟨b, hb, c, hc, d, hdR, hbi, hci, hdi, hbc, hbd, hcd, hq, _⟩ := witnesses i hi
    have he := complementary_flips hd hb hc hi hdR hbc hbi hbd hci hcd hdi.symm
    have hq' : flip (flip (flip y i) d) l ∈ C := by rwa [← hkl, ← he]
    have hX : flip (flip (flip x b) c) k ∈ selectedCorners C x k :=
      Finset.mem_filter.mpr ⟨hq, b, c, hxk hb, hxk hc, hbc, Or.inr rfl⟩
    have hY : flip (flip (flip x b) c) k ∈ selectedCorners C y l := by
      rw [he, hkl]
      exact Finset.mem_filter.mpr ⟨hq', i, d, hyl hi, hyl hdR, hdi.symm, Or.inr rfl⟩
    exact Finset.disjoint_left.mp (eightfold_cover_shells_disjoint hr hs hx hy hne)
      (Finset.mem_union_right _ hX) (Finset.mem_union_right _ hY)
  · -- The transverse axis k in the second cover leads to a corner of degree at least four.
    have hcross := nearDirections_cross hr hy hR hl hyind hkl hk
    obtain ⟨a, ha⟩ := Finset.card_pos.mp
      (show 0 < (nearDirections C y l k).card by rw [card_nearDirections hr hy hkl]; decide)
    have haR := hcross ha
    let p := flip (flip y k) a
    have hp : p ∈ C := (mem_nearDirections.mp ha).2
    obtain ⟨b, hb, c, hc, d, hdR, hba, hca, hda, hbc, hbd, hcd, hq, hq'⟩ := witnesses a haR
    have hkp : flip p k ∈ C := by
      dsimp only [p]
      rw [flip_comm (flip y k) a k, BalancedCriticalSpectrum.flip_flip]
      exact (hy.2.2 a (hyl haR)).1
    have hap : flip p a ∈ C := by
      dsimp only [p]
      rw [BalancedCriticalSpectrum.flip_flip]
      exact (hy.2.2 k hkl).1
    have hdp : flip p d ∈ C := by
      dsimp only [p]
      rw [flip_comm y k a, flip_comm (flip y a) k d,
        ← complementary_flips hd hb hc haR hdR hbc hba hbd hca hcd hda.symm]
      exact hq
    have hcp : flip p c ∈ C := by
      dsimp only [p]
      rw [flip_comm y k a, flip_comm (flip y a) k c,
        ← complementary_flips hd hb hdR haR hc hbd hba hbc hda hcd.symm hca.symm]
      exact hq'
    have hfour : ({k, a, c, d} : Finset (Fin 9)).card = 4 :=
      Finset.card_eq_four.mpr
        ⟨k, a, c, d, (hxk haR).symm, (hxk hc).symm, (hxk hdR).symm, hca.symm, hda.symm, hcd, rfl⟩
    have hsub : ({k, a, c, d} : Finset (Fin 9)) ⊆ directions C p := by
      intro t ht
      apply (mem_directions _ _ _).mpr
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hkp
      · exact hap
      · exact hcp
      · exact hdp
    have hle := Finset.card_le_card hsub
    rw [hfour, regular_directions C hr hp] at hle
    omega

private theorem distance_four_sign_class
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    (hd : hammingDist x y = 4) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      diff x y = (Finset.univ.erase k).filter (fun i => transverseSign sigma x i = s) := by
  have hcard : (diff x y).card = 4 := hd
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (diff x y).card by omega)
  have hk := (axes_not_mem_diff (distance_four_agree_on_axes hr hs hx hy hne hd)).1
  have htrans {i : Fin 9} (hi : i ∈ diff x y) : i ≠ k := fun h => hk (h ▸ hi)
  have hsign := transverseSign_unit hs (hx.2.2 a (htrans ha)).1
  refine ⟨transverseSign sigma x a, hsign, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨htrans hi, Finset.mem_univ i⟩,
        distance_four_sign_constant hr hs hx hy hne hd i hi a ha⟩
  · rw [hcard]
    obtain ⟨hpos, hneg⟩ := card_transverse_signs hr hs hx.1 hx.2.1 (fun i hi => (hx.2.2 i hi).1)
    rcases hsign with h | h
    · rw [h, hpos]
    · rw [h, hneg]

/-- At minimum endpoint distance four, the differing coordinates form a whole
Huang sign class at each closest endpoint, for parallel and nonparallel covers. -/
theorem distance_four_sign_rigidity
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma) (hx : EightfoldCover C x k) (hy : EightfoldCover C y l)
    (hne : ({x, flip x k} : Finset (Q 9)) ≠ {y, flip y l})
    (hd : hammingDist x y = 4) :
    let R := Finset.univ.filter (fun i : Fin 9 => x i ≠ y i)
    ∃ sx sy : ℝ, (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
      R = (Finset.univ.erase k).filter (fun i => transverseSign sigma x i = sx) ∧
      R = (Finset.univ.erase l).filter (fun i => transverseSign sigma y i = sy) := by
  obtain ⟨sx, hsx, hxR⟩ := distance_four_sign_class hr hs hx hy hne hd
  obtain ⟨sy, hsy, hyR⟩ := distance_four_sign_class hr hs hy hx hne.symm
    ((hammingDist_comm y x).trans hd)
  exact ⟨sx, sy, hsx, hsy, hxR, (diff_symm x y).trans hyR⟩

#print axioms distance_four_agree_on_axes
#print axioms distance_four_near_corner_excluded
#print axioms distance_four_sign_rigidity

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightfoldCoverRigidity
