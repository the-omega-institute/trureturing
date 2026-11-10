/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryPhysicalSteps
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryPhysicalSteps
   mirror-E: none(waiver:original-mask-history-recursion)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Original-mask usable physical leaves, decreasing local solver and mixed-history recursion. -/

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryFactors
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLocalLeaves
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryForests
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntact
import D5.S3.Geometry.OriginalLabelTwoSum.HistorySeed

/-! These are actual proof bodies for the physical induction. The local solver
recurses on the complete remaining local ground, and allCornersOutput supplies
its external old-corner input by genuine MixedHistory induction.
The only external physical recursive supplier is on the graph of the OLD history.
The local reduction lemmas consume only the explicitly displayed smaller corner.
All grounds are full original residual grounds; rows keep their original indices.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory

attribute [local instance] historyRecursionPropDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]


open private
  groundOutput
  corner_supported
  linked_le_deleted
  empty_corner_rows
  join_delta
  join_comm
  insertClosedOutput
  simplexJoinOutput
  path_at_injective
  sizeTwo_row_positions
  from D5.S3.Geometry.OriginalLabelTwoSum.HistoryLocalLeaves


private def projectedRimIndexEquiv {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (C D : Finset (AllMWheel.Label i.width))
    (hC : C.image i.labels = HistoryFactors.localMask g i A) :
    (HistoryFactors.projectedRimRows g i A B).chords ≃
      (HistoryForests.localRows i.width i.atLeastThree C D).chords where
  toFun c := ⟨c.1,by
    have hd := c.2
    change Disjoint
      ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1)
      (HistoryFactors.localMask g i A) at hd
    rw [PhysicalMWheel.ambient_row] at hd
    exact (Finset.disjoint_image i.labels.injective).mp (hd.mono_right hC.le)⟩
  invFun c := ⟨c.1,by
    change Disjoint
      ((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1)
      (HistoryFactors.localMask g i A)
    rw [PhysicalMWheel.ambient_row, ← hC]
    exact (Finset.disjoint_image i.labels.injective).mpr c.2⟩
  left_inv c := Subtype.ext rfl
  right_inv c := Subtype.ext rfl

private theorem projectedRim_row_image {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (C D : Finset (AllMWheel.Label i.width))
    (hC : C.image i.labels = HistoryFactors.localMask g i A)
    (hD : D.image i.labels = HistoryFactors.localMask g i B)
    (c : (HistoryFactors.projectedRimRows g i A B).chords) :
    (HistoryFactors.projectedRimRows g i A B).row c =
      ((HistoryForests.localRows i.width i.atLeastThree C D).row
        (projectedRimIndexEquiv g i A B C D hC c)).image i.labels := by
  change (PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row c.1.1 \
    HistoryFactors.localMask g i B =
      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1 \ D).image i.labels
  rw [PhysicalMWheel.ambient_row, ← hD, Finset.image_sdiff _ _ i.labels.injective]

private theorem projectedRim_ground_image {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (C D : Finset (AllMWheel.Label i.width))
    (hC : C.image i.labels = HistoryFactors.localMask g i A)
    (hD : D.image i.labels = HistoryFactors.localMask g i B) :
    HistoryFactors.localResidual g i A B =
      (HistoryForests.localRows i.width i.atLeastThree C D).ground.image i.labels := by
  change HistoryCorners.residual ((AllMWheel.ground i.width).image i.labels)
    (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B) =
      (HistoryCorners.residual (AllMWheel.ground i.width) C D).image i.labels
  rw [← hC, ← hD, HistoryCorners.residual, HistoryCorners.residual,
    Finset.image_sdiff _ _ i.labels.injective, Finset.image_union]

/-- Every surviving local index embeds in the full physical corner with its
literal projected row. No duplicate, singleton or empty row is discarded. -/
theorem physical_rim_indexed {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V) (c : (HistoryFactors.projectedRimRows g i A B).chords) :
    ∃ d : (cornerRows (wheelStepRows g i) A B).chords,
      (cornerRows (wheelStepRows g i) A B).row d =
        (HistoryFactors.projectedRimRows g i A B).row c := by
  have hq : (HistoryFactors.localRows g i).row c.1 ⊆ HistoryFactors.wheelGround g i :=
    (HistoryFactors.localRows g i).row_supported c.1
  have hr : (HistoryFactors.localRows g i).row c.1 =
      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image i.labels :=
    PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels c.1.1
  let d : (cornerRows (wheelStepRows g i) A B).chords := ⟨.inr c.1,by
    change Disjoint
      ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image i.labels) A
    rw [← hr]
    apply Finset.disjoint_left.mpr
    intro x hx hxA
    exact Finset.disjoint_left.mp c.2 hx (Finset.mem_inter.mpr ⟨hxA,hq hx⟩)⟩
  refine ⟨d,?_⟩
  change (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) c.1.1).image
    i.labels \ B = (HistoryFactors.localRows g i).row c.1 \ HistoryFactors.localMask g i B
  rw [← hr]
  ext x
  simp only [HistoryFactors.localMask,Finset.mem_sdiff,Finset.mem_inter]
  exact ⟨fun h => ⟨h.1,fun hb => h.2 hb.1⟩,
    fun h => ⟨h.1,fun hb => h.2 ⟨hb,hq h.1⟩⟩⟩

/-- A fresh local coordinate outside the ORIGINAL interface cannot occur in
any old substituted row. Consequently EVERY current physical index containing
it comes from an actual projected rim index, with exactly the same row. -/
theorem physical_local_incidence {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V) (a : V)
    (ha : a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (c : (cornerRows (wheelStepRows g i) A B).chords)
    (hc : a ∈ (cornerRows (wheelStepRows g i) A B).row c) :
    ∃ d : (HistoryFactors.projectedRimRows g i A B).chords,
      (cornerRows (wheelStepRows g i) A B).row c =
        (HistoryFactors.projectedRimRows g i A B).row d := by
  have haY : a ∈ HistoryFactors.wheelGround g i :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ha).1).1
  have haOld : a ∉ g.ground := fun h => Finset.disjoint_left.mp i.fresh h haY
  have haR : a ∉ HistoryFactors.interface g i := (Finset.mem_sdiff.mp ha).2
  rcases c with ⟨c,hcA⟩
  cases c with
  | inl d =>
      have hsub : a ∈ substitute i.e (HistoryFactors.interface g i) (g.rows.row d) :=
        (Finset.mem_sdiff.mp hc).1
      unfold substitute at hsub
      split_ifs at hsub with he
      · rcases Finset.mem_union.mp hsub with ho | hn
        · exact (haOld (g.rows.row_supported d (Finset.mem_of_mem_erase ho))).elim
        · exact (haR hn).elim
      · exact (haOld (g.rows.row_supported d hsub)).elim
  | inr d =>
      have hq : (HistoryFactors.localRows g i).row d ⊆ HistoryFactors.wheelGround g i :=
        (HistoryFactors.localRows g i).row_supported d
      have hr : (HistoryFactors.localRows g i).row d =
          (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels :=
        PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels d.1
      let e : (HistoryFactors.projectedRimRows g i A B).chords := ⟨d,by
        rw [hr]
        exact hcA.mono_right Finset.inter_subset_left⟩
      refine ⟨e,?_⟩
      change (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image
        i.labels \ B = (HistoryFactors.localRows g i).row d \ HistoryFactors.localMask g i B
      rw [← hr]
      ext x
      simp only [HistoryFactors.localMask,Finset.mem_sdiff,Finset.mem_inter]
      exact ⟨fun h => ⟨h.1,fun hb => h.2 hb.1⟩,
        fun h => ⟨h.1,fun hb => h.2 ⟨hb,hq h.1⟩⟩⟩

/-- The usable physical leaf, with incidence transferred to ALL current indexed
rows, including substituted old rows. The masks, residual ground and both
original marker coordinates are the actual physical ones. -/
theorem physical_unmarked_leaf
    {G : Type} (g : GraphData G V) (i : PhysicalHistory.WheelInput g)
    (A B : Finset V)
    (hA : A ⊆ (PhysicalHistory.physicalWheelStep g i).data.ground)
    (hB : B ⊆ (PhysicalHistory.physicalWheelStep g i).data.ground)
    (hAB : Disjoint A B)
    (hcut : HistoryFactors.localMask g i A ≠ ∅ ∨
            HistoryFactors.localMask g i B ≠ ∅)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (hsome : Nonempty (HistoryFactors.projectedRimRows g i A B).chords) :
    let r := HistoryCorners.cornerRows (PhysicalHistory.wheelStepRows g i) A B
    ∃ a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i,
      ∃ b ∈ HistoryFactors.localResidual g i A B,
        a ≠ b ∧ ∃ d : r.chords,
          r.row d = {a,b} ∧
          ∀ c : r.chords, a ∈ r.row c → r.row c = {a,b} := by
  classical
  obtain ⟨C,hC,hCi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i A ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  obtain ⟨D,hD,hDi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i B ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  let e := projectedRimIndexEquiv g i A B C D hCi
  have hr := projectedRim_row_image g i A B C D hCi hDi
  have hg := projectedRim_ground_image g i A B C D hCi hDi
  have hcut' : C ≠ ∅ ∨ D ≠ ∅ := by
    rcases hcut with h | h
    · exact Or.inl (fun he => h (hCi.symm.trans (by simp [he])))
    · exact Or.inr (fun he => h (hDi.symm.trans (by simp [he])))
  have hrows' : ∀ c : (HistoryForests.localRows i.width i.atLeastThree C D).chords,
      ((HistoryForests.localRows i.width i.atLeastThree C D).row c).card = 2 := by
    intro c
    have hc := hrows (e.symm c)
    rw [hr] at hc
    simpa only [e,Equiv.apply_symm_apply,
      Finset.card_image_of_injective _ i.labels.injective] using hc
  have hsome' : Nonempty (HistoryForests.localRows i.width i.atLeastThree C D).chords :=
    hsome.map e
  obtain ⟨x,y,hx,hy,hxy,⟨d,hd⟩,leaf⟩ :=
    unmarked_path_leaf i.width i.atLeastThree C D hC hD hcut' hrows' hsome'
  let a := i.labels (HistoryForests.«at» i.width i.atLeastThree x)
  let b := i.labels (HistoryForests.«at» i.width i.atLeastThree y)
  have ha : a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hg.symm ▸ Finset.mem_image.mpr ⟨_,(Finset.mem_sdiff.mp hx).1,rfl⟩,?_⟩
    intro haR
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp haR
    have he' : z = HistoryForests.«at» i.width i.atLeastThree x := i.labels.injective he
    exact (Finset.mem_sdiff.mp hx).2 (he' ▸ hz)
  have hb : b ∈ HistoryFactors.localResidual g i A B :=
    hg.symm ▸ Finset.mem_image.mpr ⟨_,hy,rfl⟩
  have hab : a ≠ b := fun h => hxy
    (path_at_injective _ _ (i.labels.injective h))
  have hd' : (HistoryFactors.projectedRimRows g i A B).row (e.symm d) = {a,b} := by
    rw [hr]
    simpa only [e,Equiv.apply_symm_apply,hd,Finset.image_insert,Finset.image_singleton,a,b]
  obtain ⟨d',hd'phys⟩ := physical_rim_indexed g i A B (e.symm d)
  refine ⟨a,ha,b,hb,hab,d',hd'phys.trans hd',?_⟩
  intro c hc
  obtain ⟨q,hq⟩ := physical_local_incidence g i A B a ha c hc
  have hm : a ∈ ((HistoryForests.localRows i.width i.atLeastThree C D).row (e q)).image
      i.labels := by
    rw [← hr q,← hq]
    exact hc
  obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hm
  have he' : z = HistoryForests.«at» i.width i.atLeastThree x := i.labels.injective he
  rw [hq,hr,leaf (e q) (he' ▸ hz)]
  simp only [Finset.image_insert,Finset.image_singleton,a,b]

private theorem graph_edge_steps (m : Nat) (hm : 3 ≤ m)
    (A B : Finset (AllMWheel.Label m)) {x y : Fin m}
    (h : (HistoryForests.reducedGraph m hm A B).Adj x y) :
    x.val + 1 = y.val ∨ y.val + 1 = x.val := by
  obtain ⟨k,hk,h | h⟩ := h <;> omega

/-- Each actual size-two projected rim row has its original consecutive path
positions. This is an indexed row statement, stronger than an equality of roots. -/
theorem physical_rim_positions {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (d : (HistoryFactors.projectedRimRows g i A B).chords) :
    ∃ x y : Fin i.width,
      (HistoryFactors.projectedRimRows g i A B).row d =
        {i.labels (HistoryForests.«at» i.width i.atLeastThree x),
          i.labels (HistoryForests.«at» i.width i.atLeastThree y)} ∧
      (x.val + 1 = y.val ∨ y.val + 1 = x.val) := by
  classical
  obtain ⟨C,hC,hCi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i A ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  obtain ⟨D,hD,hDi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i B ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  let e := projectedRimIndexEquiv g i A B C D hCi
  have hr := projectedRim_row_image g i A B C D hCi hDi
  have hrows' : ∀ c : (HistoryForests.localRows i.width i.atLeastThree C D).chords,
      ((HistoryForests.localRows i.width i.atLeastThree C D).row c).card = 2 := by
    intro c
    have hc := hrows (e.symm c)
    rw [hr] at hc
    simpa only [e,Equiv.apply_symm_apply,
      Finset.card_image_of_injective _ i.labels.injective] using hc
  obtain ⟨x,y,hxy,hedge⟩ := sizeTwo_row_positions i.width i.atLeastThree C D hrows' (e d)
  refine ⟨x,y,?_,graph_edge_steps i.width i.atLeastThree C D hedge⟩
  rw [hr,hxy]
  simp only [Finset.image_insert,Finset.image_singleton]

private theorem physical_incident_positions {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (a b : V) (hab : a ≠ b)
    (hb : b ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (d : (cornerRows (wheelStepRows g i) A B).chords)
    (hd : (cornerRows (wheelStepRows g i) A B).row d = {b,a}) :
    ∃ x y : Fin i.width,
      b = i.labels (HistoryForests.«at» i.width i.atLeastThree x) ∧
      a = i.labels (HistoryForests.«at» i.width i.atLeastThree y) ∧
      (x.val + 1 = y.val ∨ y.val + 1 = x.val) := by
  have hbrow : b ∈ (cornerRows (wheelStepRows g i) A B).row d := by simp [hd]
  obtain ⟨q,hq⟩ := physical_local_incidence g i A B b hb d hbrow
  obtain ⟨x,y,he,hs⟩ := physical_rim_positions g i A B hrows q
  have hba : ({b,a} : Finset V) =
      {i.labels (HistoryForests.«at» i.width i.atLeastThree x),
        i.labels (HistoryForests.«at» i.width i.atLeastThree y)} := hd.symm.trans (hq.trans he)
  have hb' : b = i.labels (HistoryForests.«at» i.width i.atLeastThree x) ∨
      b = i.labels (HistoryForests.«at» i.width i.atLeastThree y) := by
    have hh : b ∈ ({b,a} : Finset V) := by simp
    rw [hba] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have ha' : a = i.labels (HistoryForests.«at» i.width i.atLeastThree x) ∨
      a = i.labels (HistoryForests.«at» i.width i.atLeastThree y) := by
    have hh : a ∈ ({b,a} : Finset V) := by simp
    rw [hba] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  rcases hb' with hb' | hb'
  · refine ⟨x,y,hb',ha'.resolve_left (fun he => hab (he.trans hb'.symm)),hs⟩
  · exact ⟨y,x,hb',ha'.resolve_right (fun he => hab (he.trans hb'.symm)),hs.symm⟩

private theorem physical_second_neighbour_unique {G : Type} (g : GraphData G V)
    (i : WheelInput g) (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (a b c t : V)
    (hb : b ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (hab : a ≠ b) (hbc : b ≠ c) (hbt : b ≠ t) (hac : a ≠ c) (hat : a ≠ t)
    (dab dbc dbt : (cornerRows (wheelStepRows g i) A B).chords)
    (habrow : (cornerRows (wheelStepRows g i) A B).row dab = {a,b})
    (hbcrow : (cornerRows (wheelStepRows g i) A B).row dbc = {b,c})
    (hbtrow : (cornerRows (wheelStepRows g i) A B).row dbt = {b,t}) : t = c := by
  obtain ⟨x,y,hbx,hay,hxy⟩ := physical_incident_positions g i A B hrows a b hab hb dab
    (by simpa only [Finset.pair_comm] using habrow)
  obtain ⟨x',z,hbx',hcz,hxz⟩ := physical_incident_positions g i A B hrows c b hbc.symm hb dbc hbcrow
  obtain ⟨x'',w,hbx'',htw,hxw⟩ := physical_incident_positions g i A B hrows t b hbt.symm hb dbt hbtrow
  have hxx' : x = x' := path_at_injective _ _ (i.labels.injective (hbx.symm.trans hbx'))
  have hxx'' : x = x'' := path_at_injective _ _ (i.labels.injective (hbx.symm.trans hbx''))
  subst x'
  subst x''
  have hyz : y.val ≠ z.val := fun he => hac (hay.trans
    ((congrArg (fun k => i.labels (HistoryForests.«at» i.width i.atLeastThree k))
      (Fin.ext he)).trans hcz.symm))
  have hyw : y.val ≠ w.val := fun he => hat (hay.trans
    ((congrArg (fun k => i.labels (HistoryForests.«at» i.width i.atLeastThree k))
      (Fin.ext he)).trans htw.symm))
  have hwz : w = z := Fin.ext (by omega)
  rw [hwz] at htw
  exact htw.trans hcz.symm

/-- Actual second-edge selection. When b is unmarked, either its only row is
ab, or there is a genuine bc index and EVERY row containing b is ab or bc.
The proof uses original consecutive positions, including all old-row exclusions. -/
theorem physical_neighbour_cases {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V)
    (hrows : ∀ d : (HistoryFactors.projectedRimRows g i A B).chords,
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2)
    (a b : V) (hab : a ≠ b)
    (hb : b ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (dab : (cornerRows (wheelStepRows g i) A B).chords)
    (habrow : (cornerRows (wheelStepRows g i) A B).row dab = {a,b}) :
    (∀ d : (cornerRows (wheelStepRows g i) A B).chords,
      b ∈ (cornerRows (wheelStepRows g i) A B).row d →
      (cornerRows (wheelStepRows g i) A B).row d = {a,b}) ∨
    ∃ c ∈ HistoryFactors.localResidual g i A B,
      a ≠ c ∧ b ≠ c ∧
      ∃ dbc : (cornerRows (wheelStepRows g i) A B).chords,
        (cornerRows (wheelStepRows g i) A B).row dbc = {b,c} ∧
        ∀ d : (cornerRows (wheelStepRows g i) A B).chords,
          b ∈ (cornerRows (wheelStepRows g i) A B).row d →
          (cornerRows (wheelStepRows g i) A B).row d = {a,b} ∨
            (cornerRows (wheelStepRows g i) A B).row d = {b,c} := by
  classical
  let r := cornerRows (wheelStepRows g i) A B
  have other : ∀ (d : r.chords), b ∈ r.row d →
      ∃ c ∈ HistoryFactors.localResidual g i A B, b ≠ c ∧ r.row d = {b,c} := by
    intro d hd
    obtain ⟨q,hq⟩ := physical_local_incidence g i A B b hb d hd
    obtain ⟨x,y,he,hs⟩ := physical_rim_positions g i A B hrows q
    let u := i.labels (HistoryForests.«at» i.width i.atLeastThree x)
    let v := i.labels (HistoryForests.«at» i.width i.atLeastThree y)
    have huv : u ≠ v := by
      intro h
      have hh := congrArg Fin.val (path_at_injective _ _ (i.labels.injective h))
      omega
    have hb' : b = u ∨ b = v := by
      rw [hq,he] at hd
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hd
    have hu : u ∈ HistoryFactors.localResidual g i A B :=
      (HistoryFactors.projectedRimRows g i A B).row_supported q (he.symm ▸ (by simp only [u,Finset.mem_insert,Finset.mem_singleton, true_or, eq_self]))
    have hv : v ∈ HistoryFactors.localResidual g i A B :=
      (HistoryFactors.projectedRimRows g i A B).row_supported q (he.symm ▸ (by simp only [v,Finset.mem_insert,Finset.mem_singleton, or_true, eq_self]))
    rcases hb' with rfl | rfl
    · exact ⟨v,hv,huv,hq.trans he⟩
    · exact ⟨u,hu,huv.symm,by simpa only [Finset.pair_comm] using hq.trans he⟩
  by_cases honly : ∀ d : r.chords, b ∈ r.row d → r.row d = {a,b}
  · exact Or.inl honly
  · push_neg at honly
    obtain ⟨d,hd,hne⟩ := honly
    obtain ⟨c,hc,hbc,hdc⟩ := other d hd
    have hac : a ≠ c := by
      intro he
      exact hne (by simpa only [← he,Finset.pair_comm] using hdc)
    refine Or.inr ⟨c,hc,hac,hbc,d,hdc,?_⟩
    intro q hq
    by_cases he : r.row q = {a,b}
    · exact Or.inl he
    · obtain ⟨t,ht,hbt,hqt⟩ := other q hq
      have hat : a ≠ t := by
        intro h
        exact he (by simpa only [← h,Finset.pair_comm] using hqt)
      have htc := physical_second_neighbour_unique g i A B hrows a b c t hb
        hab hbc hbt hac hat dab d q habrow hdc hqt
      exact Or.inr (htc ▸ hqt)

/-- Exhaustive cases for the actual projected indexed rows. Only the fixed
two endpoints of each original rim edge are used; the width is arbitrary. -/
theorem physical_projected_row_cases {G : Type} (g : GraphData G V) (i : WheelInput g)
    (A B : Finset V) (d : (HistoryFactors.projectedRimRows g i A B).chords) :
    (HistoryFactors.projectedRimRows g i A B).row d = ∅ ∨
      (∃ a, (HistoryFactors.projectedRimRows g i A B).row d = {a}) ∨
      ((HistoryFactors.projectedRimRows g i A B).row d).card = 2 := by
  classical
  obtain ⟨C,hC,hCi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i A ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  obtain ⟨D,hD,hDi⟩ := Finset.subset_image_iff.mp
    (show HistoryFactors.localMask g i B ⊆
      (AllMWheel.ground i.width).image i.labels from Finset.inter_subset_right)
  let e := projectedRimIndexEquiv g i A B C D hCi
  have hr := projectedRim_row_image g i A B C D hCi hDi d
  obtain ⟨k,hkA,hk,h0 | h1 | h2⟩ :=
    HistoryForests.projected_row_cases i.width i.atLeastThree C D (e d)
  · exact Or.inl (by rw [hr,h0,Finset.image_empty])
  · obtain ⟨a,ha,he⟩ := h1
    exact Or.inr (Or.inl ⟨i.labels a,by rw [hr,he,Finset.image_singleton]⟩)
  · apply Or.inr
    apply Or.inr
    have hn : HistoryForests.«at» i.width i.atLeastThree (⟨k.val,by omega⟩ : Fin i.width) ≠
        HistoryForests.«at» i.width i.atLeastThree (⟨k.val + 1,by omega⟩ : Fin i.width) := by
      intro h
      have he := congrArg Fin.val (path_at_injective _ _ h)
      change k.val = k.val + 1 at he
      omega
    rw [hr,h2,Finset.card_image_of_injective _ i.labels.injective]
    simp only [HistoryForests.cutRow,Finset.card_pair hn]

section EarlierHistory
variable {n : Nat} {G : Type} {g : GraphData G V}

/-- Exact current LOCAL-ground update for the recursive original masks.
The old X is not moved into this measure and residual ghosts are not dropped. -/
theorem localResidual_update (i : WheelInput g) (A B C D : Finset V) :
    HistoryFactors.localResidual g i (A ∪ C) (B ∪ D) =
      HistoryCorners.residual (HistoryFactors.localResidual g i A B) C D := by
  ext x
  simp only [HistoryFactors.localResidual,HistoryFactors.localMask,HistoryCorners.residual,
    Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter]
  tauto

/-- The three exact ORIGINAL recursive mask choices lower the ACTUAL local
residual cardinality by one, two and three. The masks do not delete old ghosts. -/
theorem localCorner_decreases (i : WheelInput g) (A B : Finset V) (a b c : V)
    (ha : a ∈ HistoryFactors.localResidual g i A B)
    (hb : b ∈ HistoryFactors.localResidual g i A B)
    (hc : c ∈ HistoryFactors.localResidual g i A B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (HistoryFactors.localResidual g i (A ∪ {a}) B).card + 1 =
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b})).card + 2 =
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a,b,c}) B).card + 3 =
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a}) B).card <
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b})).card <
      (HistoryFactors.localResidual g i A B).card ∧
    (HistoryFactors.localResidual g i (A ∪ {a,b,c}) B).card <
      (HistoryFactors.localResidual g i A B).card := by
  let W := HistoryFactors.localResidual g i A B
  have h1 : HistoryFactors.localResidual g i (A ∪ {a}) B = W.erase a := by
    have he := localResidual_update i A B {a} ∅
    simp only [Finset.union_empty] at he
    rw [he]
    ext x
    simp only [W,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  have h2 : HistoryFactors.localResidual g i (A ∪ {a}) (B ∪ {b}) =
      (W.erase a).erase b := by
    rw [localResidual_update]
    ext x
    simp only [W,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_erase]
    tauto
  have h3 : HistoryFactors.localResidual g i (A ∪ {a,b,c}) B =
      ((W.erase a).erase b).erase c := by
    have he := localResidual_update i A B {a,b,c} ∅
    simp only [Finset.union_empty] at he
    rw [he]
    ext x
    simp only [W,HistoryCorners.residual,Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false,Finset.mem_erase]
    tauto
  rw [h1,h2,h3]
  exact local_decreases W a b c ha hb hc hab hac hbc

/-- The factor and forest packages really describe the same PHYSICAL target.
Every structural datum is constructed; there is no Output field or premise. -/
theorem step_parent_readback (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B) :
    ∃ (C D : Finset (AllMWheel.Label i.width))
      (hC : C ⊆ AllMWheel.ground i.width) (hD : D ⊆ AllMWheel.ground i.width),
      Disjoint C D ∧ C.image i.labels = HistoryFactors.localMask g i A ∧
      D.image i.labels = HistoryFactors.localMask g i B ∧
      ∃ s : HistoryForests.ParentStructure i.width i.atLeastThree C D i.labels
        (HistoryFactors.oldResidual g i A B)
        (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B),
        corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root =
        HistoryForests.parentNormalForm i.width i.atLeastThree C D i.labels
          (HistoryFactors.oldResidual g i A B)
          (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B)
          s.rowState s.markerState := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hD : Supported (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.deleted g i A B) := by
    rw [r.deleted_readback]
    exact fun _ hs => hs.2
  have hLD : HistoryFactors.linked g i A B ≤ HistoryFactors.deleted g i A B := by
    rw [r.linked_readback,r.deleted_readback]
    exact linked_le_deleted _ _ _
  obtain ⟨C,D,hC,hD',hCD,hCi,hDi,s,hs⟩ :=
    HistoryForests.physical_parent_readback i.width i.atLeastThree i.labels
      (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)
      (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B)
      Finset.inter_subset_right Finset.inter_subset_right
      (hAB.mono Finset.inter_subset_left Finset.inter_subset_left) hD hLD
  refine ⟨C,D,hC,hD',hCD,hCi,hDi,s,?_⟩
  have hp : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      HistoryForests.physicalDecorated i.width i.atLeastThree i.labels
        (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)
        (HistoryFactors.oldResidual g i A B)
        (HistoryFactors.deleted g i A B) (HistoryFactors.linked g i A B) := by
    rw [r.factorization]
    unfold HistoryForests.physicalDecorated
    simp only [HistoryFactors.projectedRimRows]
    rw [← corner_root (HistoryFactors.localRows g i)
      (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)
      Finset.inter_subset_right]
    rfl
  exact hp.trans hs

private def priorOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (insert i.e (HistoryFactors.oldResidual g i A B))
      (HistoryFactors.prior g i A B) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  exact groundOutput r.prior_ground
    (old _ _ r.prior_masks.1 r.prior_masks.2.1 r.prior_masks.2.2)

private def deletedOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryFactors.oldResidual g i A B) (HistoryFactors.deleted g i A B) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  exact groundOutput r.factor_grounds.1
    (old _ _ r.deleted_masks.1 r.deleted_masks.2.1 r.deleted_masks.2.2)

private def linkedOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryFactors.oldResidual g i A B) (HistoryFactors.linked g i A B) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  exact groundOutput r.factor_grounds.2
    (old _ _ r.linked_masks.1 r.linked_masks.2.1 r.linked_masks.2.2)

/-- A REAL empty projected rim row makes the ENTIRE target a simplex. The
result on zero total ground is UNIT; on nonempty ground it has a cone list. -/
def stepEmptyRowOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (c : (HistoryFactors.projectedRimRows g i A B).chords)
    (hc : (HistoryFactors.projectedRimRows g i A B).row c = ∅) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have he : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      delta (HistoryCorners.residual (physicalWheelStep g i).data.ground A B) := by
    apply le_antisymm
    · exact corner_supported _ _ _ _
    · intro s hs
      rw [r.factorization, r.empty_row c hc, join_delta]
      exact Or.inl (Or.inl (r.ground ▸ hs))
  exact changeOutput (HistoryIsolated.simplexOutput _) he.symm

/-- With no remaining local label, use the exact earlier deletion or link.
An existing local index on zero ground instead gives UNIT locally and the
full simplex on X. VOID and UNIT are inspected before native projection. -/
def stepZeroLocalOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hV : HistoryFactors.localResidual g i A B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  by_cases hi : Nonempty (HistoryFactors.projectedRimRows g i A B).chords
  · let c := Classical.choice hi
    have hc : (HistoryFactors.projectedRimRows g i A B).row c = ∅ :=
      Finset.subset_empty.mp (by
        simpa only [r.row_ground, hV] using
          (HistoryFactors.projectedRimRows g i A B).row_supported c)
    exact stepEmptyRowOutput h i A B hA hB hAB c hc
  · have hE : (HistoryFactors.projectedRimRows g i A B).root = ⊥ :=
      r.no_rows ⟨fun c => hi ⟨c⟩⟩
    have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B =
        HistoryFactors.oldResidual g i A B := by
      rw [r.ground, hV, Finset.union_empty]
    have hLD : HistoryFactors.linked g i A B ≤ HistoryFactors.deleted g i A B := by
      rw [r.linked_readback, r.deleted_readback]
      exact linked_le_deleted _ _ _
    by_cases hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i)
    · have he : corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root = HistoryFactors.deleted g i A B := by
        rw [r.factorization, hE, hV, if_pos hR,
          Finset.empty_sdiff, (rawJoin_void _).2, bot_sup_eq,
          (rawJoin_unit _).2, (rawJoin_unit _).2]
        exact sup_eq_right.mpr hLD
      exact changeOutput (groundOutput hg.symm
        (deletedOutput h i A B hA hB hAB old)) he.symm
    · have he : corner (physicalWheelStep g i).data.ground A B
          (physicalWheelStep g i).data.rows.root = HistoryFactors.linked g i A B := by
        rw [r.factorization, hE, hV, if_neg hR, (rawJoin_void _).2,
          bot_sup_eq, (rawJoin_unit _).2, sup_bot_eq]
      exact changeOutput (groundOutput hg.symm
        (linkedOutput h i A B hA hB hAB old)) he.symm

/-- An actual unmarked isolated LOCAL label is a cone apex for the full
physical corner. Old substituted rows and every old ghost remain present in
factorization; the VOID case is kept literal rather than inventing a point. -/
def stepUnusedLocalOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (a : V) (ha : a ∈ HistoryFactors.localResidual g i A B \ HistoryFactors.interface g i)
    (havoid : ∀ c : (HistoryFactors.projectedRimRows g i A B).chords,
      a ∉ (HistoryFactors.projectedRimRows g i A B).row c) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  obtain ⟨haV,haR⟩ := Finset.mem_sdiff.mp ha
  refine insertClosedOutput _ _ a (corner_supported _ _ _ _) ?_
  intro s hs
  rw [r.factorization] at hs ⊢
  rcases hs with (⟨u,hu,t,ht,rfl⟩ | ⟨u,hu,t,ht,rfl⟩) | hs
  · obtain ⟨c,ht⟩ := ht
    refine Or.inl (Or.inl ⟨u,hu,insert a t,⟨c,?_⟩,?_⟩)
    · exact Finset.insert_subset (Finset.mem_sdiff.mpr
        ⟨r.row_ground.symm ▸ haV,havoid c⟩) ht
    · ext x
      simp only [Finset.mem_union,Finset.mem_insert]
      tauto
  · refine Or.inl (Or.inr ⟨u,hu,insert a t,Finset.insert_subset haV ht,?_⟩)
    ext x
    simp only [Finset.mem_union,Finset.mem_insert]
    tauto
  · by_cases hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i)
    · rw [if_pos hR] at hs ⊢
      obtain ⟨u,hu,t,ht,rfl⟩ := hs
      refine Or.inr ⟨u,hu,insert a t,Finset.insert_subset
        (Finset.mem_sdiff.mpr ⟨haV,haR⟩) ht,?_⟩
      ext x
      simp only [Finset.mem_union,Finset.mem_insert]
      tauto
    · rw [if_neg hR] at hs
      exact hs.elim

/-- With no local row and an absorbed interface, the exact target is the
simplex join of the genuine earlier LINK. Nonempty local ground gives a cone;
zero local ground retains the LINK tag, including VOID and UNIT. -/
def stepAbsorbedNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : ¬ Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hs : Supported (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.linked g i A B) := by
    rw [r.linked_readback]
    exact fun _ hx => hx.1
  have he : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      rawJoin (HistoryFactors.linked g i A B)
        (delta (HistoryFactors.localResidual g i A B)) := by
    rw [r.factorization,r.no_rows hrows,if_neg hR,
      (rawJoin_void _).2,bot_sup_eq,sup_bot_eq]
  exact changeOutput (groundOutput r.ground.symm
    (simplexJoinOutput _ _ _ hs (linkedOutput h i A B hA hB hAB old))) he.symm

/-- With no local row and no retained original endpoint marker, the exact
factor is the simplex join of the earlier DELETION. All local ghosts remain
on that simplex ground; this is not a compression to face support. -/
def stepNoMarkersNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (hmark : Disjoint (HistoryFactors.localResidual g i A B) (HistoryFactors.interface g i))
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hD : Supported (HistoryFactors.oldResidual g i A B)
      (HistoryFactors.deleted g i A B) := by
    rw [r.deleted_readback]
    exact fun _ hx => hx.2
  have hLD : HistoryFactors.linked g i A B ≤ HistoryFactors.deleted g i A B := by
    rw [r.linked_readback,r.deleted_readback]
    exact linked_le_deleted _ _ _
  have he : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      rawJoin (HistoryFactors.deleted g i A B)
        (delta (HistoryFactors.localResidual g i A B)) := by
    rw [r.factorization,r.no_rows hrows,if_pos hR,r.no_markers hmark,
      (rawJoin_void _).2,bot_sup_eq]
    apply sup_eq_right.mpr
    rintro s ⟨u,hu,t,ht,rfl⟩
    exact ⟨u,hLD hu,t,ht,rfl⟩
  exact changeOutput (groundOutput r.ground.symm
    (simplexJoinOutput _ _ _ hD (deletedOutput h i A B hA hB hAB old))) he.symm

/-- A single isolated retained original endpoint is the literal earlier J
with e renamed to that coordinate. The physical factor equality is proved here;
the native main/core lists are those of the existing marker constructor. -/
def stepSingleMarkerNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (a : V) (haR : a ∈ HistoryFactors.interface g i)
    (hV : HistoryFactors.localResidual g i A B = {a})
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have haX : a ∉ X := fun hx => Finset.disjoint_left.mp r.disjoint hx
    (hV.symm ▸ (Finset.mem_singleton_self a))
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  have hz : ({a} : Finset V) \ HistoryFactors.interface g i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : x = a := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_sdiff.mp hx).2 (he.symm ▸ haR)
  have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B = insert a X := by
    rw [r.ground,hV,Finset.union_singleton]
  have hf : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      HistoryIsolated.singleFamily (restrict X J) (rawLink X i.e J) a := by
    rw [r.factorization,r.no_rows hrows,if_pos hR,hV,hz,
      (rawJoin_void _).2,bot_sup_eq,(rawJoin_unit _).2,
      r.deleted_readback,r.linked_readback]
    unfold HistoryIsolated.singleFamily
    rw [join_comm (rawLink X i.e J) (delta {a})]
    exact sup_comm _ _
  exact changeOutput (groundOutput hg.symm
    (HistoryMarkers.singleMarkerOutput X i.e a J heX haX hJ
      (priorOutput h i A B hA hB hAB old))) hf.symm

/-- Both isolated original endpoint markers use the actual twin strip followed
by the earlier J renamed to a. The b-coordinate is retained on the outer ground;
the separate C-ALONE list is inherited unchanged from the real twin API. -/
def stepTwinMarkersNoRowsOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hrows : IsEmpty (HistoryFactors.projectedRimRows g i A B).chords)
    (hR : Disjoint (HistoryFactors.localMask g i A) (HistoryFactors.interface g i))
    (a b : V) (hab : a ≠ b) (haR : a ∈ HistoryFactors.interface g i)
    (hbR : b ∈ HistoryFactors.interface g i)
    (hV : HistoryFactors.localResidual g i A B = {a,b})
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  let X := HistoryFactors.oldResidual g i A B
  let J := HistoryFactors.prior g i A B
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have haX : a ∉ X := fun hx => Finset.disjoint_left.mp r.disjoint hx
    (hV.symm ▸ (by simp : a ∈ ({a,b} : Finset V)))
  have hbX : b ∉ X := fun hx => Finset.disjoint_left.mp r.disjoint hx
    (hV.symm ▸ (by simp : b ∈ ({a,b} : Finset V)))
  have hbI : b ∉ insert a X := by
    intro hx
    exact (Finset.mem_insert.mp hx).elim (fun he => hab he.symm) hbX
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  have hz : ({a,b} : Finset V) \ HistoryFactors.interface g i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : x = a ∨ x = b := by simpa using (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_sdiff.mp hx).2 (he.elim
      (fun he => he.symm ▸ haR) (fun he => he.symm ▸ hbR))
  have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B = insert b (insert a X) := by
    rw [r.ground,hV]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hf : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      HistoryIsolated.twinFamily (restrict X J) (rawLink X i.e J) a b := by
    rw [r.factorization,r.no_rows hrows,if_pos hR,hV,hz,
      (rawJoin_void _).2,bot_sup_eq,(rawJoin_unit _).2,
      r.deleted_readback,r.linked_readback]
    unfold HistoryIsolated.twinFamily
    rw [join_comm (rawLink X i.e J) (delta {a,b})]
    exact sup_comm _ _
  exact changeOutput (groundOutput hg.symm
    (HistoryMarkers.twinMarkerOutput X i.e a b J heX haX hbI hJ
      (priorOutput h i A B hA hB hAB old))) hf.symm

/-- Actual untouched-path physical attach branch, at EVERY width and every old
mask. The two outputs passed to intactOutput are selected only on g at rank n.
The result is on the physical attach of rank n+1, including interior ports.
The empty-X branch consumes the separate existing arbitrary-coordinate terminal. -/
def stepIntactOutput (h : MixedHistory n G g) (i : WheelInput g)
    (A B : Finset V) (hA : A ⊆ (physicalWheelStep g i).data.ground)
    (hB : B ⊆ (physicalWheelStep g i).data.ground) (hAB : Disjoint A B)
    (hLA : HistoryFactors.localMask g i A = ∅)
    (hLB : HistoryFactors.localMask g i B = ∅)
    (old : ∀ C D : Finset V, C ⊆ g.ground → D ⊆ g.ground → Disjoint C D →
      Output (HistoryCorners.residual g.ground C D) (corner g.ground C D g.rows.root)) :
    Output (HistoryCorners.residual (physicalWheelStep g i).data.ground A B)
      (corner (physicalWheelStep g i).data.ground A B
        (physicalWheelStep g i).data.rows.root) := by
  classical
  let X := HistoryFactors.oldResidual g i A B
  let Y := HistoryFactors.wheelGround g i
  let J := HistoryFactors.prior g i A B
  let r := HistoryFactors.physicalWheelStep_factorization g i A B hA hB hAB
  have hV : HistoryFactors.localResidual g i A B = Y := by
    simp only [HistoryFactors.localResidual, hLA, hLB, HistoryCorners.residual,
      Finset.union_empty, Finset.sdiff_empty, Y]
  have hE : (HistoryFactors.projectedRimRows g i A B).root =
      renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree) := by
    change (cornerRows (HistoryFactors.localRows g i)
      (HistoryFactors.localMask g i A) (HistoryFactors.localMask g i B)).root = _
    rw [hLA, hLB, empty_corner_rows]
    exact PhysicalMWheel.ambient_without i.width i.atLeastThree i.labels
  have htail : Y \ HistoryFactors.interface g i =
      (AllMWheel.tailGround i.width i.atLeastThree).image i.labels := by
    exact (Finset.image_sdiff _ _ i.labels.injective).symm
  have hg : HistoryCorners.residual (physicalWheelStep g i).data.ground A B = X ∪ Y := by
    rw [r.ground, hV]
  have heX : i.e ∉ X := fun hx =>
    Finset.notMem_erase _ _ (Finset.mem_sdiff.mp hx).1
  have hXY : Disjoint X Y :=
    i.fresh.mono (Finset.sdiff_subset.trans (Finset.erase_subset _ _)) le_rfl
  have hJ : Supported (insert i.e X) J := by
    rw [← r.prior_ground]
    exact corner_supported _ _ _ _
  have hparent : corner (physicalWheelStep g i).data.ground A B
      (physicalWheelStep g i).data.rows.root =
      parentOf X Y ((AllMWheel.tailGround i.width i.atLeastThree).image i.labels)
        i.e (renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree)) J := by
    rw [r.factorization, hE, hV, r.deleted_readback, r.linked_readback,
      if_pos (by rw [hLA]; simp), htail]
    unfold parentOf phi
    ac_rfl
  have oJ : Output (insert i.e X) J := priorOutput h i A B hA hB hAB old
  have oL : Output X (rawLink X i.e J) := changeOutput
    (linkedOutput h i A B hA hB hAB old) r.linked_readback
  have out : Output (X ∪ Y)
      (parentOf X Y ((AllMWheel.tailGround i.width i.atLeastThree).image i.labels)
        i.e (renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree)) J) := by
    by_cases hX : X.Nonempty
    · exact HistoryIntact.intactOutput i.width i.atLeastThree X i.e J i.labels
        i.zero heX hX hXY hJ oJ oL
    · have hX0 : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
      rw [hX0, Finset.empty_union]
      have hJ0 : Supported ({i.e} : Finset V) J := by
        simpa only [hX0, Finset.insert_empty] using hJ
      exact HistoryIntact.emptyOldEmbeddedIntactOutput i.width i.atLeastThree i.e
        J i.labels i.zero hJ0
  exact changeOutput (groundOutput hg.symm out) hparent.symm


end EarlierHistory

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion
