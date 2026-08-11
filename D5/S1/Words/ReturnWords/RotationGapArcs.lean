/- GID: D5/S1/Words/ReturnWords/RotationGapArcs
   generality: G
   mirror-B: none(waiver:formal-interface-precedes-first-return-consumer)
   mirror-E: none(waiver:kernel-symbolic-order-interface)
   anchors: []
   digest: Irrational rotation points admit sorted cuts and adjacent half-open gap arcs. -/

import D5.S1.Recurrence.RotationOrbitGapsPartition
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.NumberTheory.Real.Irrational

namespace D5.S1.Words

open Set
open D5.S1.Recurrence.RotationOrbitGapsPartition

/-- The negative rotation orbit, together with the right endpoint of the unit interval. -/
noncomputable def rotationCutSet (α : Real) (N : Nat) : Finset Real :=
  insert 1 (rotationOrbit (-α) N)

private theorem negative_rotation_point_injective {α : Real} (hα : Irrational α) :
    Function.Injective (fun k : Nat => Int.fract ((k : Real) * (-α))) := by
  intro k l hfract
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hfract
  by_contra hkl
  have hcoeff : (k : Int) - (l : Int) ≠ 0 := by omega
  have hi : Irrational ((((k : Int) - (l : Int) : Int) : Real) * α) :=
    hα.intCast_mul hcoeff
  apply hi.ne_int (-z)
  push_cast
  rw [← hz]
  ring

private theorem one_not_mem_negative_rotation_orbit (α : Real) (N : Nat) :
    1 ∉ rotationOrbit (-α) N := by
  intro hone
  have hunit := (rotation_orbit_gaps_partition (-α) N).1 hone
  exact (lt_irrefl (1 : Real)) hunit.2

/-- An irrational positive-length rotation has exactly `N + 1` interval cuts. -/
theorem rotation_cut_set_card (α : Real) (N : Nat) (hα : Irrational α) (_hN : 0 < N) :
    (rotationCutSet α N).card = N + 1 := by
  rw [rotationCutSet, Finset.card_insert_of_notMem
    (one_not_mem_negative_rotation_orbit α N), rotationOrbit,
    Finset.card_image_of_injective _ (negative_rotation_point_injective hα),
    Finset.card_range]

private theorem zero_mem_rotation_cut_set (α : Real) (N : Nat) (hN : 0 < N) :
    0 ∈ rotationCutSet α N := by
  rw [rotationCutSet]
  apply Finset.mem_insert_of_mem
  rw [rotationOrbit, Finset.mem_image]
  exact ⟨0, Finset.mem_range.mpr hN, by simp⟩

private theorem rotation_cut_set_subset_Icc (α : Real) (N : Nat) :
    (↑(rotationCutSet α N) : Set Real) ⊆ Icc 0 1 := by
  intro x hx
  change x ∈ rotationCutSet α N at hx
  rw [rotationCutSet, Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact ⟨by norm_num, le_rfl⟩
  · have hunit := (rotation_orbit_gaps_partition (-α) N).1 hx
    exact ⟨hunit.1, hunit.2.le⟩

/-- The increasing enumeration of the cuts of an irrational positive-length rotation. -/
noncomputable def rotationCut (α : Real) (N : Nat) [Fact (Irrational α)] [NeZero N] :
    Fin (N + 1) ↪o Real :=
  (rotationCutSet α N).orderEmbOfFin
    (rotation_cut_set_card α N Fact.out (Nat.pos_of_ne_zero NeZero.out))

/-- The first sorted cut is the left endpoint zero. -/
@[simp] theorem rotation_cut_zero (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] : rotationCut α N 0 = 0 := by
  have hS : (rotationCutSet α N).Nonempty :=
    ⟨0, zero_mem_rotation_cut_set α N (Nat.pos_of_ne_zero NeZero.out)⟩
  have hfirst : rotationCut α N 0 =
      (rotationCutSet α N).min' hS := by
    simpa [rotationCut] using
      (Finset.orderEmbOfFin_zero
        (rotation_cut_set_card α N Fact.out (Nat.pos_of_ne_zero NeZero.out))
        (Nat.succ_pos N))
  rw [hfirst]
  apply le_antisymm
  · exact Finset.min'_le (rotationCutSet α N) 0 (zero_mem_rotation_cut_set α N
      (Nat.pos_of_ne_zero NeZero.out))
  · exact (rotation_cut_set_subset_Icc α N (Finset.min'_mem _ _)).1

/-- The last sorted cut is the right endpoint one. -/
@[simp] theorem rotation_cut_last (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] : rotationCut α N (Fin.last N) = 1 := by
  have hS : (rotationCutSet α N).Nonempty := by simp [rotationCutSet]
  have hlast : rotationCut α N (Fin.last N) =
      (rotationCutSet α N).max' hS := by
    unfold rotationCut
    let j : Fin (N + 1) :=
      ⟨N + 1 - 1, Nat.sub_lt (Nat.succ_pos N) (Nat.succ_pos 0)⟩
    have hj : Fin.last N = j := by
      ext
      simp [j]
    rw [hj]
    exact Finset.orderEmbOfFin_last
      (rotation_cut_set_card α N Fact.out (Nat.pos_of_ne_zero NeZero.out))
      (Nat.succ_pos N)
  rw [hlast]
  apply le_antisymm
  · exact (rotation_cut_set_subset_Icc α N (Finset.max'_mem _ _)).2
  · exact Finset.le_max' (rotationCutSet α N) 1 (by simp [rotationCutSet])

/-- The half-open arc between two adjacent sorted cuts. -/
noncomputable def rotationGapArc (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] (r : Fin N) : Set Real :=
  Ico (rotationCut α N r.castSucc) (rotationCut α N r.succ)

/-- Every adjacent rotation arc has positive length. -/
theorem rotation_gap_arc_pos (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] (r : Fin N) :
    0 < rotationCut α N r.succ - rotationCut α N r.castSucc := by
  have hlt := (rotationCut α N).strictMono r.castSucc_lt_succ
  linarith

/-- Distinct adjacent half-open rotation arcs are disjoint. -/
theorem rotation_gap_arcs_pairwise_disjoint (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] :
    Set.PairwiseDisjoint (Set.univ : Set (Fin N)) (rotationGapArc α N) := by
  simp only [Set.PairwiseDisjoint, Set.pairwise_univ]
  intro r s hrs
  change Disjoint (rotationGapArc α N r) (rotationGapArc α N s)
  rw [Set.disjoint_left]
  intro x hxr hxs
  change rotationCut α N r.castSucc ≤ x ∧ x < rotationCut α N r.succ at hxr
  change rotationCut α N s.castSucc ≤ x ∧ x < rotationCut α N s.succ at hxs
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · have hindices : r.succ ≤ s.castSucc := by
      apply Fin.mk_le_mk.mpr
      omega
    exact (not_lt_of_ge ((rotationCut α N).monotone hindices |>.trans hxs.1)) hxr.2
  · have hindices : s.succ ≤ r.castSucc := by
      apply Fin.mk_le_mk.mpr
      omega
    exact (not_lt_of_ge ((rotationCut α N).monotone hindices |>.trans hxr.1)) hxs.2

/-- The adjacent half-open rotation arcs cover the unit interval exactly. -/
theorem iUnion_rotation_gap_arc (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] :
    (⋃ r : Fin N, rotationGapArc α N r) = Ico 0 1 := by
  ext x
  constructor
  · rintro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨r, hr⟩ := hx
    change rotationCut α N r.castSucc ≤ x ∧ x < rotationCut α N r.succ at hr
    constructor
    · calc
        0 = rotationCut α N 0 := (rotation_cut_zero α N).symm
        _ ≤ rotationCut α N r.castSucc := (rotationCut α N).monotone (by simp)
        _ ≤ x := hr.1
    · calc
        x < rotationCut α N r.succ := hr.2
        _ ≤ rotationCut α N (Fin.last N) := (rotationCut α N).monotone (Fin.le_last _)
        _ = 1 := rotation_cut_last α N
  · intro hx
    let T : Finset (Fin (N + 1)) :=
      Finset.univ.filter (fun k => rotationCut α N k ≤ x)
    have hT : T.Nonempty := by
      refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa using hx.1
    let k : Fin (N + 1) := T.max' hT
    have hkT : k ∈ T := Finset.max'_mem T hT
    have hk_le_x : rotationCut α N k ≤ x := (Finset.mem_filter.mp hkT).2
    have hk_ne_last : k ≠ Fin.last N := by
      intro hk
      have hk_le_x' : rotationCut α N (Fin.last N) ≤ x := by
        simpa [hk] using hk_le_x
      rw [rotation_cut_last] at hk_le_x'
      exact (not_le_of_gt hx.2) hk_le_x'
    have hklt : k.val < N := by
      have hkval : k.val ≠ N := by
        intro hkval
        apply hk_ne_last
        ext
        simpa using hkval
      omega
    let r : Fin N := ⟨k.val, hklt⟩
    have hrk : r.castSucc = k := by ext; rfl
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    change rotationCut α N r.castSucc ≤ x ∧ x < rotationCut α N r.succ
    refine ⟨by simpa [hrk] using hk_le_x, ?_⟩
    by_contra hnot
    have hsuccT : r.succ ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, le_of_not_gt hnot⟩
    have hle := Finset.le_max' T r.succ hsuccT
    change r.succ ≤ k at hle
    rw [← hrk] at hle
    exact (not_lt_of_ge hle) r.castSucc_lt_succ

/-- The interior cuts, excluding the fixed endpoints zero and one. -/
noncomputable def rotationInteriorCutSet (α : Real) (N : Nat) : Finset Real :=
  ((rotationCutSet α N).erase 0).erase 1

/-- The number of interior cuts at or below a point. -/
noncomputable def rotationGapRank (α : Real) (N : Nat) (x : Real) : Nat :=
  ((rotationInteriorCutSet α N).filter fun y => y ≤ x).card

private theorem rotation_cut_filter_card_eq_index_filter_card (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] (x : Real) :
    ((rotationCutSet α N).filter fun y => y ≤ x).card =
      ((Finset.univ : Finset (Fin (N + 1))).filter fun k => rotationCut α N k ≤ x).card := by
  let e := rotationCut α N
  have heq : ((rotationCutSet α N).filter fun y => y ≤ x) =
      ((Finset.univ.filter fun k : Fin (N + 1) => e k ≤ x).image e) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, hyx⟩
      have hyrange : y ∈ Set.range e := by
        change y ∈ Set.range (rotationCut α N)
        unfold rotationCut
        rw [Finset.range_orderEmbOfFin]
        exact hy
      obtain ⟨k, rfl⟩ := hyrange
      exact ⟨k, hyx, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, hk⟩
  rw [heq, Finset.card_image_of_injective _ e.injective]

private theorem rotation_gap_rank_eq_cut_card_sub_one (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] {x : Real} (hx : x ∈ Ico (0 : Real) 1) :
    rotationGapRank α N x =
      ((rotationCutSet α N).filter fun y => y ≤ x).card - 1 := by
  rw [rotationGapRank, rotationInteriorCutSet, Finset.filter_erase, Finset.filter_erase]
  have hone : 1 ∉ (rotationCutSet α N).filter (fun y => y ≤ x) := by
    simp [not_le_of_gt hx.2]
  rw [Finset.erase_eq_of_notMem (by simpa using hone)]
  apply Finset.card_erase_of_mem
  exact Finset.mem_filter.mpr
    ⟨zero_mem_rotation_cut_set α N (Nat.pos_of_ne_zero NeZero.out), hx.1⟩

/-- Filter rank is exactly membership in the correspondingly numbered adjacent arc. -/
theorem rotation_gap_rank_iff_mem_rotation_gap_arc (α : Real) (N : Nat)
    [Fact (Irrational α)] [NeZero N] {x : Real} (hx : x ∈ Ico (0 : Real) 1)
    (r : Fin N) :
    rotationGapRank α N x = r.val ↔ x ∈ rotationGapArc α N r := by
  let c := ((Finset.univ : Finset (Fin (N + 1))).filter
    fun k => rotationCut α N k ≤ x).card
  have hcpos : 0 < c := by
    apply Finset.card_pos.mpr
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa using hx.1
  have hlo : r.val < c ↔ rotationCut α N r.castSucc ≤ x := by
    simpa [c] using
      (Tuple.lt_card_le_iff_apply_le_of_monotone (j := r.castSucc) (a := x)
        (rotationCut α N).monotone)
  have hhi : r.val + 1 < c ↔ rotationCut α N r.succ ≤ x := by
    simpa [c] using
      (Tuple.lt_card_le_iff_apply_le_of_monotone (j := r.succ) (a := x)
        (rotationCut α N).monotone)
  rw [rotation_gap_rank_eq_cut_card_sub_one α N hx,
    rotation_cut_filter_card_eq_index_filter_card]
  change c - 1 = r.val ↔ _
  constructor
  · intro hcard
    change rotationCut α N r.castSucc ≤ x ∧ x < rotationCut α N r.succ
    have hc : c = r.val + 1 := by omega
    refine ⟨hlo.mp (by omega), ?_⟩
    apply lt_of_not_ge
    intro hupper
    have := hhi.mpr hupper
    omega
  · intro harc
    change rotationCut α N r.castSucc ≤ x ∧ x < rotationCut α N r.succ at harc
    have hlower := hlo.mpr harc.1
    have hupper : ¬r.val + 1 < c := by
      intro hlt
      exact (not_le_of_gt harc.2) (hhi.mp hlt)
    omega

#print axioms rotation_cut_set_card
#print axioms rotation_cut_zero
#print axioms rotation_cut_last
#print axioms rotation_gap_arc_pos
#print axioms rotation_gap_arcs_pairwise_disjoint
#print axioms iUnion_rotation_gap_arc
#print axioms rotation_gap_rank_iff_mem_rotation_gap_arc

end D5.S1.Words
