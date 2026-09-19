/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lower-heavy and upper-heavy crown blocks merge through the two endpoints. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeOddBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope

/-- The selected blocks with more actual lower (even) vertices. -/
noncomputable def crownSelectedLowerBlocks {n : ℕ}
    (P : ConnectedCyclePartition (2 * n)) (selected : Finset (Quotient P.toSetoid)) :
    Finset (Quotient P.toSetoid) := by
  classical
  exact selected.filter fun C =>
    (crownBlockParityVertices P C 1).card < (crownBlockParityVertices P C 0).card

/-- The selected blocks with more actual upper (odd) vertices. -/
noncomputable def crownSelectedUpperBlocks {n : ℕ}
    (P : ConnectedCyclePartition (2 * n)) (selected : Finset (Quotient P.toSetoid)) :
    Finset (Quotient P.toSetoid) := by
  classical
  exact selected.filter fun C =>
    (crownBlockParityVertices P C 0).card < (crownBlockParityVertices P C 1).card

/- The source's two endpoint fibers are represented by one code: lower-heavy
   blocks use bottom, upper-heavy blocks use top, and every other actual block
   keeps its quotient label. -/
noncomputable def twoSidedMergeCode {n : ℕ}
    (P : ConnectedCyclePartition (2 * n))
    (lower upper : Finset (Quotient P.toSetoid)) :
    CrownAugmentedVertex n → Sum Unit (Sum (Quotient P.toSetoid) Unit) := by
  classical
  exact fun u => match u with
    | .bottom => Sum.inl ()
    | .top => Sum.inr (Sum.inr ())
    | .vertex i =>
        if (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower then Sum.inl ()
        else if (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper then Sum.inr (Sum.inr ())
        else Sum.inr (Sum.inl (Quotient.mk'' i))

private noncomputable def twoSidedMergeSetoid {n : ℕ}
    (P : ConnectedCyclePartition (2 * n))
    (lower upper : Finset (Quotient P.toSetoid)) :
    Setoid (CrownAugmentedVertex n) :=
  Setoid.ker (twoSidedMergeCode P lower upper)

/- This is the actual lower/upper split needed by Proposition 3.3: when the
   selected families are disjoint, neither endpoint fiber can accidentally
   contain the other endpoint. -/
/- Every selected original lower block is attached to the actual bottom edge,
   and every selected upper block to the actual top edge. -/
/- The two endpoint stars connect all selected blocks, while every unselected
   original block keeps its path in the actual crown cycle. -/
theorem twoSidedMerge_connected {n : ℕ} (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n))
    (lower upper : Finset (Quotient P.toSetoid))
    (hdisjoint : Disjoint lower upper) (u v : CrownAugmentedVertex n) :
    (twoSidedMergeSetoid P lower upper).r u v ↔
      (crownPartitionGraph (twoSidedMergeSetoid P lower upper)).Reachable u v := by
  have parity_succ_mod {n : ℕ} (_hn : 2 ≤ n) (a : Fin (2 * n)) :
      ((a.val + 1) % (2 * n)) % 2 = (a.val + 1) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    exact dvd_mul_right 2 n
  have pred_mod_succ_mod {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
      (hab : a = (b + 1) % N) : b = (a + N - 1) % N := by
    by_cases hwrap : b + 1 < N
    · rw [Nat.mod_eq_of_lt hwrap] at hab
      rw [hab, show b + 1 + N - 1 = b + N by omega, Nat.add_mod, Nat.mod_self,
        Nat.add_zero, Nat.mod_eq_of_lt hb]
      exact (Nat.mod_eq_of_lt hb).symm
    · have hbtop : b + 1 = N := by omega
      rw [hbtop, Nat.mod_self] at hab
      subst a
      rw [zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  have succ_mod_of_pred_mod {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
      (hba : b = (a + N - 1) % N) : a = (b + 1) % N := by
    by_cases ha0 : a = 0
    · subst a
      rw [zero_add, Nat.mod_eq_of_lt (by omega)] at hba
      rw [hba, show N - 1 + 1 = N by omega, Nat.mod_self]
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hform : a + N - 1 = (a - 1) + N := by omega
      have hpredlt : a - 1 < N := by omega
      have hsum : ((a - 1) + N) % N = a - 1 := by
        simp [Nat.mod_eq_of_lt hpredlt]
      rw [hform, hsum] at hba
      rw [hba, show a - 1 + 1 = a by omega, Nat.mod_eq_of_lt ha]
  have crownRelation_symm_iff_cycleGraph_adj {n : ℕ} (hn : 2 ≤ n)
      (i j : Fin (2 * n)) :
      crownRelation n i j ∨ crownRelation n j i ↔
        (SimpleGraph.cycleGraph (2 * n)).Adj i j := by
    letI : NeZero (2 * n) := ⟨by omega⟩
    constructor
    · intro h
      rw [SimpleGraph.cycleGraph_adj']
      rcases h with hij | hji
      · rcases hij with ⟨_, hnext | hprev⟩
        · right
          have hji : j = i + 1 := by
            apply Fin.ext
            simpa [Fin.add_def] using hnext
          simpa [hji] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
        · left
          have hij : i = j + 1 := by
            apply Fin.ext
            have hsucc := succ_mod_of_pred_mod (N := 2 * n) (a := i.val) (b := j.val)
              (by omega) i.isLt j.isLt hprev
            simpa [Fin.add_def] using hsucc
          simpa [hij] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
      · rcases hji with ⟨_, hnext | hprev⟩
        · left
          have hij : i = j + 1 := by
            apply Fin.ext
            simpa [Fin.add_def] using hnext
          simpa [hij] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
        · right
          have hji : j = i + 1 := by
            apply Fin.ext
            have hsucc := succ_mod_of_pred_mod (N := 2 * n) (a := j.val) (b := i.val)
              (by omega) j.isLt i.isLt hprev
            simpa [Fin.add_def] using hsucc
          simpa [hji] using (Nat.mod_eq_of_lt (show 1 < 2 * n by omega))
    · intro hij
      rw [SimpleGraph.cycleGraph_adj'] at hij
      rcases hij with hij | hji
      · have hsub : i - j = (1 : Fin (2 * n)) := by
          apply Fin.ext
          change (i - j).val = 1 % (2 * n)
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hij
        have hij' : i = j + 1 := (sub_eq_iff_eq_add').mp hsub
        by_cases hj : j.val % 2 = 0
        · right
          refine ⟨hj, Or.inl ?_⟩
          have hval := congrArg Fin.val hij'
          simpa [Fin.add_def] using hval
        · left
          have hjodd : j.val % 2 = 1 := by omega
          have hival := congrArg Fin.val hij'
          have hival' : i.val = (j.val + 1) % (2 * n) := by
            simpa [Fin.add_def] using hival
          have hi : i.val % 2 = 0 := by
            rw [hival']
            rw [parity_succ_mod hn]
            omega
          refine ⟨hi, Or.inr ?_⟩
          exact pred_mod_succ_mod (N := 2 * n) (a := i.val) (b := j.val)
            (by omega) i.isLt j.isLt hival'
      · have hsub : j - i = (1 : Fin (2 * n)) := by
          apply Fin.ext
          change (j - i).val = 1 % (2 * n)
          rw [Nat.mod_eq_of_lt (by omega)]
          exact hji
        have hji' : j = i + 1 := (sub_eq_iff_eq_add').mp hsub
        by_cases hi : i.val % 2 = 0
        · left
          refine ⟨hi, Or.inl ?_⟩
          have hval := congrArg Fin.val hji'
          simpa [Fin.add_def] using hval
        · right
          have hiodd : i.val % 2 = 1 := by omega
          have hjval := congrArg Fin.val hji'
          have hjval' : j.val = (i.val + 1) % (2 * n) := by
            simpa [Fin.add_def] using hjval
          have hj : j.val % 2 = 0 := by
            rw [hjval']
            rw [parity_succ_mod hn]
            omega
          refine ⟨hj, Or.inr ?_⟩
          exact pred_mod_succ_mod (N := 2 * n) (a := j.val) (b := i.val)
            (by omega) j.isLt i.isLt hjval'
  have twoSidedMerge_bottom_iff {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      (lower upper : Finset (Quotient P.toSetoid)) (i : Fin (2 * n)) :
      (twoSidedMergeSetoid P lower upper).r .bottom (.vertex i) ↔
        (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower := by
    classical
    change twoSidedMergeCode P lower upper .bottom =
      twoSidedMergeCode P lower upper (.vertex i) ↔ _
    by_cases hi : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower
    · simp [twoSidedMergeCode, hi]
    · by_cases hj : (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper
      · simp [twoSidedMergeCode, hi, hj]
      · simp [twoSidedMergeCode, hi, hj]
  have twoSidedMerge_top_iff {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      (lower upper : Finset (Quotient P.toSetoid))
      (hdisjoint : Disjoint lower upper) (i : Fin (2 * n)) :
      (twoSidedMergeSetoid P lower upper).r .top (.vertex i) ↔
        (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper := by
    classical
    change twoSidedMergeCode P lower upper .top =
      twoSidedMergeCode P lower upper (.vertex i) ↔ _
    by_cases hi : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower
    · have hnot : (Quotient.mk'' i : Quotient P.toSetoid) ∉ upper := by
        intro h
        exact (Finset.disjoint_left.1 hdisjoint) hi h
      simp [twoSidedMergeCode, hi, hnot]
    · simp [twoSidedMergeCode, hi]
  have twoSidedMerge_unselected_originals {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      (lower upper : Finset (Quotient P.toSetoid))
      (i j : Fin (2 * n))
      (hiLower : (Quotient.mk'' i : Quotient P.toSetoid) ∉ lower)
      (hiUpper : (Quotient.mk'' i : Quotient P.toSetoid) ∉ upper)
      (hjLower : (Quotient.mk'' j : Quotient P.toSetoid) ∉ lower)
      (hjUpper : (Quotient.mk'' j : Quotient P.toSetoid) ∉ upper) :
      (twoSidedMergeSetoid P lower upper).r (.vertex i) (.vertex j) ↔
        P.toSetoid.r i j := by
    classical
    change twoSidedMergeCode P lower upper (.vertex i) =
      twoSidedMergeCode P lower upper (.vertex j) ↔ _
    have hcode :
        twoSidedMergeCode P lower upper (.vertex i) =
            twoSidedMergeCode P lower upper (.vertex j) ↔
          (Quotient.mk'' i : Quotient P.toSetoid) = Quotient.mk'' j := by
      simp [twoSidedMergeCode, hiLower, hiUpper, hjLower, hjUpper]
    constructor
    · intro h
      exact @Quotient.exact _ P.toSetoid _ _ (hcode.mp h)
    · intro h
      exact hcode.mpr (Quotient.sound h)
  have twoSidedMerge_endpoint_separation {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      (lower upper : Finset (Quotient P.toSetoid)) :
      ¬ (twoSidedMergeSetoid P lower upper).r .bottom .top := by
    classical
    change twoSidedMergeCode P lower upper .bottom ≠
      twoSidedMergeCode P lower upper .top
    simp [twoSidedMergeCode]
  have twoSidedMerge_selected_adjacent {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      (lower upper : Finset (Quotient P.toSetoid))
      (hdisjoint : Disjoint lower upper)
      (i : Fin (2 * n)) :
      ((Quotient.mk'' i : Quotient P.toSetoid) ∈ lower →
        (crownPartitionGraph (twoSidedMergeSetoid P lower upper)).Adj
          .bottom (.vertex i)) ∧
      ((Quotient.mk'' i : Quotient P.toSetoid) ∈ upper →
        (crownPartitionGraph (twoSidedMergeSetoid P lower upper)).Adj
          (.vertex i) .top) := by
    classical
    constructor
    · intro hi
      rw [crownPartitionGraph, SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inl ⟨(twoSidedMerge_bottom_iff P lower upper i).mpr hi,
        by simp [crownAugmentedLE]⟩⟩
    · intro hi
      rw [crownPartitionGraph, SimpleGraph.fromRel_adj]
      exact ⟨by simp, Or.inl ⟨(twoSidedMerge_top_iff P lower upper hdisjoint i).mpr hi |>.symm,
        by simp [crownAugmentedLE]⟩⟩
  classical
  let s := twoSidedMergeSetoid P lower upper
  have hback {a b : CrownAugmentedVertex n}
      (h : (crownPartitionGraph s).Reachable a b) : s.r a b := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact s.refl _
    | @cons a b c hab _ ih =>
        rw [crownPartitionGraph, SimpleGraph.fromRel_adj] at hab
        rcases hab.2 with hab | hab
        · exact s.trans hab.1 ih
        · exact s.trans (s.symm hab.1) ih
  refine ⟨?_, hback⟩
  intro huv
  cases u with
  | bottom =>
      cases v with
      | bottom => exact SimpleGraph.Reachable.rfl
      | top => exact False.elim (twoSidedMerge_endpoint_separation P lower upper huv)
      | vertex j =>
          exact ((twoSidedMerge_selected_adjacent P lower upper hdisjoint j).1
            ((twoSidedMerge_bottom_iff P lower upper j).mp huv)).reachable
  | top =>
      cases v with
      | bottom =>
          exact False.elim (twoSidedMerge_endpoint_separation P lower upper
            ((twoSidedMergeSetoid P lower upper).symm huv))
      | top => exact SimpleGraph.Reachable.rfl
      | vertex j =>
          exact ((twoSidedMerge_selected_adjacent P lower upper hdisjoint j).2
            ((twoSidedMerge_top_iff P lower upper hdisjoint j).mp huv)).reachable.symm
  | vertex i =>
      cases v with
      | bottom =>
          exact ((twoSidedMerge_selected_adjacent P lower upper hdisjoint i).1
            ((twoSidedMerge_bottom_iff P lower upper i).mp
              ((twoSidedMergeSetoid P lower upper).symm huv))).reachable.symm
      | top =>
          exact ((twoSidedMerge_selected_adjacent P lower upper hdisjoint i).2
            ((twoSidedMerge_top_iff P lower upper hdisjoint i).mp
              ((twoSidedMergeSetoid P lower upper).symm huv))).reachable
      | vertex j =>
          by_cases hiLower : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower
          · have hjLower : (Quotient.mk'' j : Quotient P.toSetoid) ∈ lower := by
              by_contra hjLower
              change twoSidedMergeCode P lower upper (.vertex i) =
                twoSidedMergeCode P lower upper (.vertex j) at huv
              by_cases hjUpper : (Quotient.mk'' j : Quotient P.toSetoid) ∈ upper <;>
                simp [twoSidedMergeCode, hiLower, hjLower, hjUpper] at huv
            exact (((twoSidedMerge_selected_adjacent P lower upper hdisjoint i).1
              hiLower).reachable.symm.trans
                ((twoSidedMerge_selected_adjacent P lower upper hdisjoint j).1
                  hjLower).reachable)
          · by_cases hiUpper : (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper
            · have hjLower : (Quotient.mk'' j : Quotient P.toSetoid) ∉ lower := by
                intro hjLower
                change twoSidedMergeCode P lower upper (.vertex i) =
                  twoSidedMergeCode P lower upper (.vertex j) at huv
                simp [twoSidedMergeCode, hiLower, hiUpper, hjLower] at huv
              have hjUpper : (Quotient.mk'' j : Quotient P.toSetoid) ∈ upper := by
                by_contra hjUpper
                change twoSidedMergeCode P lower upper (.vertex i) =
                  twoSidedMergeCode P lower upper (.vertex j) at huv
                simp [twoSidedMergeCode, hiLower, hiUpper, hjLower, hjUpper] at huv
              exact (((twoSidedMerge_selected_adjacent P lower upper hdisjoint i).2
                hiUpper).reachable.trans
                  ((twoSidedMerge_selected_adjacent P lower upper hdisjoint j).2
                    hjUpper).reachable.symm)
            · have hjLower : (Quotient.mk'' j : Quotient P.toSetoid) ∉ lower := by
                intro hjLower
                change twoSidedMergeCode P lower upper (.vertex i) =
                  twoSidedMergeCode P lower upper (.vertex j) at huv
                simp [twoSidedMergeCode, hiLower, hiUpper, hjLower] at huv
              have hjUpper : (Quotient.mk'' j : Quotient P.toSetoid) ∉ upper := by
                intro hjUpper
                change twoSidedMergeCode P lower upper (.vertex i) =
                  twoSidedMergeCode P lower upper (.vertex j) at huv
                simp [twoSidedMergeCode, hiLower, hiUpper, hjLower, hjUpper] at huv
              have hij : P.toSetoid.r i j :=
                (twoSidedMerge_unselected_originals P lower upper i j hiLower hiUpper
                  hjLower hjUpper).mp huv
              let f : cyclePartitionGraph P.toSetoid →g crownPartitionGraph s :=
                { toFun := CrownAugmentedVertex.vertex
                  map_rel' := by
                    intro a b hab
                    rw [crownPartitionGraph, SimpleGraph.fromRel_adj]
                    have hsab : s.r (.vertex a) (.vertex b) := by
                      change twoSidedMergeCode P lower upper (.vertex a) =
                        twoSidedMergeCode P lower upper (.vertex b)
                      have hq : (Quotient.mk'' a : Quotient P.toSetoid) = Quotient.mk'' b :=
                        Quotient.sound hab.1
                      simp only [twoSidedMergeCode]
                      rw [hq]
                    have hcrown :=
                      (crownRelation_symm_iff_cycleGraph_adj hn a b).mpr hab.2
                    rcases hcrown with habc | hbac
                    · exact ⟨by exact fun h => hab.2.ne (CrownAugmentedVertex.vertex.inj h),
                        Or.inl ⟨hsab, Or.inr habc⟩⟩
                    · exact ⟨by exact fun h => hab.2.ne (CrownAugmentedVertex.vertex.inj h),
                        Or.inr ⟨s.symm hsab, Or.inr hbac⟩⟩ }
              obtain ⟨w⟩ := P.connected hij
              exact ⟨w.map f⟩
private def twoSidedMergeCodeLE {n : ℕ} (P : ConnectedCyclePartition (2 * n)) :
    Sum Unit (Sum (Quotient P.toSetoid) Unit) →
      Sum Unit (Sum (Quotient P.toSetoid) Unit) → Prop
  | .inl _, _ => True
  | .inr (.inl C), .inr (.inl D) => crownCycleBlockLE P C D
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inr (.inr _) => True
  | _, _ => False

/- Source Proposition 3.3 uses exactly these orientation facts: no original
   quotient block enters a selected lower-heavy block, and no selected
   upper-heavy block exits to another original quotient block. -/
theorem twoSidedMerge_compatible {n : ℕ} (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n))
    (selected : Finset (Quotient P.toSetoid))
    (hselected : ∀ C ∈ selected,
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1)
    (hcompatible : crownCycleCompatible P) :
    let s := twoSidedMergeSetoid P (crownSelectedLowerBlocks P selected)
      (crownSelectedUpperBlocks P selected)
    ∀ {C D : Quotient s},
      crownPartitionBlockLE s C D → crownPartitionBlockLE s D C → C = D := by
  have twoSidedMergeCodeLE_refl {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      (a : Sum Unit (Sum (Quotient P.toSetoid) Unit)) :
      twoSidedMergeCodeLE P a a := by
    cases a with
    | inl => simp [twoSidedMergeCodeLE]
    | inr a =>
        cases a with
        | inl => exact Relation.ReflTransGen.refl
        | inr => simp [twoSidedMergeCodeLE]
  have twoSidedMergeCodeLE_trans {n : ℕ}
      (P : ConnectedCyclePartition (2 * n))
      {a b c : Sum Unit (Sum (Quotient P.toSetoid) Unit)} :
      twoSidedMergeCodeLE P a b → twoSidedMergeCodeLE P b c →
        twoSidedMergeCodeLE P a c := by
    cases a with
    | inl => simp [twoSidedMergeCodeLE]
    | inr a =>
        cases a with
        | inr =>
            cases b with
            | inl => simp [twoSidedMergeCodeLE]
            | inr b => cases b <;> simp [twoSidedMergeCodeLE]
        | inl A =>
            cases b with
            | inl => simp [twoSidedMergeCodeLE]
            | inr b =>
                cases b with
                | inr =>
                    cases c with
                    | inl => simp [twoSidedMergeCodeLE]
                    | inr c => cases c <;> simp [twoSidedMergeCodeLE]
                | inl B =>
                    cases c with
                    | inl => simp [twoSidedMergeCodeLE]
                    | inr c =>
                        cases c with
                        | inr => simp [twoSidedMergeCodeLE]
                        | inl C =>
                            intro hAB hBC
                            exact hAB.trans hBC
  have twoSidedMergeCodeLE_antisymm {n : ℕ}
      (P : ConnectedCyclePartition (2 * n)) (hcompatible : crownCycleCompatible P)
      {a b : Sum Unit (Sum (Quotient P.toSetoid) Unit)} :
      twoSidedMergeCodeLE P a b → twoSidedMergeCodeLE P b a → a = b := by
    cases a with
    | inl =>
        cases b with
        | inl => simp
        | inr b => cases b <;> simp [twoSidedMergeCodeLE]
    | inr a =>
        cases a with
        | inr =>
            cases b with
            | inl => simp [twoSidedMergeCodeLE]
            | inr b => cases b <;> simp [twoSidedMergeCodeLE]
        | inl A =>
            cases b with
            | inl => simp [twoSidedMergeCodeLE]
            | inr b =>
                cases b with
                | inr => simp [twoSidedMergeCodeLE]
                | inl B =>
                    intro hAB hBA
                    exact congrArg (fun C => Sum.inr (Sum.inl C))
                      (hcompatible hAB hBA)
  classical
  dsimp only
  letI : NeZero (2 * n) := ⟨by omega⟩
  let lower := crownSelectedLowerBlocks P selected
  let upper := crownSelectedUpperBlocks P selected
  have hdisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro C hL hU
    have hL' := (Finset.mem_filter.mp hL).2
    have hU' := (Finset.mem_filter.mp hU).2
    exact (Nat.lt_asymm hL' hU')
  have hlower : ∀ L ∈ lower, ∀ C, crownCycleBlockRel P C L → C = L := by
    intro L hL
    obtain ⟨hLs, hmajor⟩ := Finset.mem_filter.mp hL
    exact (crownOddBlock_geometry hn P L (hselected L hLs)).2.1 hmajor
  have hupper : ∀ U ∈ upper, ∀ C, crownCycleBlockRel P U C → C = U := by
    intro U hU
    obtain ⟨hUs, hmajor⟩ := Finset.mem_filter.mp hU
    exact (crownOddBlock_geometry hn P U (hselected U hUs)).2.2 hmajor
  let code := twoSidedMergeCode P lower upper
  let s := twoSidedMergeSetoid P lower upper
  let qcode : Quotient s → Sum Unit (Sum (Quotient P.toSetoid) Unit) :=
    Quotient.lift code (by
      intro a b hab
      exact hab)
  have qcode_mk (u : CrownAugmentedVertex n) : qcode (Quotient.mk'' u) = code u := rfl
  have hqcode_injective : Function.Injective qcode := by
    intro C D hCD
    revert hCD
    refine Quotient.inductionOn₂ C D ?_
    intro u v huv
    apply Quotient.sound
    exact huv
  have hvertexStep (i j : Fin (2 * n)) (hij : crownRelation n i j) :
      twoSidedMergeCodeLE P (code (.vertex i)) (code (.vertex j)) := by
    by_cases hiLower : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower
    · simp [code, twoSidedMergeCode, hiLower, twoSidedMergeCodeLE]
    by_cases hjUpper : (Quotient.mk'' j : Quotient P.toSetoid) ∈ upper
    · by_cases hjLower : (Quotient.mk'' j : Quotient P.toSetoid) ∈ lower
      · exact False.elim ((Finset.disjoint_left.1 hdisjoint) hjLower hjUpper)
      · by_cases hiUpper : (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper <;>
          simp [code, twoSidedMergeCode, hiLower, hiUpper, hjLower, hjUpper,
            twoSidedMergeCodeLE]
    by_cases hjLower : (Quotient.mk'' j : Quotient P.toSetoid) ∈ lower
    · have hrel : crownCycleBlockRel P (Quotient.mk'' i) (Quotient.mk'' j) :=
        ⟨i, j, rfl, rfl, hij⟩
      have heq := hlower (Quotient.mk'' j) hjLower (Quotient.mk'' i) hrel
      have hiLower' : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower := by
        rw [heq]
        exact hjLower
      exact False.elim (hiLower hiLower')
    by_cases hiUpper : (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper
    · have hrel : crownCycleBlockRel P (Quotient.mk'' i) (Quotient.mk'' j) :=
        ⟨i, j, rfl, rfl, hij⟩
      have heq := hupper (Quotient.mk'' i) hiUpper (Quotient.mk'' j) hrel
      have hjUpper' : (Quotient.mk'' j : Quotient P.toSetoid) ∈ upper := by
        rw [heq]
        exact hiUpper
      exact False.elim (hjUpper hjUpper')
    simp only [code, twoSidedMergeCode, hiLower, hiUpper, hjLower, hjUpper,
      if_false, twoSidedMergeCodeLE]
    exact Relation.ReflTransGen.single ⟨i, j, rfl, rfl, hij⟩
  have hstep {A B : Quotient s} (hAB : crownPartitionBlockRel s A B) :
      twoSidedMergeCodeLE P (qcode A) (qcode B) := by
    obtain ⟨u, v, hu, hv, huv⟩ := hAB
    have hcode_u : qcode A = code u := by rw [← hu, qcode_mk]
    have hcode_v : qcode B = code v := by rw [← hv, qcode_mk]
    rw [hcode_u, hcode_v]
    cases u with
    | bottom => simp [code, twoSidedMergeCode, twoSidedMergeCodeLE]
    | top =>
        cases v <;> simp [crownAugmentedLE] at huv
        simp [code, twoSidedMergeCode, twoSidedMergeCodeLE]
    | vertex i =>
        cases v with
        | bottom => simp [crownAugmentedLE] at huv
        | top =>
            by_cases hiLower : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower
            · simp [code, twoSidedMergeCode, hiLower, twoSidedMergeCodeLE]
            · by_cases hiUpper : (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper <;>
                simp [code, twoSidedMergeCode, hiLower, hiUpper,
                  twoSidedMergeCodeLE]
        | vertex j =>
            rcases huv with hij | hij
            · subst j
              exact twoSidedMergeCodeLE_refl P _
            · exact hvertexStep i j hij
  have hpath {A B : Quotient s} (hAB : crownPartitionBlockLE s A B) :
      twoSidedMergeCodeLE P (qcode A) (qcode B) := by
    induction hAB with
    | refl => exact twoSidedMergeCodeLE_refl P _
    | tail hAC hCB ih => exact twoSidedMergeCodeLE_trans P ih (hstep hCB)
  intro C D hCD hDC
  apply hqcode_injective
  exact twoSidedMergeCodeLE_antisymm P hcompatible (hpath hCD) (hpath hDC)
/-- Source Proposition 3.3's forward map: split selected actual odd blocks by
    their actual parity counts and merge them with the corresponding endpoints. -/
noncomputable def twoSidedMergeCCP {n : ℕ} (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n))
    (selected : Finset (Quotient P.toSetoid))
    (hselected : ∀ C ∈ selected,
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1)
    (hcompatible : crownCycleCompatible P) : CrownConnectedCompatiblePartition n := by
  classical
  let lower := crownSelectedLowerBlocks P selected
  let upper := crownSelectedUpperBlocks P selected
  have hdisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro C hL hU
    exact Nat.lt_asymm (Finset.mem_filter.mp hL).2 (Finset.mem_filter.mp hU).2
  exact
    { toSetoid := twoSidedMergeSetoid P lower upper
      connected := twoSidedMerge_connected hn P lower upper hdisjoint
      compatible := twoSidedMerge_compatible hn P selected hselected hcompatible }

/-- The actual parity split is a disjoint cover of the selected odd blocks.
    The merged quotient has precisely the unselected quotient labels and two
    inhabited endpoint labels, hence the source's exact block count. -/
theorem twoSidedMergeCCP_card {n : ℕ} (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n))
    (selected : Finset (Quotient P.toSetoid))
    (hselected : ∀ C ∈ selected,
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1)
    (hcompatible : crownCycleCompatible P) :
    Disjoint (crownSelectedLowerBlocks P selected) (crownSelectedUpperBlocks P selected) ∧
      (∀ C, C ∈ selected ↔ C ∈ crownSelectedLowerBlocks P selected ∨
        C ∈ crownSelectedUpperBlocks P selected) ∧
      Nat.card (Quotient (twoSidedMergeCCP hn P selected hselected hcompatible).toSetoid) =
        Nat.card (Quotient P.toSetoid) - selected.card + 2 := by
  classical
  letI : NeZero (2 * n) := ⟨by omega⟩
  let lower := crownSelectedLowerBlocks P selected
  let upper := crownSelectedUpperBlocks P selected
  have hdisjoint : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro C hL hU
    exact Nat.lt_asymm (Finset.mem_filter.mp hL).2 (Finset.mem_filter.mp hU).2
  have hcover : lower ∪ upper = selected := by
    ext C
    simp only [lower, upper, crownSelectedLowerBlocks, crownSelectedUpperBlocks,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hC
      have h := (crownOddBlock_geometry hn P C (hselected C hC)).1
      rcases h with h | h
      · exact Or.inl ⟨hC, by omega⟩
      · exact Or.inr ⟨hC, by omega⟩
  refine ⟨hdisjoint, ?_, ?_⟩
  · intro C
    change C ∈ selected ↔ C ∈ lower ∨ C ∈ upper
    rw [← hcover, Finset.mem_union]
  let code := twoSidedMergeCode P lower upper
  let R := {C : Quotient P.toSetoid // C ∉ selected}
  let labels := Sum Unit (Sum R Unit)
  have hnot (C : R) : C.val ∉ lower ∧ C.val ∉ upper := by
    constructor
    · intro h
      exact C.property (Finset.mem_filter.mp h).1
    · intro h
      exact C.property (Finset.mem_filter.mp h).1
  let f : labels → Set.range code := fun a => match a with
    | .inl _ => ⟨Sum.inl (), ⟨.bottom, rfl⟩⟩
    | .inr (.inr _) => ⟨Sum.inr (Sum.inr ()), ⟨.top, rfl⟩⟩
    | .inr (.inl C) => ⟨Sum.inr (Sum.inl C.val), ⟨.vertex C.val.out, by
        simp [code, twoSidedMergeCode, (hnot C).1, (hnot C).2]⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval := congrArg Subtype.val hab
      cases a with
      | inl a =>
          cases b with
          | inl b => rfl
          | inr b => cases b <;> simp [f] at hval
      | inr a =>
          cases a with
          | inl A =>
              cases b with
              | inl b => simp [f] at hval
              | inr b =>
                  cases b with
                  | inl B =>
                      have hAB : A.val = B.val := by simpa [f] using hval
                      exact congrArg (fun C : R => Sum.inr (Sum.inl C)) (Subtype.ext hAB)
                  | inr b => simp [f] at hval
          | inr a =>
              cases b with
              | inl b => simp [f] at hval
              | inr b => cases b <;> simp_all [f]
    · rintro ⟨_, u, rfl⟩
      cases u with
      | bottom => exact ⟨Sum.inl (), rfl⟩
      | top => exact ⟨Sum.inr (Sum.inr ()), rfl⟩
      | vertex v =>
          by_cases hL : (Quotient.mk'' v : Quotient P.toSetoid) ∈ lower
          · refine ⟨Sum.inl (), ?_⟩
            apply Subtype.ext
            simp [f, code, twoSidedMergeCode, hL]
          · by_cases hU : (Quotient.mk'' v : Quotient P.toSetoid) ∈ upper
            · refine ⟨Sum.inr (Sum.inr ()), ?_⟩
              apply Subtype.ext
              simp [f, code, twoSidedMergeCode, hL, hU]
            · have hS : (Quotient.mk'' v : Quotient P.toSetoid) ∉ selected := by
                rw [← hcover, Finset.mem_union]
                exact not_or.mpr ⟨hL, hU⟩
              refine ⟨Sum.inr (Sum.inl ⟨Quotient.mk'' v, hS⟩), ?_⟩
              apply Subtype.ext
              simp [f, code, twoSidedMergeCode, hL, hU]
  let e : Quotient (Setoid.ker code) ≃ labels :=
    (Setoid.quotientKerEquivRange code).trans (Equiv.ofBijective f hf).symm
  have hcard := Fintype.card_congr e
  have hR : Fintype.card R = Fintype.card (Quotient P.toSetoid) - selected.card := by
    simp [R, Fintype.card_subtype_compl]
  change Nat.card (Quotient (Setoid.ker code)) = _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [hcard]
  simp only [labels, Fintype.card_sum, Fintype.card_unit, hR]
  omega

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
