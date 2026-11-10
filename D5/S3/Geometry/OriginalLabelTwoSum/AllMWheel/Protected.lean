/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Protected
   mirror-E: none(waiver:all-m-protected-source-only)
   anchors: [mathlib/module/Mathlib.Order.UpperLower.CompleteLattice]
   utility: none
   digest: Actual maximal-critical protection, path Gamma and ghost-retaining zero fillings on the original wheel grounds. -/

import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.CycleWord
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.ProtectedFillings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
attribute [local instance] allMWheelProtectedPropDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open FiniteProtectedDualWord OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]


open private D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.dual_mem D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.word_owner D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.contract_endpoint D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.interval_independent D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.root_word D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.cycle_edge_linear D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.ground_positive D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.cycle_face_proper from D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.ProtectedFillings


/- A pivot changes from the earlier residue lo+1 to the later residue lo.
   This finite set is only arithmetic notation used in the EXISTING Word. -/
private def switchBase (m lo k j : Nat) : Finset (Label m) :=
  Finset.univ.filter (fun x =>
    (lo + 1 ≤ x.val ∧ x.val < lo + 3*j ∧ x.val % 3 = (lo + 1) % 3) ∨
    (lo + 3*j + 3 ≤ x.val ∧ x.val < lo + 3*k - 2 ∧ x.val % 3 = lo % 3))

private theorem switch_pair (m lo k j : Nat) (hk : 1 ≤ k) (hj : j < k)
    (h : lo + (3*k - 2) ≤ m + 1) :
    Symbol.pair (switchBase m lo k j) (⟨lo + 3*j, by omega⟩ : Label m) ∈
      pathWord (labelInterval m lo (3*k - 2) h) := by
  induction j generalizing lo k with
  | zero =>
      by_cases h1 : k = 1
      · subst k
        have he : switchBase m lo 1 0 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hh := (Finset.mem_filter.mp hx).2
          rcases hh with ⟨hl, hu, _⟩ | ⟨hl, hu, _⟩ <;> omega
        simpa [labelInterval, he] using
          (show Symbol.pair ∅ (⟨lo, by omega⟩ : Label m) ∈
            pathWord [⟨lo, by omega⟩] by simp)
      · have hn : 3*k - 2 = (3*k - 4) + 2 := by omega
        simp only [hn]
        change _ ∈ pathWord (⟨lo, by omega⟩ :: ⟨lo+1, by omega⟩ ::
          labelInterval m (lo+2) (3*k-4) (by omega))
        rw [pathWord_cons_cons]
        apply List.mem_append.mpr
        left
        apply List.mem_map.mpr
        refine ⟨switchBase m lo k 0, (mem_orderedFaces _ _).mpr ?_, ?_⟩
        · apply (interval_independent _ _ _ _ _).mpr
          constructor
          · intro x hx
            simp only [switchBase, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            constructor <;> omega
          · intro x hx y hy hxy
            simp only [switchBase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
            omega
        · simp
  | succ j ih =>
      have hk' : 1 ≤ k-1 := by omega
      have hj' : j < k-1 := by omega
      have hn : 3*k-2 = (3*(k-1)-2)+3 := by omega
      have hb : switchBase m lo k (j+1) =
          insert (⟨lo+1, by omega⟩ : Label m) (switchBase m (lo+3) (k-1) j) := by
        ext x
        simp only [switchBase, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Fin.ext_iff]
        omega
      have hp : (⟨lo+3*(j+1), by omega⟩ : Label m) =
          (⟨(lo+3)+3*j, by omega⟩ : Label m) := by
        apply Fin.ext
        change lo + 3 * (j + 1) = (lo + 3) + 3 * j
        omega
      simp only [hn]
      change _ ∈ pathWord (⟨lo, by omega⟩ :: ⟨lo+1, by omega⟩ ::
        ⟨lo+2, by omega⟩ :: labelInterval m (lo+3) (3*(k-1)-2) (by omega))
      rw [pathWord_cons_cons]
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨Symbol.pair (switchBase m (lo+3) (k-1) j) (⟨(lo+3)+3*j, by omega⟩ : Label m),
        ih (lo+3) (k-1) hk' hj' (by omega), by simp only [List.tail_cons,
          adjoinSymbol_pair, hb, hp]⟩

/-- P07 a_j, indexed here from zero; j=0 corresponds to the ordinary j=1. -/
def collarA (m : Nat) (j : Fin (m/3)) : Finset (Label m) :=
  insert (lastLabel m) (switchBase m 2 (m/3) j.val)
def collarPivot (m : Nat) (j : Fin (m/3)) : Label m :=
  ⟨3*j.val+2, by have := j.isLt; omega⟩
def collarB (m : Nat) (j : Fin (m/3)) : Finset (Label m) :=
  insert (collarPivot m j) (collarA m j)
def collarUpper (m : Nat) (j : Fin (m/3)) : Finset (Label m) := ground m \ collarA m j
def collarLower (m : Nat) (j : Fin (m/3)) : Finset (Label m) := ground m \ collarB m j

private theorem good_width (m : Nat) (h1 : m % 3 = 1) : m = 3*(m/3)+1 := by omega
private theorem good_k (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) : 0 < m/3 := by omega

private theorem collarA_mem (m : Nat) (h1 : m % 3 = 1) (j : Fin (m/3)) (x : Label m) :
    x ∈ collarA m j ↔ x.val = m ∨
      (3 ≤ x.val ∧ x.val ≤ 3*j.val ∧ x.val % 3 = 0) ∨
      (3*j.val+5 ≤ x.val ∧ x.val < m ∧ x.val % 3 = 2) := by
  simp only [collarA, switchBase, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.ext_iff, lastLabel]
  have hmk := good_width m h1
  omega

private theorem collar_pair_in_word (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) : Symbol.pair (collarA m j) (collarPivot m j) ∈ cycleWord m hm := by
  have he : m-3 = 3*(m/3)-2 := by omega
  have hp := switch_pair m 2 (m/3) j.val (by have := good_k m hm h1; omega)
    j.isLt (by omega)
  have ht : Symbol.pair (switchBase m 2 (m/3) j.val) (collarPivot m j) ∈
      pathWord (cyclePathLast m hm) := by
    simpa only [cyclePathLast, he, collarPivot, Nat.add_comm 2 (3*j.val)] using hp
  rw [cycleWord_eq]
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨_, ht, rfl⟩

private theorem collar_pair_data (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) :
    collarA m j ∈ facets (cycleIndependentOn m hm) ∧
      collarB m j ∈ facets (cycleIndependentOn m hm) ∧ collarPivot m j ∉ collarA m j :=
  (cycleWordData m hm).pair_data _ _ (collar_pair_in_word m hm h1 j)

private theorem good_critical (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Symbol.critical (labelsCongruent m 2 2) ∈ cycleWord m hm := by
  apply (criticalFaces_mem _ _).mp
  rw [cycleWord_critical_formula, if_neg (by omega : m % 3 ≠ 0), if_pos h1]
  simp

private theorem cycle_no_adj (m : Nat) (hm : 3 ≤ m) {U : Finset (Label m)}
    (hU : U ∈ facets (cycleIndependentOn m hm)) {x y : Label m}
    (hx : x ∈ U) (hy : y ∈ U) (he : {x, y} ∈ cycleEdges m hm) : False := by
  have h := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  exact h.2 {x, y} he (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)

/- Only the two adjacent holes 3j+2,3j+3 can extend a_j. This is the
   domination calculation, not an assumption about the wanted endpoint. -/
private theorem collar_holes (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (x : Label m) (hx : x ∈ ground m)
    (ha : x ∉ collarA m j) (hp : x.val ≠ 3*j.val+2) (hq : x.val ≠ 3*j.val+3) :
    ∃ y ∈ collarA m j, {x, y} ∈ cycleEdges m hm := by
  have hxp := ground_positive m hx
  have hxm := x.isLt
  have hj := j.isLt
  have hmk := good_width m h1
  have hn := not_congr (collarA_mem m h1 j x)
  have hna := hn.mp ha
  by_cases hx1 : x.val = 1
  · refine ⟨lastLabel m, by simp [collarA], ?_⟩
    have he : x = firstLabel m hm := Fin.ext hx1
    rw [he, Finset.pair_comm]
    exact (cycleEdges_mem m hm _).mpr (Or.inr rfl)
  · by_cases hxm1 : x.val+1 = m
    · exact ⟨lastLabel m, by simp [collarA],
        cycle_edge_linear m hm x (lastLabel m) hxp (by simpa [lastLabel] using hxm1.symm)⟩
    · by_cases hleft : x.val < 3*j.val+2
      · by_cases hr1 : x.val % 3 = 1
        · let y : Label m := ⟨x.val-1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inl ?_)), ?_⟩
          · dsimp [y]; exact ⟨by omega, by omega, by omega⟩
          · rw [Finset.pair_comm]
            apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega
        · let y : Label m := ⟨x.val+1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inl ?_)),
            cycle_edge_linear m hm x y hxp rfl⟩
          dsimp [y]
          exact ⟨by omega, by omega, by omega⟩
      · by_cases hr0 : x.val % 3 = 0
        · let y : Label m := ⟨x.val-1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inr ?_)), ?_⟩
          · dsimp [y]; exact ⟨by omega, by omega, by omega⟩
          · rw [Finset.pair_comm]
            apply cycle_edge_linear m hm y x <;> dsimp [y] <;> omega
        · let y : Label m := ⟨x.val+1, by omega⟩
          refine ⟨y, (collarA_mem m h1 j y).mpr (Or.inr (Or.inr ?_)),
            cycle_edge_linear m hm x y hxp rfl⟩
          dsimp [y]
          exact ⟨by omega, by omega, by omega⟩

private theorem collar_next (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (hj : j.val+1 < m/3) :
    collarB m ⟨j.val+1, hj⟩ =
      insert (⟨3*j.val+3, by have := j.isLt; omega⟩ : Label m) (collarA m j) := by
  ext x
  simp only [collarB, Finset.mem_insert, Fin.ext_iff, collarPivot,
    collarA_mem m h1]
  have hx := x.isLt
  have hmk := good_width m h1
  omega

private theorem collar_supersets (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (U : Finset (Label m))
    (hU : U ∈ facets (cycleIndependentOn m hm)) (haU : collarA m j ⊆ U) :
    U = collarA m j ∨ U = collarB m j ∨
      ∃ hj : j.val+1 < m/3, U = collarB m ⟨j.val+1, hj⟩ := by
  let p := collarPivot m j
  let q : Label m := ⟨3*j.val+3, by have := j.isLt; omega⟩
  have hu := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  have holes : ∀ x ∈ U, x ∈ collarA m j ∨ x = p ∨ x = q := by
    intro x hx
    by_cases ha : x ∈ collarA m j
    · exact Or.inl ha
    · by_cases hp : x = p
      · exact Or.inr (Or.inl hp)
      · by_cases hq : x = q
        · exact Or.inr (Or.inr hq)
        · obtain ⟨y, hy, he⟩ := collar_holes m hm h1 j x (hu.1 hx) ha
            (by intro hv; exact hp (Fin.ext hv)) (by intro hv; exact hq (Fin.ext hv))
          exact (cycle_no_adj m hm hU hx (haU hy) he).elim
  have hadj : ¬ (p ∈ U ∧ q ∈ U) := by
    rintro ⟨hp, hq⟩
    exact cycle_no_adj m hm hU hp hq (cycle_edge_linear m hm p q
      (by dsimp [p, collarPivot]; omega) (by dsimp [p, q, collarPivot] <;> omega))
  by_cases hp : p ∈ U
  · right; left
    apply Finset.Subset.antisymm
    · intro x hx
      rcases holes x hx with ha | rfl | rfl
      · exact Finset.mem_insert_of_mem ha
      · exact Finset.mem_insert_self _ _
      · exact (hadj ⟨hp, hx⟩).elim
    · exact Finset.insert_subset hp haU
  · by_cases hq : q ∈ U
    · right; right
      have hj : j.val+1 < m/3 := by
        by_contra hn
        have hlast : (lastLabel m).val = q.val+1 := by
          dsimp [q, lastLabel]; have := j.isLt; have := good_width m h1; omega
        exact cycle_no_adj m hm hU hq (haU (by simp [collarA]))
          (cycle_edge_linear m hm q (lastLabel m) (by dsimp [q]; omega) hlast)
      refine ⟨hj, ?_⟩
      rw [collar_next m hm h1 j hj]
      apply Finset.Subset.antisymm
      · intro x hx
        rcases holes x hx with ha | rfl | rfl
        · exact Finset.mem_insert_of_mem ha
        · exact (hp hx).elim
        · exact Finset.mem_insert_self _ _
      · exact Finset.insert_subset hq haU
    · left
      apply Finset.Subset.antisymm _ haU
      intro x hx
      rcases holes x hx with ha | rfl | rfl
      · exact ha
      · exact (hp hx).elim
      · exact (hq hx).elim

private theorem critical_supersets (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (U : Finset (Label m)) (hU : U ∈ facets (cycleIndependentOn m hm))
    (hSU : labelsCongruent m 2 2 ⊆ U) :
    U = labelsCongruent m 2 2 ∨ U = collarB m ⟨0, good_k m hm h1⟩ := by
  have hu := (mem_cycleIndependentOn m hm U).mp ((mem_cycleFamily m hm U).mp hU)
  have holes : ∀ x ∈ U, x ∈ labelsCongruent m 2 2 ∨ x = lastLabel m := by
    intro x hx
    have hxp := ground_positive m (hu.1 hx)
    have hxm := x.isLt
    by_cases hl : x.val = m
    · exact Or.inr (Fin.ext hl)
    · by_cases h2 : x.val % 3 = 2
      · left
        simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, h2⟩
      · by_cases h0 : x.val % 3 = 0
        · let y : Label m := ⟨x.val-1, by omega⟩
          have hy : y ∈ labelsCongruent m 2 2 := by
            simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [y]; exact ⟨by omega, by omega⟩
          exact (cycle_no_adj m hm hU (hSU hy) hx
            (cycle_edge_linear m hm y x (by dsimp [y]; omega) (by dsimp [y]; omega))).elim
        · let y : Label m := ⟨x.val+1, by omega⟩
          have hy : y ∈ labelsCongruent m 2 2 := by
            simp only [labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [y]; exact ⟨by omega, by omega⟩
          exact (cycle_no_adj m hm hU hx (hSU hy) (cycle_edge_linear m hm x y hxp rfl)).elim
  have hb0 : collarB m ⟨0, good_k m hm h1⟩ =
      insert (lastLabel m) (labelsCongruent m 2 2) := by
    ext x
    simp only [collarB, Finset.mem_insert, collarA_mem m h1, Fin.ext_iff,
      collarPivot, labelsCongruent, Finset.mem_filter, Finset.mem_univ, true_and, lastLabel]
    have hx := x.isLt
    omega
  by_cases hl : lastLabel m ∈ U
  · right
    rw [hb0]
    exact Finset.Subset.antisymm
      (fun x hx => (holes x hx).elim (fun h => Finset.mem_insert_of_mem h)
        (fun h => Finset.mem_insert.mpr (Or.inl h))) (Finset.insert_subset hl hSU)
  · left
    exact Finset.Subset.antisymm (fun x hx => (holes x hx).resolve_right (fun h => hl (h ▸ hx))) hSU

/-- The actual P07 protection is the sole critical AND its actual whole pairs. -/
def goodH (m : Nat) : Finset (Finset (Label m)) :=
  insert (labelsCongruent m 2 2)
    ((Finset.univ : Finset (Fin (m/3))).biUnion (fun j => {collarA m j, collarB m j}))

private theorem mem_goodH (m : Nat) (T : Finset (Label m)) :
    T ∈ goodH m ↔ T = labelsCongruent m 2 2 ∨
      ∃ j : Fin (m/3), T = collarA m j ∨ T = collarB m j := by
  simp only [goodH, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]

/-- Full good-class Contract: upward, whole-symbol and all-critical coverage
    are established from the actual canonical word, not passed in. -/
def goodCycleContract (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Contract (ground m) (facets (cycleIndependentOn m hm)) where
  toWord := cycleWordData m hm
  «protected» := goodH m
  protected_subset := by
    intro T hT
    rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩
    · exact (cycleWordData m hm).critical_data _ (good_critical m hm h1)
    · exact (collar_pair_data m hm h1 j).1
    · exact (collar_pair_data m hm h1 j).2.1
  protected_upward := by
    intro T U hT hU hTU
    apply (mem_goodH m U).mpr
    rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩
    · rcases critical_supersets m hm h1 U hU hTU with he | he
      · exact Or.inl he
      · exact Or.inr ⟨⟨0, good_k m hm h1⟩, Or.inr he⟩
    all_goals
      have haU : collarA m j ⊆ U := by
        first | exact hTU | exact (Finset.subset_insert _ _).trans hTU
      rcases collar_supersets m hm h1 j U hU haU with he | he | ⟨hj, he⟩
      · exact Or.inr ⟨j, Or.inl he⟩
      · exact Or.inr ⟨j, Or.inr he⟩
      · exact Or.inr ⟨⟨j.val+1, hj⟩, Or.inr he⟩
  protected_pair := by
    intro L v hp
    have whole : ∀ T ∈ (Symbol.pair L v).faces, T ∈ goodH m →
        ∀ U ∈ (Symbol.pair L v).faces, U ∈ goodH m := by
      intro T hT hH U hU
      rcases (mem_goodH m T).mp hH with he | ⟨j, he | he⟩
      · have ho := word_owner (cycleWordData m hm).partition hp (good_critical m hm h1)
          hT (by simpa only [he, Symbol.faces, Finset.mem_singleton])
        cases ho
      all_goals
        have ht : T ∈ (Symbol.pair (collarA m j) (collarPivot m j)).faces := by
          simp [Symbol.faces, he, collarB]
        have ho := word_owner (cycleWordData m hm).partition hp
          (collar_pair_in_word m hm h1 j) hT ht
        rw [ho] at hU
        rcases (show U = collarA m j ∨ U = collarB m j by
          simpa only [Symbol.faces, Finset.mem_insert, Finset.mem_singleton, collarB] using hU)
          with he | he
        · exact (mem_goodH m U).mpr (Or.inr ⟨j, Or.inl he⟩)
        · exact (mem_goodH m U).mpr (Or.inr ⟨j, Or.inr he⟩)
    exact ⟨fun h => whole L (by simp [Symbol.faces]) h _ (by simp [Symbol.faces]),
      fun h => whole (insert v L) (by simp [Symbol.faces]) h _ (by simp [Symbol.faces])⟩
  critical_protected := by
    intro S hS
    have hc := (criticalFaces_mem _ S).mpr hS
    rw [cycleWordData_word, cycleWord_critical_formula, if_neg (by omega : m % 3 ≠ 0), if_pos h1] at hc
    exact (mem_goodH m S).mpr (Or.inl (Finset.mem_singleton.mp hc))
  emitted_proper := by
    intro L v hp _
    exact cycle_face_proper m hm _ ((cycleWordData m hm).pair_data L v hp).2.1

/-- Standalone B1, without the retained eta1 simplex. -/
def collarCore (m : Nat) (hm : 3 ≤ m) : Family (Label m) :=
  A1 m hm ⊔ facets ((Finset.univ : Finset (Fin (m/3))).image (collarUpper m))

private theorem good_dual (m : Nat) (hm : 3 ≤ m) :
    rawDual (ground m) (facets (cycleIndependentOn m hm)) = A1 m hm :=
  (cycleWord_rawDual_eq_wheelRoot m hm).trans (wheelRoot_eq_A1 m hm)

private theorem good_endpoint (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    rawEndpoint (ground m) (facets (cycleIndependentOn m hm))
      (goodCycleContract m hm h1).protected (goodCycleContract m hm h1).protected_upward =
        endpoint (collarCore m hm) {eta1 m hm} := by
  rw [contract_endpoint, good_dual]
  apply SetLike.ext
  intro s
  change (s ∈ A1 m hm ∨ ∃ t ∈ (goodH m).image (fun T => ground m \ T), s ⊆ t) ↔
    (s ∈ A1 m hm ∨ ∃ t ∈ (Finset.univ : Finset (Fin (m/3))).image (collarUpper m), s ⊆ t) ∨
      ∃ t ∈ ({eta1 m hm} : Finset (Finset (Label m))), s ⊆ t
  constructor
  · rintro (h | ⟨t, ht, hst⟩)
    · exact Or.inl (Or.inl h)
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
      rcases (mem_goodH m T).mp hT with rfl | ⟨j, rfl | rfl⟩
      · exact Or.inr ⟨eta1 m hm, by simp, hst⟩
      · exact Or.inl (Or.inr ⟨collarUpper m j, Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, rfl⟩, hst⟩)
      · exact Or.inl (Or.inr ⟨collarUpper m j, Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, rfl⟩, hst.trans
            (Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _))⟩)
  · rintro ((h | ⟨t, ht, hst⟩) | ⟨t, ht, hst⟩)
    · exact Or.inl h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      exact Or.inr ⟨collarUpper m j, Finset.mem_image.mpr
        ⟨collarA m j, (mem_goodH m _).mpr (Or.inr ⟨j, Or.inl rfl⟩), rfl⟩, hst⟩
    · have he : t = eta1 m hm := Finset.mem_singleton.mp ht
      subst t
      exact Or.inr ⟨eta1 m hm, Finset.mem_image.mpr
        ⟨labelsCongruent m 2 2, (mem_goodH m _).mpr (Or.inl rfl), rfl⟩, hst⟩

private theorem eta_good_cells (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    CriticalData (collarCore m hm) {eta1 m hm} := by
  have hS := (cycleWordData m hm).critical_data _ (good_critical m hm h1)
  have hSW := (cycleWordData m hm).supported _ hS
  have hmS : lastLabel m ∉ labelsCongruent m 2 2 := by
    simp [labelsCongruent, lastLabel, h1]
  have hmEta : lastLabel m ∈ eta1 m hm := by
    exact Finset.mem_sdiff.mpr ⟨by simp [ground, lastLabel, ne_eq, Fin.ext_iff] <;> omega, hmS⟩
  have hEtaAbsent : eta1 m hm ∉ A1 m hm := by
    rw [← good_dual m hm, dual_mem]
    rintro ⟨_, hn⟩
    exact hn (by simpa only [eta1, Finset.sdiff_sdiff_eq_self hSW] using hS)
  have hAbs : eta1 m hm ∉ collarCore m hm := by
    rintro (h | ⟨t, ht, he⟩)
    · exact hEtaAbsent h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_sdiff.mp (he hmEta)).2 (by simp [collarA])
  constructor
  · intro s hs
    have he := Finset.mem_singleton.mp hs
    subst s
    exact ⟨lastLabel m, hmEta⟩
  · intro s hs
    have he := Finset.mem_singleton.mp hs
    subst s
    exact hAbs
  · intro s hs t hts
    have he := Finset.mem_singleton.mp hs
    subst s
    by_cases ht : t ∈ A1 m hm
    · exact Or.inl ht
    · have htW : t ⊆ ground m := hts.subset.trans Finset.sdiff_subset
      have hU : ground m \ t ∈ facets (cycleIndependentOn m hm) := by
        by_contra hn
        exact ht (by rw [← good_dual m hm, dual_mem]; exact ⟨htW, hn⟩)
      have hSU : labelsCongruent m 2 2 ⊆ ground m \ t := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hSW hx, fun hxt =>
          (Finset.mem_sdiff.mp (hts.subset hxt)).2 hx⟩
      rcases critical_supersets m hm h1 _ hU hSU with hEq | hEq
      · have he' := congrArg (fun q : Finset (Label m) => ground m \ q) hEq
        have hte : t = eta1 m hm := by
          simpa only [Finset.sdiff_sdiff_eq_self htW, eta1] using he'
        exact (hts.ne hte).elim
      · have he' := congrArg (fun q : Finset (Label m) => ground m \ q) hEq
        have hte : t = collarLower m ⟨0, good_k m hm h1⟩ := by
          simpa only [Finset.sdiff_sdiff_eq_self htW, collarLower] using he'
        right
        refine ⟨collarUpper m ⟨0, good_k m hm h1⟩,
          Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [hte]
        exact Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _)
  · intro s hs t ht _
    exact (Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm

private def collarRest (m j : Nat) : Finset (Finset (Label m)) :=
  ((Finset.univ : Finset (Fin (m/3))).filter (fun i => j ≤ i.val)).biUnion
    (fun i => {collarA m i, collarB m i})

private theorem mem_collarRest (m j : Nat) (T : Finset (Label m)) :
    T ∈ collarRest m j ↔ ∃ i : Fin (m/3), j ≤ i.val ∧ (T = collarA m i ∨ T = collarB m i) := by
  simp only [collarRest, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]

private theorem collarRest_up (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) (j : Nat) :
    ∀ {T U}, T ∈ collarRest m j → U ∈ facets (cycleIndependentOn m hm) →
      T ⊆ U → U ∈ collarRest m j := by
  intro T U hT hU hTU
  obtain ⟨i, hi, he⟩ := (mem_collarRest m j T).mp hT
  have haU : collarA m i ⊆ U := by
    rcases he with rfl | rfl
    · exact hTU
    · exact (Finset.subset_insert _ _).trans hTU
  apply (mem_collarRest m j U).mpr
  rcases collar_supersets m hm h1 i U hU haU with he | he | ⟨hn, he⟩
  · exact ⟨i, hi, Or.inl he⟩
  · exact ⟨i, hi, Or.inr he⟩
  · exact ⟨⟨i.val+1, hn⟩, by change j ≤ i.val + 1; omega, Or.inr he⟩

private def collarState (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) (j : Nat) :
    Family (Label m) := rawEndpoint (ground m) (facets (cycleIndependentOn m hm))
      (collarRest m j) (collarRest_up m hm h1 j)

private theorem collarRest_subset (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (T : Finset (Label m)) (hT : T ∈ collarRest m j.val)
    (hsub : T ⊆ collarB m j) : T = collarA m j ∨ T = collarB m j := by
  obtain ⟨i, hi, he⟩ := (mem_collarRest m j.val T).mp hT
  have hai : collarA m i ⊆ T := by
    rcases he with rfl | rfl
    · exact le_rfl
    · exact Finset.subset_insert _ _
  have hij : i = j := by
    apply Fin.ext
    by_contra hn
    have hlt : j.val < i.val := by omega
    let q : Label m := ⟨3*j.val+3, by have := j.isLt; omega⟩
    have hq : q ∈ collarA m i := by
      apply (collarA_mem m h1 i q).mpr
      right; left
      dsimp [q]
      exact ⟨by omega, by omega, by omega⟩
    have hqn : q ∉ collarB m j := by
      simp only [collarB, Finset.mem_insert, collarA_mem m h1, Fin.ext_iff, collarPivot]
      dsimp [q]
      have := good_width m h1
      have := j.isLt
      omega
    exact hqn (hsub (hai hq))
  simpa only [hij] using he

private theorem collarState_cofaces (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) (s : Finset (Label m)) (hs : s ∈ collarState m hm h1 j.val)
    (hfs : collarLower m j ⊆ s) : s = collarLower m j ∨ s = collarUpper m j := by
  obtain ⟨hsW, hs⟩ := hs
  have hbW := (cycleWordData m hm).supported _ (collar_pair_data m hm h1 j).2.1
  have hcsub : ground m \ s ⊆ collarB m j := by
    intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (hfs (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp hx).1, hn⟩))
  have hcK := (facets (cycleIndependentOn m hm)).lower hcsub
    (collar_pair_data m hm h1 j).2.1
  have hcH : ground m \ s ∈ collarRest m j.val := hs.resolve_left (fun h => h hcK)
  rcases collarRest_subset m hm h1 j _ hcH hcsub with he | he
  · right
    have h := congrArg (fun q : Finset (Label m) => ground m \ q) he
    simpa only [Finset.sdiff_sdiff_eq_self hsW, collarUpper] using h
  · left
    have h := congrArg (fun q : Finset (Label m) => ground m \ q) he
    simpa only [Finset.sdiff_sdiff_eq_self hsW, collarLower] using h

private theorem collar_upper_eq (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) : insert (collarPivot m j) (collarLower m j) = collarUpper m j := by
  have hd := collar_pair_data m hm h1 j
  have hp := (cycleWordData m hm).supported _ hd.2.1 (Finset.mem_insert_self _ _)
  ext x
  by_cases hx : x = collarPivot m j
  · subst x; simp [collarLower, collarUpper, collarB, hp, hd.2.2]
  · simp [collarLower, collarUpper, collarB, hx]

private theorem collarState_upper (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) : collarUpper m j ∈ collarState m hm h1 j.val := by
  have haW := (cycleWordData m hm).supported _ (collar_pair_data m hm h1 j).1
  refine ⟨Finset.sdiff_subset, Or.inr ?_⟩
  rw [collarUpper, Finset.sdiff_sdiff_eq_self haW]
  exact (mem_collarRest m j.val _).mpr ⟨j, le_rfl, Or.inl rfl⟩

private theorem collarState_next (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Fin (m/3)) :
    cut (collarState m hm h1 j.val) {collarLower m j} = collarState m hm h1 (j.val+1) := by
  apply SetLike.ext
  intro s
  change (s ∈ collarState m hm h1 j.val ∧ ∀ a ∈ ({collarLower m j} : Finset (Finset (Label m))), ¬ a ⊆ s) ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨hsW, hc⟩, hnot⟩
    refine ⟨hsW, ?_⟩
    rcases hc with hn | hc
    · exact Or.inl hn
    · obtain ⟨i, hi, he⟩ := (mem_collarRest m j.val _).mp hc
      by_cases heq : i.val = j.val
      · have hij : i = j := Fin.ext heq
        subst i
        have hsEq : s = collarLower m j ∨ s = collarUpper m j := by
          rcases he with he | he
          · right
            have hh := congrArg (fun T : Finset (Label m) => ground m \ T) he
            simpa only [Finset.sdiff_sdiff_eq_self hsW, collarUpper] using hh
          · left
            have hh := congrArg (fun T : Finset (Label m) => ground m \ T) he
            simpa only [Finset.sdiff_sdiff_eq_self hsW, collarLower] using hh
        have hfs : collarLower m j ⊆ s := by
          rcases hsEq with rfl | rfl
          · exact le_rfl
          · exact Finset.sdiff_subset_sdiff_right _ (Finset.subset_insert _ _)
        exact (hnot hfs).elim
      · exact Or.inr ((mem_collarRest m (j.val+1) _).mpr ⟨i, by omega, he⟩)
  · rintro ⟨hsW, hc⟩
    have hprev : s ∈ collarState m hm h1 j.val := by
      refine ⟨hsW, ?_⟩
      rcases hc with hn | hc
      · exact Or.inl hn
      · obtain ⟨i, hi, he⟩ := (mem_collarRest m (j.val+1) _).mp hc
        exact Or.inr ((mem_collarRest m j.val _).mpr ⟨i, by omega, he⟩)
    refine ⟨hprev, ?_⟩
    intro hfs
    have hb := (collar_pair_data m hm h1 j).2.1
    have hcsub : ground m \ s ⊆ collarB m j := by
      intro x hx
      by_contra hn
      exact (Finset.mem_sdiff.mp hx).2 (hfs (Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hx).1, hn⟩))
    have hcK := (facets (cycleIndependentOn m hm)).lower hcsub hb
    have hcH := hc.resolve_left (fun h => h hcK)
    obtain ⟨i, hi, he⟩ := (mem_collarRest m (j.val+1) _).mp hcH
    let q : Label m := ⟨3*j.val+3, by have := j.isLt; omega⟩
    have hq : q ∈ collarA m i := by
      apply (collarA_mem m h1 i q).mpr
      right; left
      dsimp [q]; exact ⟨by omega, by omega, by omega⟩
    have hqT : q ∈ ground m \ s := by
      rcases he with he | he <;> rw [he]
      · exact hq
      · exact Finset.mem_insert_of_mem hq
    have hn : q ∉ collarB m j := by
      simp only [collarB, Finset.mem_insert, collarA_mem m h1, Fin.ext_iff, collarPivot]
      dsimp [q]; have := good_width m h1; have := j.isLt; omega
    exact hn (hcsub hqT)

private theorem collarState_final (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    collarState m hm h1 (m/3) = A1 m hm := by
  apply SetLike.ext
  intro s
  rw [← good_dual m hm, dual_mem]
  change (s ⊆ ground m ∧ (ground m \ s ∉ facets (cycleIndependentOn m hm) ∨
    ground m \ s ∈ collarRest m (m/3))) ↔ _
  have hn : ∀ T, T ∉ collarRest m (m/3) := by
    intro T h
    obtain ⟨i, hi, _⟩ := (mem_collarRest _ _ _).mp h
    have := i.isLt
    omega
  simp only [hn, or_false]

private theorem collarState_start (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    collarState m hm h1 0 = collarCore m hm := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hsW, hn | hH⟩
    · left
      change s ∈ A1 m hm
      rw [← good_dual m hm, dual_mem]
      exact ⟨hsW, hn⟩
    · obtain ⟨i, _, he⟩ := (mem_collarRest m 0 _).mp hH
      right
      refine ⟨collarUpper m i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
      have hsub : collarA m i ⊆ ground m \ s := by
        rcases he with he | he
        · rw [he]
        · rw [he]
          exact Finset.subset_insert _ _
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hsW hx, fun hxa =>
        (Finset.mem_sdiff.mp (hsub hxa)).2 hx⟩
  · rintro (hs | ⟨t, ht, hst⟩)
    · change s ∈ A1 m hm at hs
      rw [← good_dual m hm, dual_mem] at hs
      exact ⟨hs.1, Or.inl hs.2⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      have hsW : s ⊆ ground m := hst.trans Finset.sdiff_subset
      refine ⟨hsW, ?_⟩
      by_cases hc : ground m \ s ∈ facets (cycleIndependentOn m hm)
      · right
        apply collarRest_up m hm h1 0
          ((mem_collarRest m 0 _).mpr ⟨i, Nat.zero_le _, Or.inl rfl⟩) hc
        intro x hx
        have hxW := (cycleWordData m hm).supported _ (collar_pair_data m hm h1 i).1 hx
        exact Finset.mem_sdiff.mpr ⟨hxW, fun hxs => (Finset.mem_sdiff.mp (hst hxs)).2 hx⟩
      · exact Or.inl hc

private def collarFrom (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1)
    (j : Nat) (hj : j ≤ m/3) :
    Sequence (project (collarState m hm h1 j)) (project (A1 m hm)) := by
  by_cases hlt : j < m/3
  · let i : Fin (m/3) := ⟨j, hlt⟩
    have hp := cycle_face_proper m hm _ (collar_pair_data m hm h1 i).2.1
    have hne : (collarLower m i).Nonempty := by
      rw [collarLower, Finset.sdiff_nonempty]
      exact fun h => hp.ne (Finset.Subset.antisymm hp.subset h)
    have hv : collarPivot m i ∉ collarLower m i := by simp [collarLower, collarB]
    have hu : insert (collarPivot m i) (collarLower m i) ∈ collarState m hm h1 j := by
      rw [collar_upper_eq m hm h1 i]
      exact collarState_upper m hm h1 i
    have hf : ∀ s ∈ collarState m hm h1 j, collarLower m i ⊆ s →
        s = collarLower m i ∨ s = insert (collarPivot m i) (collarLower m i) := by
      intro s hs hfs
      rw [collar_upper_eq m hm h1 i]
      exact collarState_cofaces m hm h1 i s hs hfs
    let P := emitPair (collarState m hm h1 j) (collarLower m i) (collarPivot m i) hne hv hu hf
    have hret : P.retained = project (collarState m hm h1 (j+1)) := by
      rw [emitPair_retained, collarState_next m hm h1 i]
    exact Sequence.step P ((collarFrom m hm h1 (j+1) (by omega)).cast hret.symm rfl)
  · have he : j = m/3 := by omega
    subst j
    exact (Sequence.refl _).cast (congrArg project (collarState_final m hm h1)).symm rfl
termination_by m/3-j
decreasing_by omega

/-- Genuine increasing P07 collar list on B1 ALONE. Each step above constructs
    its native pair from the exact current family and its two cofaces. -/
def collarSequence (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Sequence (project (collarCore m hm)) (project (A1 m hm)) :=
  (collarFrom m hm h1 0 (Nat.zero_le _)).cast
    (congrArg project (collarState_start m hm h1)) rfl

/-- Good-class fill1 with actual main list, exact critical eta1 and the
    SEPARATE collar just constructed. -/
def fill1Good (m : Nat) (hm : 3 ≤ m) (h1 : m % 3 = 1) :
    Filling (ground m) (A1 m hm) where
  empty_mem := by
    rw [← good_dual m hm, dual_mem]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro h
    have hp := cycle_face_proper m hm _ h
    simp only [Finset.sdiff_empty] at hp
    exact hp.ne rfl
  collar := collarCore m hm
  critical := {eta1 m hm}
  contains := le_sup_left
  supported := by
    intro s hs
    rcases hs with hs | ⟨t, ht, hst⟩
    · rw [← wheelRoot_eq_A1 m hm] at hs
      exact (rimRows m (by omega)).root_supported s hs
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact hst.trans Finset.sdiff_subset
  critical_supported := by intro s hs; rw [Finset.mem_singleton.mp hs]; exact Finset.sdiff_subset
  cells := eta_good_cells m hm h1
  main := (goodCycleContract m hm h1).protectedDualWordSequence.cast rfl
    (congrArg project (good_endpoint m hm h1))
  separate := collarSequence m hm h1

/-- Both residues and the collar residue share the original Filling API;
    none of the desired outputs is an input to this all-m function. -/
def fill1 (m : Nat) (hm : 3 ≤ m) : Filling (ground m) (A1 m hm) :=
  if h1 : m % 3 = 1 then fill1Good m hm h1 else fill1Excluded m hm h1

theorem fill1_critical (m : Nat) (hm : 3 ≤ m) :
    (fill1 m hm).critical = cycleCritical m hm := by
  unfold fill1
  split_ifs with h1
  · simp only [fill1Good, cycleCritical, if_neg (by omega : m % 3 ≠ 0), if_pos h1, eta1]
  · exact fill1Excluded_critical m hm h1

private def nativeTable (K : PreAbstractSimplicialComplex V) : Finset (Finset V) :=
  by
    classical
    exact Finset.univ.filter (fun s => s ∈ K)
private def nativeEuler (K : PreAbstractSimplicialComplex V) : Int :=
  ∑ s ∈ nativeTable K, (-1 : Int)^s.card

/- Finite, ordinary, codimension-one pairs preserve this invariant. The
   argument uses the actual retained family and excludes the empty face via
   the imported CollapsePair lower_nonempty/upper_mem conditions. -/
private theorem pair_euler (P : CollapsePair V) : nativeEuler P.ambient = nativeEuler P.retained := by
  have hlu : P.lower ≠ P.upper := by
    intro he
    exact P.apex_notMem (he.symm ▸ Finset.mem_insert_self _ _)
  have hl : P.lower ∈ P.ambient := P.lower_mem
  have hlt : P.lower ∉ nativeTable P.retained := by
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      P.mem_retained_iff]
    tauto
  have hut : P.upper ∉ nativeTable P.retained := by
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      P.mem_retained_iff]
    tauto
  have ht : nativeTable P.ambient = insert P.lower (insert P.upper (nativeTable P.retained)) := by
    ext s
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, P.mem_retained_iff]
    constructor
    · intro hs
      by_cases hsl : s = P.lower
      · exact Or.inl hsl
      · by_cases hsu : s = P.upper
        · exact Or.inr (Or.inl hsu)
        · exact Or.inr (Or.inr ⟨hs, hsl, hsu⟩)
    · rintro (rfl | rfl | ⟨hs, _, _⟩)
      · exact hl
      · exact P.upper_mem
      · exact hs
  unfold nativeEuler
  rw [ht, Finset.sum_insert (by simp [hlt, hlu]), Finset.sum_insert hut]
  have hc : P.upper.card = P.lower.card+1 := by
    exact Finset.card_insert_of_notMem P.apex_notMem
  rw [hc, pow_succ]
  ring

private theorem sequence_euler {K L : PreAbstractSimplicialComplex V} (S : Sequence K L) :
    nativeEuler K = nativeEuler L := by
  induction S with
  | refl => rfl
  | step P T ih => exact (pair_euler P).trans ih

private theorem cell_euler (B : Family V) (d : Finset V)
    (hc : CriticalData B {d}) :
    nativeEuler (project (endpoint B {d})) = (-1 : Int)^d.card + nativeEuler (project B) := by
  have hn := hc.nonempty d (by simp)
  have ha := hc.absent d (by simp)
  have ht : nativeTable (project (endpoint B {d})) = insert d (nativeTable (project B)) := by
    ext s
    simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, mem_project]
    constructor
    · rintro ⟨hsn, hs | ⟨t, ht, hst⟩⟩
      · exact Or.inr ⟨hsn, hs⟩
      · have he : t = d := Finset.mem_singleton.mp ht
        subst t
        by_cases hs : s = d
        · exact Or.inl hs
        · exact Or.inr ⟨hsn, hc.boundary d (by simp) s
            (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hs⟩)⟩
    · rintro (he | ⟨hsn, hs⟩)
      · rw [he]
        exact ⟨hn, Or.inr ⟨d, by simp, le_rfl⟩⟩
      · exact ⟨hsn, Or.inl hs⟩
  unfold nativeEuler
  rw [ht, Finset.sum_insert]
  simp only [nativeTable, Finset.mem_filter, Finset.mem_univ, true_and, mem_project,
    not_and_or, ha, not_false_eq_true, or_true]

/-- Exact raw-path complementary critical family in every residue. -/
theorem pathFilling_critical (m : Nat) (hm : 3 ≤ m) :
    (pathFilling m hm).critical =
      if m % 3 = 1 then ∅ else
        {ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)} := by
  change (criticalFaces (pathRootWordData m hm).word).image (fun T => ground m \ T) = _
  rw [root_word, pathWord_critical_formula _ (pathRootPath_nodup m hm), pathRootPath_length]
  split_ifs <;> simp

/-- Necessity includes BOTH excluded residues. It uses ordinary finite Euler
    invariance and the actual one-critical partial filling; no homology or
    inferred collapse from a contractible target is used. -/
theorem gamma_iff (m : Nat) (hm : 3 ≤ m) :
    Nonempty (Sequence (project (delta (ground m))) (project (pathRoot m hm))) ↔
      goodResidue m := by
  constructor
  · rintro ⟨G⟩
    by_contra hn
    have hr : m % 3 ≠ 1 := by
      intro h1
      exact hn ⟨m/3, good_width m h1⟩
    let d := ground m \ FiniteIndependentPathGreedy.pathChosen (pathRootPath m hm)
    have hc : (pathFilling m hm).critical = {d} := by
      rw [pathFilling_critical, if_neg hr]
    have hmain := sequence_euler (pathFilling m hm).main
    have hgamma := sequence_euler G
    have hcells : CriticalData (pathRoot m hm) {d} := by
      rw [← hc]
      exact (pathFilling m hm).cells
    have hcell := cell_euler (pathRoot m hm) d hcells
    change nativeEuler (project (delta (ground m))) =
      nativeEuler (project (endpoint (pathRoot m hm) (pathFilling m hm).critical)) at hmain
    rw [hc] at hmain
    have hzero : (-1 : Int)^d.card = 0 := by omega
    exact (pow_ne_zero d.card (by decide : (-1 : Int) ≠ 0)) hzero
  · intro hg
    exact ⟨gammaGood m hm hg⟩

end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
