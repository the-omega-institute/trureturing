/- GID: D5/S3/Combinatorics/PriorityLattice/TestartTreeCode
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PriorityLattice/TestartTreeCode
   mirror-E: none(waiver:structural-bijection)
   anchors: []
   utility: none
   digest: Maximum-label insertion for increasing-tree parent codes. -/

import D5.S3.Combinatorics.PriorityLattice.IntervalForestBasic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic

/-! Maximum-label cycle insertion and its native increasing-tree source. -/

namespace D5.S3.Combinatorics.PriorityLattice.TestartTreeCode

open Equiv

/-- Vertex `v` stands for label `v+1`; the value is its parent label. -/
abbrev ParentCode (n : ℕ) := (v : Fin n) → Fin (v.val + 1)

/-- The existing native unordered increasing-tree carrier, including its root. -/
abbrev NativeTree (n : ℕ) :=
  {t : IntervalForestBasic.IntervalForest n // IntervalForestBasic.IsTree t}

/-- Separate the parent of the new largest label. -/
def splitCode (n : ℕ) : ParentCode (n + 1) ≃ Fin (n + 1) × ParentCode n :=
  (Fin.snocEquiv (fun v : Fin (n + 1) => Fin (v.val + 1))).symm

/-- Insert the new maximum after its parent, or as a singleton when the parent
is zero. Inverting the standard option decomposition selects predecessors. -/
def insertEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  ((Equiv.prodCongr (finSuccEquiv n) (Equiv.inv (Perm (Fin n)))).trans
    Equiv.Perm.decomposeOption.symm).trans
      ((Equiv.permCongr (finSuccEquivLast (n := n)).symm).trans
        (Equiv.inv (Perm (Fin (n + 1)))))

theorem insert_apply (n : ℕ) (p : Fin (n + 1)) (s : Perm (Fin n))
    (v : Fin (n + 1)) :
    insertEquiv n (p,s) v = finSuccEquivLast.symm
      (s.optionCongr (Equiv.swap none (finSuccEquiv n p) (finSuccEquivLast v))) := by
  simp [insertEquiv, Equiv.permCongr_def, Equiv.Perm.decomposeOption,
    Equiv.Perm.mul_def]
  rfl

private theorem insert_zero (n : ℕ) (s : Perm (Fin n)) (v : Fin n) :
    insertEquiv n (0,s) v.castSucc = (s v).castSucc := by
  simp [insert_apply]

private theorem insert_parent (n : ℕ) (p : Fin n) (s : Perm (Fin n)) :
    insertEquiv n (p.succ,s) p.castSucc = Fin.last n := by
  simp [insert_apply]

private theorem insert_other (n : ℕ) (p v : Fin n) (s : Perm (Fin n)) (h : v ≠ p) :
    insertEquiv n (p.succ,s) v.castSucc = (s v).castSucc := by
  simp [insert_apply, Equiv.swap_apply_of_ne_of_ne, h]

/-- Recursive insertion equivalence on all parent codes. -/
def codeEquiv : (n : ℕ) → ParentCode n ≃ Perm (Fin n)
  | 0 => Equiv.ofUnique _ _
  | n+1 => ((splitCode n).trans (Equiv.prodCongr (Equiv.refl _) (codeEquiv n))).trans
      (insertEquiv n)

/-- The tree source is the existing parent-code equivalence, without a plane
order or any extra restriction on siblings. -/
noncomputable def nativeEquiv (n : ℕ) : NativeTree n ≃ Perm (Fin n) :=
  (IntervalForestBasic.treeEquivCode n).trans (codeEquiv n)

/-- A positive label has a child precisely when it occurs as a parent. -/
def HasChild {n : ℕ} (t : ParentCode n) (v : Fin n) : Prop :=
  ∃ w : Fin n, (t w).val = v.val + 1

private theorem code_succ (n : ℕ) (t : ParentCode (n + 1)) :
    codeEquiv (n + 1) t = insertEquiv n (t (Fin.last n), codeEquiv n (fun v => t v.castSucc)) := rfl

private theorem hasChild_castSucc (n : ℕ) (t : ParentCode (n + 1)) (v : Fin n) :
    HasChild t v.castSucc ↔ HasChild (fun w : Fin n => t w.castSucc) v ∨
      (t (Fin.last n)).val = v.val + 1 := by
  simp only [HasChild, Fin.val_castSucc]
  constructor
  · rintro ⟨w,hw⟩
    revert hw
    refine Fin.lastCases ?_ (fun j => ?_) w
    · exact Or.inr
    · intro hw
      exact Or.inl ⟨j,hw⟩
  · rintro (⟨w,hw⟩ | hw)
    · exact ⟨w.castSucc,hw⟩
    · exact ⟨Fin.last n,hw⟩

private theorem hasChild_last (n : ℕ) (t : ParentCode (n + 1)) :
    ¬ HasChild t (Fin.last n) := by
  rintro ⟨w,hw⟩
  have hp := (t w).isLt
  have := w.isLt
  simp only [Fin.val_last] at hw
  omega

private theorem code_excedance (n : ℕ) (t : ParentCode n) (v : Fin n) :
    v < codeEquiv n t v ↔ HasChild t v := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) v
    · simp only [hasChild_last, iff_false]
      exact not_lt_of_ge (Fin.le_last _)
    · rw [hasChild_castSucc, code_succ]
      refine Fin.cases ?_ (fun p => ?_) (t (Fin.last n))
      · rw [insert_zero]
        simpa using ih (fun v => t v.castSucc) j
      · by_cases hj : j = p
        · subst j
          rw [insert_parent]
          simp
        · rw [insert_other _ _ _ _ hj]
          have hn : ¬ p.val = j.val := by
            intro h
            exact hj (Fin.ext (by omega))
          simpa [hn] using ih (fun v => t v.castSucc) j

theorem native_parent_code {n : ℕ} (t : ParentCode n) (v : Fin n) :
    (((IntervalForestBasic.treeEquivCode n).symm t).val.parent v.succ).map Fin.val =
      some (t v).val := by
  change (if h : v.succ.val = 0 then none else
    some ⟨(t ⟨v.succ.val-1, by omega⟩).val, _⟩ : Option (Fin (n + 1))).map Fin.val = _
  simp


/-- Non-plane native incidence; no sibling order is stored. -/
def Internal {n : ℕ} (t : NativeTree n) (v : Fin (n + 1)) : Prop :=
  ∃ w, t.val.parent w = some v

private theorem native_child_code {n : ℕ} (t : ParentCode n) (v : Fin n) :
    Internal ((IntervalForestBasic.treeEquivCode n).symm t) v.succ ↔ HasChild t v := by
  constructor
  · rintro ⟨w,hw⟩
    revert hw
    refine Fin.cases ?_ (fun j => ?_) w
    · simp [IntervalForestBasic.IntervalForest.parent_zero]
    · intro hw
      have h := native_parent_code t j
      rw [hw] at h
      exact ⟨j, by simpa using h.symm⟩
  · rintro ⟨w,hw⟩
    refine ⟨w.succ, ?_⟩
    have h := native_parent_code t w
    cases hp : ((IntervalForestBasic.treeEquivCode n).symm t).val.parent w.succ with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at h
      congr 1
      apply Fin.ext
      simpa [h] using hw

private theorem native_statistic {n : ℕ} (t : NativeTree n) (v : Fin n) :
    v < nativeEquiv n t v ↔ Internal t v.succ := by
  simpa only [nativeEquiv, Equiv.trans_apply, Equiv.symm_apply_apply] using
    (code_excedance n (IntervalForestBasic.treeEquivCode n t) v).trans
      (native_child_code (IntervalForestBasic.treeEquivCode n t) v).symm

private theorem root_internal {n : ℕ} (hn : 0 < n) (t : NativeTree n) : Internal t 0 := by
  let v : Fin n := ⟨0,hn⟩
  have h := native_parent_code (IntervalForestBasic.treeEquivCode n t) v
  rw [(IntervalForestBasic.treeEquivCode n).symm_apply_apply] at h
  have hp : (IntervalForestBasic.treeEquivCode n t v).val = 0 := by
    have := (IntervalForestBasic.treeEquivCode n t v).isLt
    change (IntervalForestBasic.treeEquivCode n t v).val < 1 at this
    omega
  refine ⟨v.succ, ?_⟩
  cases hw : t.val.parent v.succ with
  | none => simp [hw] at h
  | some p =>
    simp only [hw, Option.map_some, Option.some.injEq] at h
    have : p = 0 := Fin.ext (h.trans hp)
    simp [hw,this]

/-- Reflect the first `N-1` positions, fixing the last position. -/
def reflectPositions : (n : ℕ) → Perm (Fin n)
  | 0 => Equiv.refl _
  | n+1 => Equiv.permCongr finSuccEquivLast.symm (Fin.revPerm.optionCongr)

/-- The fixed involution D in zero-based coordinates. Values represent their
positive labels by adding one. -/
def dual {n : ℕ} (s : Perm (Fin n)) : Perm (Fin n) :=
  (reflectPositions n).trans (s.trans Fin.revPerm)

private theorem reflect_last (n : ℕ) : reflectPositions (n + 1) (Fin.last n) = Fin.last n := by
  simp [reflectPositions, Equiv.permCongr_def]

private theorem reflect_castSucc (n : ℕ) (i : Fin n) :
    reflectPositions (n + 1) i.castSucc = i.rev.castSucc := by
  simp [reflectPositions, Equiv.permCongr_def, Fin.revPerm]

private theorem reflect_involutive (n : ℕ) (i : Fin n) :
    reflectPositions n (reflectPositions n i) = i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [reflect_last]
    · simp [reflect_castSucc]

private theorem dual_dual {n : ℕ} (s : Perm (Fin n)) : dual (dual s) = s := by
  ext i
  simp [dual, reflect_involutive, Equiv.trans_apply, Fin.revPerm]

/-- The exact positive-label position and value formulas of the sealed D map. -/
theorem dual_formula {n : ℕ} (s : Perm (Fin n)) (i : Fin n) :
    ((reflectPositions n i).val+1 =
      if i.val+1 < n then n-(i.val+1) else n) ∧
    (dual s i).val+1 = n+1-((s (reflectPositions n i)).val+1) := by
  constructor
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [reflect_last]
      · rw [reflect_castSucc]
        simp only [Fin.val_castSucc, Fin.val_rev]
        have := j.isLt
        rw [ite_eq_left (by omega)]
        omega
  · change (s (reflectPositions n i)).rev.val+1 = _
    simp only [Fin.val_rev]
    have := (s (reflectPositions n i)).isLt
    omega

private theorem dual_excedance (n : ℕ) (s : Perm (Fin (n + 1))) (i : Fin n) :
    i.castSucc < dual s i.castSucc ↔ s i.rev.castSucc ≤ i.rev.castSucc := by
  change i.castSucc < (s (reflectPositions _ i.castSucc)).rev ↔ _
  rw [reflect_castSucc]
  simp only [Fin.lt_def, Fin.le_def, Fin.val_rev, Fin.val_castSucc]
  have := (s i.rev.castSucc).isLt
  have := i.isLt
  omega

/-- Source-native internal labels are exactly `0,...,a-1`. -/
def TreeClass (a b : ℕ) :=
  {t : NativeTree (a + b - 1) // ∀ v, Internal t v ↔ v.val < a}

/-- Strict excedance positions are exactly `[b-1]`, with fixed points allowed. -/
def PermClass (a b : ℕ) :=
  {s : Perm (Fin (a + b - 1)) // ∀ i, i < s i ↔ i.val + 1 < b}

private theorem native_class_iff (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (t : NativeTree (a + b - 1)) :
    (∀ v, Internal t v ↔ v.val < a) ↔
      ∀ i, i < nativeEquiv (a + b - 1) t i ↔ i.val + 1 < a := by
  constructor
  · intro h i
    exact (native_statistic t i).trans (h i.succ)
  · intro h v
    refine Fin.cases ?_ (fun i => ?_) v
    · change Internal t 0 ↔ 0 < a
      exact ⟨fun _ => by omega, fun _ => root_internal (by omega : 0 < a + b - 1) t⟩
    · exact (native_statistic t i).symm.trans (h i)

private theorem dual_class_iff (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (s : Perm (Fin (a + b - 1))) :
    (∀ i, i < s i ↔ i.val + 1 < a) ↔
      ∀ i, i < dual s i ↔ i.val + 1 < b := by
  obtain ⟨n, hn⟩ : ∃ n, a + b - 1 = n+1 := ⟨a + b - 2, by omega⟩
  revert s
  rw [hn]
  intro s
  constructor
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have : ¬ (Fin.last n) < dual s (Fin.last n) := not_lt_of_ge (Fin.le_last _)
      simp only [this, Fin.val_last, false_iff]
      omega
    · rw [dual_excedance]
      have hh := h j.rev.castSucc
      simp only [Fin.val_castSucc, Fin.val_rev, Fin.lt_def, Fin.le_def] at hh ⊢
      have := j.isLt
      omega
  · intro h i
    have h' : ∀ i, i < dual (dual s) i ↔ i.val + 1 < a := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have : ¬ (Fin.last n) < dual (dual s) (Fin.last n) := not_lt_of_ge (Fin.le_last _)
        simp only [this, Fin.val_last, false_iff]
        omega
      · rw [dual_excedance]
        have hh := h j.rev.castSucc
        simp only [Fin.val_castSucc, Fin.val_rev, Fin.lt_def, Fin.le_def] at hh ⊢
        have := j.isLt
        omega
    simpa only [dual_dual] using h' i


/-- The all-size native-tree equivalence restricted by the individual internal
labels. The operational DFS and minimum-first reconstruction are separate
interfaces to this insertion implementation. -/
noncomputable def insertionClassEquiv (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    TreeClass a b ≃ PermClass a b where
  toFun t := ⟨dual (nativeEquiv (a + b - 1) t.val),
    (dual_class_iff a b ha hb _).mp ((native_class_iff a b ha hb _).mp t.property)⟩
  invFun s := ⟨(nativeEquiv (a + b - 1)).symm (dual s.val),
    (native_class_iff a b ha hb _).mpr (by
      rw [(nativeEquiv (a + b - 1)).apply_symm_apply]
      apply (dual_class_iff a b ha hb (dual s.val)).mpr
      simpa only [dual_dual] using s.property)⟩
  left_inv t := by
    apply Subtype.ext
    simp only [dual_dual, Equiv.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply, dual_dual]


end D5.S3.Combinatorics.PriorityLattice.TestartTreeCode
