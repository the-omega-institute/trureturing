/- GID: D5/S3/Geometry/OriginalLabelTwoSum/CellLabels
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/CellLabels
   mirror-E: none(waiver:original-label-two-sum-cell-labels)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Wheel critical labels have a recoverable original-label transform, exact size increment and closed-chain formulas. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Certificates

/-! UNCOMPILED. These label consequences are consumed by WheelSupplier.
They are NOT a substitute for its main/core sequences or for a graph 2-sum
binding. In particular no arbitrary graph certificate theorem is asserted here. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
variable {V : Type*} [DecidableEq V]

/-- The original wheel transform removes the interface coordinate only when it
actually occurs, and uses the new 1-spoke only in that branch. -/
def wheelCell (e a c d : V) (s : Finset V) : Finset V :=
  if e ∈ s then s.erase e ∪ {a,c,d} else s ∪ {c,d}

/-- The new first spoke distinguishes the two branches and recovers e. -/
theorem wheelCell_recovery (W s : Finset V) (e a c d : V)
    (hs : s ⊆ W) (he : e ∈ W) (ha : a ∉ W) (hc : c ∉ W) (hd : d ∉ W)
    (hac : a ≠ c) (had : a ≠ d) :
    (wheelCell e a c d s ∩ W) ∪
      (if a ∈ wheelCell e a c d s then {e} else ∅) = s := by
  by_cases hes : e ∈ s
  · have heq : wheelCell e a c d s = s.erase e ∪ {a,c,d} := by simp [wheelCell,hes]
    have hpart : (s.erase e ∪ {a,c,d}) ∩ W = s.erase e := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hv,hw⟩
        rcases hv with hv | rfl | rfl | rfl
        · exact hv
        · exact False.elim (ha hw)
        · exact False.elim (hc hw)
        · exact False.elim (hd hw)
      · intro hv
        exact ⟨Or.inl hv,hs (Finset.mem_of_mem_erase hv)⟩
    rw [heq,hpart,if_pos (by simp)]
    simpa [Finset.union_singleton] using Finset.insert_erase hes
  · have han : a ∉ s := fun h => ha (hs h)
    have heq : wheelCell e a c d s = s ∪ {c,d} := by simp [wheelCell,hes]
    rw [heq,if_neg (by simp [han,hac,had]),Finset.union_empty]
    ext v
    simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hv,hw⟩
      rcases hv with hv | rfl | rfl
      · exact hv
      · exact False.elim (hc hw)
      · exact False.elim (hd hw)
    · exact fun hv => ⟨Or.inl hv,hs hv⟩

/-- Exact +2 in BOTH branches, including an interface critical singleton. -/
theorem wheelCell_card (W s : Finset V) (e a c d : V)
    (hs : s ⊆ W) (ha : a ∉ W) (hc : c ∉ W) (hd : d ∉ W)
    (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d) :
    (wheelCell e a c d s).card = s.card + 2 := by
  have hdisj : Disjoint s ({a,c,d} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ha (hs hv)
    · exact hc (hs hv)
    · exact hd (hs hv)
  by_cases he : e ∈ s
  · simp only [wheelCell,he,if_pos]
    rw [Finset.card_union_of_disjoint (hdisj.mono_left (Finset.erase_subset _ _)),
      Finset.card_erase_of_mem he]
    have hthree : ({a,c,d} : Finset V).card = 3 := by simp [hac,had,hcd]
    rw [hthree]
    have : 0 < s.card := Finset.card_pos.mpr ⟨e,he⟩
    omega
  · simp only [wheelCell,he,if_neg]
    rw [Finset.card_union_of_disjoint (hdisj.mono_right (by
      intro v hv; simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢; tauto))]
    simp [hcd]

/-- No critical-face count is lost to image collisions. This is a consequence
of the explicit recovery equation, not a count assumption of the compiler. -/
theorem wheelCell_count (W : Finset V) (C : Finset (Finset V)) (e a c d : V)
    (hC : ∀ s ∈ C, s ⊆ W) (he : e ∈ W)
    (ha : a ∉ W) (hc : c ∉ W) (hd : d ∉ W) (hac : a ≠ c) (had : a ≠ d) :
    (C.image (wheelCell e a c d)).card = C.card := by
  apply Finset.card_image_iff.mpr
  intro s hs t ht hst
  have hrecS := wheelCell_recovery W s e a c d (hC s hs) he ha hc hd hac had
  have hrecT := wheelCell_recovery W t e a c d (hC t ht) he ha hc hd hac had
  rw [hst] at hrecS
  exact hrecS.symm.trans hrecT

namespace ClosedChain
/-- The full supply of original labels; a finite prefix uses only finitely many.
No Fintype on this infinite pool is assumed by any native collapse. -/
abbrev Label := Fin 3 ⊕ (Nat × Fin 4)
def p : Label := .inl 0
def u : Label := .inl 1
def v : Label := .inl 2
/-- Source index j,k denotes the mathematical label r(j+1,k+1). -/
def r (j : Nat) (k : Fin 4) : Label := .inr (j,k)
def S (n : Nat) : Finset Label := (Finset.range n).biUnion (fun j => {r j 2,r j 3})
def interface (n : Nat) : Label := if n = 0 then u else r (n-1) 0
def first (n : Nat) : Finset Label := insert (interface n) (S n)
def second (n : Nat) : Finset Label := insert v (S n)
def ground (n : Nat) : Finset Label :=
  {p,v,interface n} ∪ (Finset.range n).biUnion (fun j => {r j 1,r j 2,r j 3})

private theorem mem_S (n j : Nat) (k : Fin 4) :
    r j k ∈ S n ↔ j < n ∧ (k = 2 ∨ k = 3) := by
  simp only [S,Finset.mem_biUnion,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨l,hl,h⟩
    rcases h with h | h
    · have hh : j = l ∧ k = 2 := by simpa [r] using h
      exact ⟨hh.1 ▸ hl,Or.inl hh.2⟩
    · have hh : j = l ∧ k = 3 := by simpa [r] using h
      exact ⟨hh.1 ▸ hl,Or.inr hh.2⟩
  · rintro ⟨hj,hk | hk⟩
    · subst k; exact ⟨j,hj,Or.inl rfl⟩
    · subst k; exact ⟨j,hj,Or.inr rfl⟩

private theorem S_succ (n : Nat) : S (n+1) = S n ∪ {r n 2,r n 3} := by
  simp only [S,Finset.range_add_one,Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-- The literal closed-chain label formula is consumed by the ORIGINAL
conditional critical transform, with no block-diagonal row replacement. -/
theorem critical_recurrence (n : Nat) :
    wheelCell (interface n) (r n 0) (r n 2) (r n 3) (first n) = first (n+1) ∧
    wheelCell (interface n) (r n 0) (r n 2) (r n 3) (second n) = second (n+1) := by
  have heS : interface n ∉ S n := by
    by_cases hn : n = 0
    · simp [hn,interface,S]
    · simp [interface,hn,mem_S]
  have hev : interface n ≠ v := by
    by_cases hn : n = 0 <;> simp [interface,hn,u,v,r]
  constructor
  · simp only [first,wheelCell,Finset.mem_insert_self,if_pos,
      Finset.erase_insert heS,S_succ,interface,Nat.add_sub_cancel,show n+1 ≠ 0 by omega,if_neg]
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
    tauto
  · have hn : interface n ∉ second n := by simp [second,hev,heS]
    simp only [wheelCell,hn,if_neg,second,S_succ]
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
    tauto

/-- Every finite closed prefix has exactly the stated critical sizes. This
arithmetic does not instantiate a closed-chain native history or its graph binding. -/
theorem critical_sizes (n : Nat) : (first n).card = 2*n+1 ∧ (second n).card = 2*n+1 := by
  have hS : ∀ n, (S n).card = 2*n := by
    intro n
    induction n with
    | zero => simp [S]
    | succ n ih =>
      rw [S_succ,Finset.card_union_of_disjoint (by
        apply Finset.disjoint_left.mpr
        intro x hx hnew
        simp only [Finset.mem_insert,Finset.mem_singleton] at hnew
        rcases hnew with rfl | rfl
        · exact (Nat.lt_irrefl n) ((mem_S n n 2).mp hx).1
        · exact (Nat.lt_irrefl n) ((mem_S n n 3).mp hx).1)]
      have hpair : ({r n 2,r n 3} : Finset Label).card = 2 := by simp [r]
      rw [ih,hpair]; omega
  have hi : interface n ∉ S n := by
    by_cases hn : n = 0
    · simp [hn,interface,S]
    · simp [interface,hn,mem_S]
  have hv : v ∉ S n := by simp [v,S,r]
  constructor
  · simpa only [first,Finset.card_insert_of_notMem hi,hS]
  · simpa only [second,Finset.card_insert_of_notMem hv,hS]

/-- Coupled original chord rows, retained as an ordered list before root union.
This is source preparation for the graph-bound iteration, not that theorem. -/
def rows : Nat → List (Finset Label)
  | 0 => [{p,u},{u,v},{p,v}]
  | n+1 => (rows n).map (substitute (interface n) {r n 0,r n 1}) ++
      [{r n 1,r n 2},{r n 2,r n 3},{r n 3,r n 0}]

end ClosedChain
end D5.S3.Geometry.OriginalLabelTwoSum
