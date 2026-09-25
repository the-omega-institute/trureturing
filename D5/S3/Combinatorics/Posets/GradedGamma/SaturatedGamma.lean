/- GID: D5/S3/Combinatorics/Posets/GradedGamma/SaturatedGamma
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/GradedGamma/SaturatedGamma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Alternating parity runs have an exact strict-join count. -/

import D5.S3.Combinatorics.Posets.GradedGamma.SaturatedDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.GradedGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

variable {α : Type*} [Fintype α] [PartialOrder α] [GradeOrder ℕ α]

/-- Number of changes from an odd run to an even run before a position. -/
def strictBoundaryCount (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α)) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin (Fintype.card α - 1) =>
    k.val < i.val ∧ parityBoundary e k ∧
      runIndex e ⟨k.val, by omega⟩ % 2 = 1).card

/-- Alternating parity changes contribute one strict boundary at every
second transition, starting with the second transition. -/
theorem strictBoundaryCount_eq_half (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α)) :
    strictBoundaryCount e i = runIndex e i / 2 := by
  classical
  have hstep (t : Fin (Fintype.card α - 1)) :
      strictBoundaryCount e ⟨t.val + 1, by omega⟩ =
        strictBoundaryCount e ⟨t.val, by omega⟩ +
          if parityBoundary e t ∧
              runIndex e ⟨t.val, by omega⟩ % 2 = 1 then 1 else 0 := by
    let A := Finset.univ.filter fun k : Fin (Fintype.card α - 1) =>
      k.val < t.val ∧ parityBoundary e k ∧
        runIndex e ⟨k.val, by omega⟩ % 2 = 1
    let B := Finset.univ.filter fun k : Fin (Fintype.card α - 1) =>
      k.val < t.val + 1 ∧ parityBoundary e k ∧
        runIndex e ⟨k.val, by omega⟩ % 2 = 1
    have hnot : t ∉ A := by simp [A]
    have hleft : strictBoundaryCount e ⟨t.val + 1, by omega⟩ = B.card := by
      simp [strictBoundaryCount, B]
    have hright : strictBoundaryCount e ⟨t.val, by omega⟩ = A.card := by
      simp [strictBoundaryCount, A]
    by_cases ht : parityBoundary e t ∧
        runIndex e ⟨t.val, by omega⟩ % 2 = 1
    · have hset : B = insert t A := by
        ext k
        simp only [B, A, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_insert]
        by_cases hkt : k = t
        · subst k
          simp [ht]
        · constructor
          · intro h
            right
            have hne : k.val ≠ t.val := by
              intro heq
              exact hkt (Fin.ext heq)
            exact ⟨by omega, h.2⟩
          · rintro (h | ⟨hlt, hpar⟩)
            · exact False.elim (hkt h)
            · exact ⟨by omega, hpar⟩
      rw [hleft, hright, if_pos ht, hset,
        Finset.card_insert_of_notMem hnot]
    · have hset : B = A := by
        ext k
        simp only [B, A, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          have hne : k.val ≠ t.val := by
            intro heq
            have hkt : k = t := Fin.ext heq
            subst k
            exact ht h.2
          exact ⟨by omega, h.2⟩
        · intro h
          exact ⟨by omega, h.2⟩
      rw [hleft, hright, if_neg ht, hset, add_zero]
  have hind : ∀ n : ℕ, (hn : n < Fintype.card α) →
      strictBoundaryCount e ⟨n, hn⟩ = runIndex e ⟨n, hn⟩ / 2 := by
    intro n
    induction n with
    | zero =>
        intro hn
        simp [strictBoundaryCount, runIndex]
    | succ n ih =>
        intro hn
        let t : Fin (Fintype.card α - 1) := ⟨n, by omega⟩
        have hprev := ih (by omega : n < Fintype.card α)
        have hs := hstep t
        have hr := runIndex_succ e t
        change strictBoundaryCount e ⟨n + 1, hn⟩ =
          strictBoundaryCount e ⟨n, by omega⟩ +
            (if parityBoundary e t ∧
              runIndex e ⟨n, by omega⟩ % 2 = 1 then 1 else 0) at hs
        change runIndex e ⟨n + 1, hn⟩ =
          runIndex e ⟨n, by omega⟩ +
            (if parityBoundary e t then 1 else 0) at hr
        rw [hs, hr, hprev]
        by_cases hb : parityBoundary e t
        · simp only [hb, true_and, if_true]
          by_cases hp : runIndex e ⟨n, by omega⟩ % 2 = 1
          · simp only [hp, if_true]
            omega
          · simp only [hp, if_false]
            omega
        · simp [hb]
  exact hind i.val i.isLt

/-- Descents that occur inside the fixed parity runs of a representative. -/
def internalDescentCount (e e' : EnumeratingExtension α)
    (ω : α → ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin (Fintype.card α - 1) =>
    ¬ parityBoundary e i ∧ descent ω e' i).card

/-- On one saturated-extension fiber, every canonical descent is either an
odd-to-even run boundary or an ordinary descent internal to an antichain run. -/
theorem compatible_descentCard_split [Nonempty α]
    (e e' : EnumeratingExtension α)
    (hcompat : ∀ x y : α,
      runIndex e (e.1.symm x) < runIndex e (e.1.symm y) →
        e'.1.symm x < e'.1.symm y)
    (ω : α → ℕ) (hbound : ∀ x, ω x < Fintype.card α)
    (hfirst : ∀ h : 0 < Fintype.card α,
      grade ℕ (e ⟨0, h⟩) % 2 = 0) :
    descentCard (parityLabel ω) e' =
      strictBoundaryCount e ⟨Fintype.card α - 1, by
        have hp : 0 < Fintype.card α := Fintype.card_pos
        omega⟩ + internalDescentCount e e' ω := by
  classical
  have hrun := (compatible_run_index e e' hcompat).1
  have hparity := (compatible_run_index e e' hcompat).2
  have hfirst' : ∀ h : 0 < Fintype.card α,
      grade ℕ (e' ⟨0, h⟩) % 2 = 0 := by
    intro h
    rw [hparity]
    exact hfirst h
  have hboundary (i : Fin (Fintype.card α - 1)) :
      parityBoundary e' i ↔ parityBoundary e i := by
    unfold parityBoundary
    rw [hparity ⟨i.val, by omega⟩, hparity ⟨i.val + 1, by omega⟩]
  let strictSet : Finset (Fin (Fintype.card α - 1)) :=
    Finset.univ.filter fun i => parityBoundary e i ∧
      runIndex e ⟨i.val, by omega⟩ % 2 = 1
  let innerSet : Finset (Fin (Fintype.card α - 1)) :=
    Finset.univ.filter fun i => ¬ parityBoundary e i ∧ descent ω e' i
  have hdis : Disjoint strictSet innerSet := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 : parityBoundary e i := (Finset.mem_filter.mp hi).2.1
    have h2 : ¬ parityBoundary e i := (Finset.mem_filter.mp hj).2.1
    exact h2 h1
  have hsets : descentFinset (parityLabel ω) e' = strictSet ∪ innerSet := by
    ext i
    simp only [descentFinset, strictSet, innerSet, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union]
    rw [parityLabel_descent_at_run e' ω hbound hfirst' i]
    rw [← (hboundary i)]
    rw [hrun ⟨i.val, by omega⟩]
    by_cases hb : parityBoundary e' i <;> simp [hb]
  have hstrict : strictSet.card =
      strictBoundaryCount e ⟨Fintype.card α - 1, by
        have hp : 0 < Fintype.card α := Fintype.card_pos
        omega⟩ := by
    unfold strictBoundaryCount
    congr 1
    ext i
    simp only [strictSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hi : i.val < Fintype.card α - 1 := i.isLt
    simp only [hi, true_and]
  change (descentFinset (parityLabel ω) e').card =
    strictBoundaryCount e ⟨Fintype.card α - 1, by
      have hp : 0 < Fintype.card α := Fintype.card_pos
      omega⟩ + innerSet.card
  rw [hsets, Finset.card_union_of_disjoint hdis, hstrict]

/-- Sorting a run fiber does not skip any position of the full extension. -/
theorem sorted_run_positions_adjacent (e : EnumeratingExtension α)
    (k : Fin (Fintype.card α))
    (i : Fin (Fintype.card (RunPosition e k) - 1)) :
    ((Fintype.orderIsoFinOfCardEq (RunPosition e k) rfl)
      ⟨i.val + 1, by omega⟩).1.val =
      ((Fintype.orderIsoFinOfCardEq (RunPosition e k) rfl)
        ⟨i.val, by omega⟩).1.val + 1 := by
  classical
  let iso : Fin (Fintype.card (RunPosition e k)) ≃o RunPosition e k :=
    Fintype.orderIsoFinOfCardEq (RunPosition e k) rfl
  let u := iso ⟨i.val, by omega⟩
  let v := iso ⟨i.val + 1, by omega⟩
  have huv : u.1.val < v.1.val := by
    have h := iso.strictMono (show
      (⟨i.val, by omega⟩ : Fin (Fintype.card (RunPosition e k))) <
        ⟨i.val + 1, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    exact h
  change v.1.val = u.1.val + 1
  by_contra hne
  have hgap : u.1.val + 1 < v.1.val := by omega
  let t : Fin (Fintype.card α) := ⟨u.1.val + 1, by omega⟩
  have hut : u.1 ≤ t := by
    apply Fin.mk_le_mk.mpr
    change u.1.val ≤ u.1.val + 1
    omega
  have htv : t ≤ v.1 := by
    apply Fin.mk_le_mk.mpr
    change u.1.val + 1 ≤ v.1.val
    omega
  have ht : runBucket e t = k :=
    (runBucket_interval e u.1 v.1 t hut htv (u.2.trans v.2.symm)).trans u.2
  let z : RunPosition e k := ⟨t, ht⟩
  have huz : u < z := by
    change u.1.val < u.1.val + 1
    omega
  have hzv : z < v := by
    change u.1.val + 1 < v.1.val
    exact hgap
  have hleft := iso.symm.strictMono huz
  have hright := iso.symm.strictMono hzv
  have hleft' : i.val < (iso.symm z).val := by
    change (iso.symm u).val < (iso.symm z).val at hleft
    simpa [u] using hleft
  have hright' : (iso.symm z).val < i.val + 1 := by
    change (iso.symm z).val < (iso.symm v).val at hright
    simpa [v] using hright
  omega

end
end D5.S3.Combinatorics.Posets.GradedGamma
