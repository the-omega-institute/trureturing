/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion
   mirror-E: none(waiver:delete-least-value)
   anchors: []
   utility: none
   digest: Deleting both least-value copies preserves every avoidance class. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion

open D5.S3.Combinatorics.Nonnesting

theorem delete_lowest_avoider (w : List ℕ) (n : ℕ) (Λ : List (List ℕ))
    (hw : w ∈ NonnestingDefs.avoiders (n + 1) Λ) :
    (w.filter (fun x => decide (1 < x))).map (fun x => x - 1) ∈
      NonnestingDefs.avoiders n Λ := by
  let u := w.filter (fun x => decide (1 < x))
  let v := u.map (fun x => x - 1)
  have huPositive : ∀ x ∈ u, 1 < x := by
    intro x hx
    simpa [u] using (List.mem_filter.mp hx).2
  have hrestore : v.map (fun x => x + 1) = u := by
    unfold v
    rw [List.map_map]
    calc
      u.map ((fun x => x + 1) ∘ (fun x => x - 1)) = u.map id := by
        apply List.map_congr_left
        intro x hx
        simp only [Function.comp_apply, id_eq]
        have := huPositive x hx
        omega
      _ = u := List.map_id u
  have huSub : List.Sublist u w := List.filter_sublist
  have hbase : ((List.range' 1 (n + 1)).flatMap fun i => [i, i]) =
      [1, 1] ++ ((List.range' 2 n).flatMap fun i => [i, i]) := by
    simp [List.range'_succ]
  have hhigh : ∀ x ∈ ((List.range' 2 n).flatMap fun i => [i, i]), 1 < x := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hx
    have hxi' : x = i := by simpa using hxi
    subst x
    have hir : 2 ≤ i ∧ i < 2 + n := by simpa using hi
    omega
  have huPerm : u.Perm ((List.range' 2 n).flatMap fun i => [i, i]) := by
    have hf := hw.1.filter (fun x => decide (1 < x))
    rw [hbase, List.filter_append] at hf
    have hhighFilter :
        (((List.range' 2 n).flatMap fun i => [i, i]).filter
          (fun x => decide (1 < x))) =
          ((List.range' 2 n).flatMap fun i => [i, i]) := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hhigh x hx]
    simpa [u, hhighFilter] using hf
  have hmap : ∀ s j : ℕ,
      (((List.range' (s + 1) j).flatMap fun i => [i, i]).map fun x => x - 1) =
        ((List.range' s j).flatMap fun i => [i, i]) := by
    intro s j
    induction j generalizing s with
    | zero => simp
    | succ j ih =>
      simp [List.range'_succ, ih (s + 1), Nat.add_assoc]
  have hvPerm : v.Perm ((List.range' 1 n).flatMap fun i => [i, i]) := by
    have hm := huPerm.map (fun x => x - 1)
    simpa [v, hmap 1 n] using hm
  have hocc (σ : List ℕ) (havoid : ¬ NonnestingDefs.Occurs σ w) :
      ¬ NonnestingDefs.Occurs σ v := by
    intro h
    rcases h with ⟨x, hxlt, hxmem, hxsub, _⟩
    let y : ℕ → ℕ := fun i => x i + 1
    apply havoid
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨y, ?_, ?_, ?_, by simp⟩
    · intro i hi hlt
      dsimp [y]
      exact Nat.add_lt_add_right (hxlt i hi hlt) 1
    · intro i hi hle
      have hx : x i ∈ v := hxmem i hi hle
      have hy : y i ∈ u := by
        rw [← hrestore]
        exact List.mem_map_of_mem hx
      exact huSub.subset hy
    · have hm := hxsub.map (fun x => x + 1)
      have hsub : List.Sublist (σ.map y) u := by
        simpa [y, hrestore, List.map_map, Function.comp_def] using hm
      exact hsub.trans huSub
  change v ∈ NonnestingDefs.avoiders n Λ
  exact ⟨hvPerm, hocc [1, 2, 2, 1] hw.2.1,
    hocc [2, 1, 1, 2] hw.2.2.1,
    fun σ hσ => hocc σ (hw.2.2.2 σ hσ)⟩

theorem first_order_after_filter (w : List ℕ) (k a b : ℕ)
    (hka : k < a) (hkb : k < b) (hma : a ∈ w) (hmb : b ∈ w)
    (hab : w.idxOf a < w.idxOf b) :
    (w.filter (fun x => decide (k < x))).idxOf a <
      (w.filter (fun x => decide (k < x))).idxOf b := by
  induction w with
  | nil => simp at hma
  | cons x xs ih =>
    have habne : a ≠ b := by
      intro heq
      subst b
      exact (Nat.lt_irrefl _ hab)
    by_cases hxa : x = a
    · subst x
      have hba : b ≠ a := Ne.symm habne
      have hbmem : b ∈ xs := by simpa [hba] using hmb
      simp [hka, List.idxOf_cons_ne _ habne]
    by_cases hxb : x = b
    · subst x
      have hba : b ≠ a := Ne.symm habne
      simp [List.idxOf_cons_ne _ hba] at hab
    have hma' : a ∈ xs := by
      rcases List.mem_cons.mp hma with h | h
      · exact (hxa h.symm).elim
      · exact h
    have hmb' : b ∈ xs := by
      rcases List.mem_cons.mp hmb with h | h
      · exact (hxb h.symm).elim
      · exact h
    have htail : xs.idxOf a < xs.idxOf b := by
      simpa [List.idxOf_cons_ne _ hxa, List.idxOf_cons_ne _ hxb] using hab
    have hih := ih hma' hmb' htail
    by_cases hkx : k < x
    · simpa [hkx, List.idxOf_cons_ne _ hxa, List.idxOf_cons_ne _ hxb]
        using Nat.succ_lt_succ hih
    · simpa [hkx] using hih

end D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion.delete_lowest_avoider
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion.first_order_after_filter
