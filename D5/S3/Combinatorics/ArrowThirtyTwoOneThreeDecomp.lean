/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp
   mirror-E: none(waiver:last-cycle-decomposition-of-the-arrow-pattern-32-1-to-3)
   anchors: []
   utility: none
   digest: Structural lemmas for splitting an arrow avoider at its final Foata cycle. -/

import D5.S3.Combinatorics.ArrowWilfCharacterization
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan

/-- Appending a new maximum as a singleton final cycle preserves all old Foata edges. -/
theorem hat_append_fresh_max (q : List ℕ) (m x : ℕ)
    (hm : ∀ y ∈ q, y < m) (hx : x ∈ q) :
    hat (q ++ [m]) x = hat q x := by
  let i := q.idxOf x
  have hi : i < q.length := List.idxOf_lt_length_of_mem hx
  have hidx : (q ++ [m]).idxOf x = i := List.idxOf_append_of_mem hx
  have hmax : IsLtrMax (q ++ [m]) q.length := by
    intro j hj
    have hjq : q.getD j 0 < m := by
      rw [List.getD_eq_getElem (l := q) 0 hj]
      exact hm _ (List.getElem_mem hj)
    rw [List.getD_append q [m] 0 j hj]
    simpa [List.getD_append_right] using hjq
  have hltr (j : ℕ) (hj : j < q.length) :
      IsLtrMax (q ++ [m]) j ↔ IsLtrMax q j := by
    constructor
    · intro h k hk
      have h' := h k hk
      rwa [List.getD_append q [m] 0 k (by omega),
        List.getD_append q [m] 0 j hj] at h'
    · intro h k hk
      rw [List.getD_append q [m] 0 k (by omega),
        List.getD_append q [m] 0 j hj]
      exact h k hk
  have hgreatest (j : ℕ) (hj : j < q.length) :
      Nat.findGreatest (IsLtrMax (q ++ [m])) j =
        Nat.findGreatest (IsLtrMax q) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Nat.findGreatest_succ, Nat.findGreatest_succ]
        by_cases h : IsLtrMax q (j + 1)
        · simp [h, (hltr (j + 1) hj).mpr h]
        · simp [h, (hltr (j + 1) hj).not.mpr h, ih (by omega)]
  have hbranch :
      (i + 1 < (q ++ [m]).length ∧ ¬ IsLtrMax (q ++ [m]) (i + 1)) ↔
      (i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)) := by
    constructor
    · rintro ⟨hnext, hnot⟩
      have hle : i + 1 ≤ q.length := by simpa using hnext
      have hlt : i + 1 < q.length := by
        by_contra h
        have heq : i + 1 = q.length := by omega
        exact hnot (heq ▸ hmax)
      exact ⟨hlt, (hltr _ hlt).mpr.mt hnot⟩
    · rintro ⟨hnext, hnot⟩
      refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      exact (hltr _ hnext).mp.mt hnot
  unfold hat
  rw [hidx]
  change (if i + 1 < (q ++ [m]).length ∧ ¬ IsLtrMax (q ++ [m]) (i + 1)
    then (q ++ [m]).getD (i + 1) 0
    else (q ++ [m]).getD (Nat.findGreatest (IsLtrMax (q ++ [m])) i) 0) =
    (if i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)
    then q.getD (i + 1) 0
    else q.getD (Nat.findGreatest (IsLtrMax q) i) 0)
  by_cases h : i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)
  · rw [if_pos (hbranch.mpr h), if_pos h]
    exact List.getD_append q [m] 0 (i + 1) h.1
  · have h' : ¬ (i + 1 < (q ++ [m]).length ∧
        ¬ IsLtrMax (q ++ [m]) (i + 1)) := fun t => h (hbranch.mp t)
    rw [if_neg h', if_neg h, hgreatest i hi]
    exact List.getD_append q [m] 0 _
      (lt_of_le_of_lt (Nat.findGreatest_le i) hi)

/-- The final position of a permutation belongs to the cycle started by its maximum. -/
theorem hat_last_entry_eq_max (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 (n + 1))) :
    hat p (p.getD (p.length - 1) 0) = n + 1 := by
  let m := n + 1
  have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hm : m ∈ p := hp.mem_iff.mpr (by
    dsimp [m]
    rw [List.range'_1_concat]
    simp [Nat.add_comm])
  have hi : p.idxOf m < p.length := List.idxOf_lt_length_of_mem hm
  have hget : p.getD (p.idxOf m) 0 = m := by
    rw [List.getD_eq_getElem (l := p) 0 hi, List.getElem_idxOf hi]
  have hbound (j : ℕ) (hj : j < p.length) (hne : j ≠ p.idxOf m) :
      p.getD j 0 < m := by
    have hjmem : p.getD j 0 ∈ p := by
      rw [List.getD_eq_getElem (l := p) 0 hj]
      exact List.getElem_mem hj
    have hrange := hp.mem_iff.mp hjmem
    rcases List.mem_range'.mp hrange with ⟨k, hk, hval⟩
    have hneq : p.getD j 0 ≠ m := by
      intro heq
      have helem : p[j] = p[p.idxOf m] := by
        rw [← List.getD_eq_getElem (l := p) 0 hj,
          ← List.getD_eq_getElem (l := p) 0 hi, hget]
        exact heq
      exact hne (hnd.getElem_inj_iff.mp helem)
    dsimp [m]
    omega
  have hltr : IsLtrMax p (p.idxOf m) := by
    intro j hj
    rw [hget]
    exact hbound j (by omega) (by omega)
  have hlastlt : p.length - 1 < p.length := by omega
  have hlastidx : p.idxOf (p.getD (p.length - 1) 0) = p.length - 1 := by
    rw [List.getD_eq_getElem (l := p) 0 hlastlt]
    exact hnd.idxOf_getElem (p.length - 1) hlastlt
  have hfind : Nat.findGreatest (IsLtrMax p) (p.length - 1) = p.idxOf m := by
    apply Nat.findGreatest_eq_iff.mpr
    refine ⟨by omega, (fun _ => hltr), ?_⟩
    intro j hj hle hlj
    have hjlen : j < p.length := by omega
    have hlt := hlj (p.idxOf m) hj
    rw [hget] at hlt
    exact (Nat.not_lt.mpr (hbound j hjlen (by omega)).le) hlt
  unfold hat
  rw [hlastidx]
  have hnot : ¬ (p.length - 1 + 1 < p.length ∧
      ¬ IsLtrMax p (p.length - 1 + 1)) := by omega
  rw [if_neg hnot, hfind, hget]

/-- After the global maximum, every nonterminal Foata edge follows the next word entry. -/
theorem hat_next_after_max (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 (n + 1))) (i : ℕ)
    (hafter : p.idxOf (n + 1) < i) (hnext : i + 1 < p.length) :
    hat p (p.getD i 0) = p.getD (i + 1) 0 := by
  let m := n + 1
  have hafter' : p.idxOf m < i := hafter
  have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hm : m ∈ p := hp.mem_iff.mpr (by
    dsimp [m]
    rw [List.range'_1_concat]
    simp [Nat.add_comm])
  have him : p.idxOf m < p.length := List.idxOf_lt_length_of_mem hm
  have hmval : p.getD (p.idxOf m) 0 = m := by
    rw [List.getD_eq_getElem (l := p) 0 him, List.getElem_idxOf him]
  have hine : i < p.length := by omega
  have hiidx : p.idxOf (p.getD i 0) = i := by
    rw [List.getD_eq_getElem (l := p) 0 hine]
    exact hnd.idxOf_getElem i hine
  have hnext_lt : p.getD (i + 1) 0 < m := by
    have hmem : p.getD (i + 1) 0 ∈ p := by
      rw [List.getD_eq_getElem (l := p) 0 hnext]
      exact List.getElem_mem hnext
    have hrange := hp.mem_iff.mp hmem
    rcases List.mem_range'.mp hrange with ⟨j, hj, hjval⟩
    have hne : p.getD (i + 1) 0 ≠ m := by
      intro heq
      have helem : p[i + 1] = p[p.idxOf m] := by
        rw [← List.getD_eq_getElem (l := p) 0 hnext,
          ← List.getD_eq_getElem (l := p) 0 him, hmval]
        exact heq
      have hidx := hnd.getElem_inj_iff.mp helem
      omega
    dsimp [m]
    omega
  have hnot : ¬ IsLtrMax p (i + 1) := by
    intro h
    have hlt := h (p.idxOf m) (by omega)
    rw [hmval] at hlt
    omega
  unfold hat
  rw [hiidx]
  rw [if_pos ⟨hnext, hnot⟩]

/-- The singleton final cycle is exactly the empty selected-set case of the decomposition. -/
theorem append_max_avoiders_iff (n : ℕ) (q : List ℕ) :
    q ++ [n + 1] ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ↔
      q ∈ avoiders n [3, 2] [(1, 3)] 3 := by
  have edgeCriterion (n : ℕ) (p : List ℕ) :
      p ∈ avoiders n [3, 2] [(1, 3)] 3 ↔
        p.Perm (List.range' 1 n) ∧
          ∀ a c : ℕ, a ∈ p → a < c → c < hat p a →
            [c, hat p a].Sublist p := by
    have hcontains : Contains [3, 2] [(1, 3)] 3 p ↔
        ∃ a c : ℕ, a ∈ p ∧ c ∈ p ∧ a < c ∧ c < hat p a ∧
          [hat p a, c].Sublist p := by
      constructor
      · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        refine ⟨x 1, x 2, hxmem 1 (by omega) (by omega),
          hxmem 2 (by omega) (by omega),
          hxlt 1 (by omega) (by omega), ?_, ?_⟩
        · rw [hxhat (1, 3) (by simp)]
          exact hxlt 2 (by omega) (by omega)
        · simpa [hxhat (1, 3) (by simp)] using hxsub
      · rintro ⟨a, c, ha, hc, hac, hcb, hsub⟩
        let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then c else hat p a
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl <;> simp [x, hac, hcb]
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · simpa [x] using ha
          · simpa [x] using hc
          · exact hsub.subset (by simp [x])
        · simpa [x] using hsub
        · intro bc hbc
          simp only [List.mem_singleton] at hbc
          subst bc
          simp [x]
    constructor
    · intro hp
      have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
      refine ⟨hp.1, ?_⟩
      intro a c ha hac hcb
      have hb : hat p a ∈ p := by
        change (if p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
          then p.getD (p.idxOf a + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf a)) 0) ∈ p
        split_ifs with hbranch
        · rw [List.getD_eq_getElem (l := p) 0 hbranch.1]
          exact List.getElem_mem hbranch.1
        · have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
          have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf a) < p.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) hi
          rw [List.getD_eq_getElem (l := p) 0 hg]
          exact List.getElem_mem hg
      have hc : c ∈ p := by
        have hra : a ∈ List.range' 1 n := hp.1.mem_iff.mp ha
        have hrb : hat p a ∈ List.range' 1 n := hp.1.mem_iff.mp hb
        have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
        rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
        apply hp.1.mem_iff.mpr
        apply List.mem_range'.mpr
        refine ⟨c - 1, ?_, ?_⟩ <;> omega
      rcases pair_sublist_total hnd (Nat.ne_of_lt hcb) hc hb with h | h
      · exact h
      · exact (hp.2 (hcontains.mpr ⟨a, c, ha, hc, hac, hcb, h⟩)).elim
    · rintro ⟨hperm, hedge⟩
      refine ⟨hperm, ?_⟩
      intro h
      rcases hcontains.mp h with ⟨a, c, ha, hc, hac, hcb, hbad⟩
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
      exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb)
        ⟨hedge a c ha hac hcb, hbad⟩
  let m := n + 1
  have hperm : (q ++ [m]).Perm (List.range' 1 (n + 1)) ↔
      q.Perm (List.range' 1 n) := by
    rw [List.range'_1_concat]
    simpa [m, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (List.perm_append_right_iff [m] :
        (q ++ [m]).Perm (List.range' 1 n ++ [m]) ↔
          q.Perm (List.range' 1 n))
  have hpair (a b : ℕ) (ha : a < m) (hb : b < m) :
      [a, b].Sublist (q ++ [m]) ↔ [a, b].Sublist q := by
    constructor
    · intro h
      apply h.of_sublist_append_left
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_singleton]
      rcases hx with rfl | rfl <;> omega
    · intro h
      exact List.sublist_append_of_sublist_left h
  constructor
  · intro hp
    have hqperm : q.Perm (List.range' 1 n) := hperm.mp hp.1
    have hm : ∀ y ∈ q, y < m := by
      intro y hy
      have hr := hqperm.mem_iff.mp hy
      rcases List.mem_range'.mp hr with ⟨j, hj, hjy⟩
      dsimp [m]
      omega
    have hedge := (edgeCriterion (n + 1) (q ++ [m])).mp hp |>.2
    apply (edgeCriterion n q).mpr
    refine ⟨hqperm, ?_⟩
    intro a c ha hac hcb
    have hb : hat q a ∈ q := by
      change (if q.idxOf a + 1 < q.length ∧ ¬ IsLtrMax q (q.idxOf a + 1)
        then q.getD (q.idxOf a + 1) 0
        else q.getD (Nat.findGreatest (IsLtrMax q) (q.idxOf a)) 0) ∈ q
      split_ifs with hbranch
      · rw [List.getD_eq_getElem (l := q) 0 hbranch.1]
        exact List.getElem_mem hbranch.1
      · have hi : q.idxOf a < q.length := List.idxOf_lt_length_of_mem ha
        have hg := lt_of_le_of_lt
          (Nat.findGreatest_le (P := IsLtrMax q) (q.idxOf a)) hi
        rw [List.getD_eq_getElem (l := q) 0 hg]
        exact List.getElem_mem hg
    have hmb : hat q a < m := hm _ hb
    have hmc : c < m := lt_trans hcb hmb
    have hgood := hedge a c (List.mem_append.mpr (Or.inl ha)) hac
      (by rw [hat_append_fresh_max q m a hm ha]; exact hcb)
    rw [hat_append_fresh_max q m a hm ha] at hgood
    exact (hpair c (hat q a) hmc hmb).mp hgood
  · intro hq
    have hqperm : q.Perm (List.range' 1 n) := hq.1
    have hm : ∀ y ∈ q, y < m := by
      intro y hy
      have hr := hqperm.mem_iff.mp hy
      rcases List.mem_range'.mp hr with ⟨j, hj, hjy⟩
      dsimp [m]
      omega
    have hqnodup : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
    have hmn : m ∉ q := by
      intro h
      exact (Nat.lt_irrefl m) (hm m h)
    have happnodup : (q ++ [m]).Nodup := by
      simpa [List.concat_eq_append] using (List.nodup_concat q m).mpr ⟨hmn, hqnodup⟩
    have hmax : IsLtrMax (q ++ [m]) q.length := by
      intro j hj
      have hjq : q.getD j 0 < m := by
        rw [List.getD_eq_getElem (l := q) 0 hj]
        exact hm _ (List.getElem_mem hj)
      rw [List.getD_append q [m] 0 j hj]
      simpa [List.getD_append_right] using hjq
    have hmidx : (q ++ [m]).idxOf m = q.length := by
      simp [List.idxOf_append_of_notMem hmn]
    have hmfixed : hat (q ++ [m]) m = m := by
      apply (hat_fixed_iff happnodup (List.mem_append.mpr (Or.inr (by simp)))).mpr
      constructor
      · simpa [hmidx] using hmax
      · left
        simp [hmidx]
    apply (edgeCriterion (n + 1) (q ++ [m])).mpr
    refine ⟨hperm.mpr hqperm, ?_⟩
    intro a c ha hac hcb
    rcases List.mem_append.mp ha with ha | ha
    · have hqgood := (edgeCriterion n q).mp hq |>.2
      rw [hat_append_fresh_max q m a hm ha] at hcb ⊢
      exact List.sublist_append_of_sublist_left (hqgood a c ha hac hcb)
    · have ham : a = m := by simpa using ha
      subst a
      rw [hmfixed] at hcb
      omega

/-- The last letter of the final Foata cycle is the largest of its other letters. -/
theorem final_cycle_last_is_max (n : ℕ) (pre w : List ℕ) (a : ℕ)
    (hp : pre ++ (n + 1) :: (w ++ [a]) ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3) :
    ∀ c ∈ w, c ≤ a := by
  have edgeCriterion (n : ℕ) (p : List ℕ) :
      p ∈ avoiders n [3, 2] [(1, 3)] 3 ↔
        p.Perm (List.range' 1 n) ∧
          ∀ a c : ℕ, a ∈ p → a < c → c < hat p a →
            [c, hat p a].Sublist p := by
    have hcontains : Contains [3, 2] [(1, 3)] 3 p ↔
        ∃ a c : ℕ, a ∈ p ∧ c ∈ p ∧ a < c ∧ c < hat p a ∧
          [hat p a, c].Sublist p := by
      constructor
      · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        refine ⟨x 1, x 2, hxmem 1 (by omega) (by omega),
          hxmem 2 (by omega) (by omega),
          hxlt 1 (by omega) (by omega), ?_, ?_⟩
        · rw [hxhat (1, 3) (by simp)]
          exact hxlt 2 (by omega) (by omega)
        · simpa [hxhat (1, 3) (by simp)] using hxsub
      · rintro ⟨a, c, ha, hc, hac, hcb, hsub⟩
        let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then c else hat p a
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl <;> simp [x, hac, hcb]
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · simpa [x] using ha
          · simpa [x] using hc
          · exact hsub.subset (by simp [x])
        · simpa [x] using hsub
        · intro bc hbc
          simp only [List.mem_singleton] at hbc
          subst bc
          simp [x]
    constructor
    · intro hp
      have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
      refine ⟨hp.1, ?_⟩
      intro a c ha hac hcb
      have hb : hat p a ∈ p := by
        change (if p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
          then p.getD (p.idxOf a + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf a)) 0) ∈ p
        split_ifs with hbranch
        · rw [List.getD_eq_getElem (l := p) 0 hbranch.1]
          exact List.getElem_mem hbranch.1
        · have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
          have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf a) < p.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) hi
          rw [List.getD_eq_getElem (l := p) 0 hg]
          exact List.getElem_mem hg
      have hc : c ∈ p := by
        have hra : a ∈ List.range' 1 n := hp.1.mem_iff.mp ha
        have hrb : hat p a ∈ List.range' 1 n := hp.1.mem_iff.mp hb
        have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
        rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
        apply hp.1.mem_iff.mpr
        apply List.mem_range'.mpr
        refine ⟨c - 1, ?_, ?_⟩ <;> omega
      rcases pair_sublist_total hnd (Nat.ne_of_lt hcb) hc hb with h | h
      · exact h
      · exact (hp.2 (hcontains.mpr ⟨a, c, ha, hc, hac, hcb, h⟩)).elim
    · rintro ⟨hperm, hedge⟩
      refine ⟨hperm, ?_⟩
      intro h
      rcases hcontains.mp h with ⟨a, c, ha, hc, hac, hcb, hbad⟩
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
      exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb)
        ⟨hedge a c ha hac hcb, hbad⟩
  let p := pre ++ (n + 1) :: (w ++ [a])
  have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
  have hlast : p.getD (p.length - 1) 0 = a := by
    simp [p]
  have hwrap : hat p a = n + 1 := by
    rw [← hlast]
    exact hat_last_entry_eq_max n p hp.1
  have hsmall : ∀ c ∈ w, c < n + 1 := by
    intro c hc
    have hrange : c ∈ List.range' 1 (n + 1) := hp.1.mem_iff.mp (by
      simp [List.mem_append, hc])
    rcases List.mem_range'.mp hrange with ⟨j, hj, hcval⟩
    have htailnd : ((n + 1) :: (w ++ [a])).Nodup := hnd.of_append_right
    have hnot : n + 1 ∉ w ++ [a] := (List.nodup_cons.mp htailnd).1
    have hne : c ≠ n + 1 := by
      intro heq
      exact hnot (heq ▸ List.mem_append.mpr (Or.inl hc))
    omega
  have hedge := (edgeCriterion (n + 1) p).mp hp |>.2
  intro c hc
  by_contra hca
  have hac : a < c := Nat.lt_of_not_ge hca
  have hcn : c < n + 1 := hsmall c hc
  have ha : a ∈ p := by
    simp [p, List.mem_append]
  have hcnsub : [c, n + 1].Sublist p := by
    have h := hedge a c ha hac (by simpa [p, hwrap] using hcn)
    simpa [p, hwrap] using h
  have hncsub : [n + 1, c].Sublist p := by
    have hc' : [c].Sublist (w ++ [a]) :=
      List.singleton_sublist.mpr (List.mem_append.mpr (Or.inl hc))
    exact List.sublist_append_of_sublist_right (hc'.cons_cons (n + 1))
  exact pair_sublist_asymm hnd (Nat.ne_of_lt hcn) ⟨hcnsub, hncsub⟩

/-- The ordering after the final maximum contains no classical `132` pattern. -/
theorem final_cycle_avoid132 (n : ℕ) (pre w : List ℕ)
    (hp : pre ++ (n + 1) :: w ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3) :
    ¬ Has132 w := by
  have edgeCriterion (n : ℕ) (p : List ℕ) :
      p ∈ avoiders n [3, 2] [(1, 3)] 3 ↔
        p.Perm (List.range' 1 n) ∧
          ∀ a c : ℕ, a ∈ p → a < c → c < hat p a →
            [c, hat p a].Sublist p := by
    have hcontains : Contains [3, 2] [(1, 3)] 3 p ↔
        ∃ a c : ℕ, a ∈ p ∧ c ∈ p ∧ a < c ∧ c < hat p a ∧
          [hat p a, c].Sublist p := by
      constructor
      · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
        refine ⟨x 1, x 2, hxmem 1 (by omega) (by omega),
          hxmem 2 (by omega) (by omega),
          hxlt 1 (by omega) (by omega), ?_, ?_⟩
        · rw [hxhat (1, 3) (by simp)]
          exact hxlt 2 (by omega) (by omega)
        · simpa [hxhat (1, 3) (by simp)] using hxsub
      · rintro ⟨a, c, ha, hc, hac, hcb, hsub⟩
        let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then c else hat p a
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl <;> simp [x, hac, hcb]
        · intro i hi hik
          have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · simpa [x] using ha
          · simpa [x] using hc
          · exact hsub.subset (by simp [x])
        · simpa [x] using hsub
        · intro bc hbc
          simp only [List.mem_singleton] at hbc
          subst bc
          simp [x]
    constructor
    · intro hp
      have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
      refine ⟨hp.1, ?_⟩
      intro a c ha hac hcb
      have hb : hat p a ∈ p := by
        change (if p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
          then p.getD (p.idxOf a + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) (p.idxOf a)) 0) ∈ p
        split_ifs with hbranch
        · rw [List.getD_eq_getElem (l := p) 0 hbranch.1]
          exact List.getElem_mem hbranch.1
        · have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
          have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf a) < p.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) hi
          rw [List.getD_eq_getElem (l := p) 0 hg]
          exact List.getElem_mem hg
      have hc : c ∈ p := by
        have hra : a ∈ List.range' 1 n := hp.1.mem_iff.mp ha
        have hrb : hat p a ∈ List.range' 1 n := hp.1.mem_iff.mp hb
        have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
        rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
        apply hp.1.mem_iff.mpr
        apply List.mem_range'.mpr
        refine ⟨c - 1, ?_, ?_⟩ <;> omega
      rcases pair_sublist_total hnd (Nat.ne_of_lt hcb) hc hb with h | h
      · exact h
      · exact (hp.2 (hcontains.mpr ⟨a, c, ha, hc, hac, hcb, h⟩)).elim
    · rintro ⟨hperm, hedge⟩
      refine ⟨hperm, ?_⟩
      intro h
      rcases hcontains.mp h with ⟨a, c, ha, hc, hac, hcb, hbad⟩
      have hnd : p.Nodup := hperm.nodup_iff.mpr List.nodup_range'
      exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb)
        ⟨hedge a c ha hac hcb, hbad⟩
  let p := pre ++ (n + 1) :: w
  have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
  have hwnd : w.Nodup := (hnd.of_append_right).of_cons
  have hdis := (List.nodup_append'.mp hnd).2.2
  have hmaxnot : n + 1 ∉ pre := by
    intro h
    exact hdis h (by simp)
  have hmaxidx : p.idxOf (n + 1) = pre.length := by
    simp [p, List.idxOf_append_of_notMem hmaxnot]
  have hget (t : ℕ) (ht : t < w.length) :
      p.getD (pre.length + 1 + t) 0 = w.getD t 0 := by
    dsimp [p]
    rw [List.getD_append_right pre ((n + 1) :: w) 0
      (pre.length + 1 + t) (by omega)]
    have heq : pre.length + 1 + t - pre.length = t + 1 := by omega
    rw [heq, List.getD_eq_getElem (l := (n + 1) :: w) 0 (by simp [ht])]
    change w[t] = w.getD t 0
    rw [List.getD_eq_getElem (l := w) 0 ht]
  have hedge := (edgeCriterion (n + 1) p).mp hp |>.2
  intro h132
  rcases (hasAdj132_iff w hwnd).mpr h132 with
    ⟨i, k, hik, hk, hai, hcb⟩
  have hi : i < w.length := by omega
  have hi1 : i + 1 < w.length := by omega
  let a := w.getD i 0
  let b := w.getD (i + 1) 0
  let c := w.getD k 0
  have hposi : pre.length + 1 + i < p.length := by simp [p]; omega
  have hposi1 : pre.length + 1 + i + 1 < p.length := by simp [p]; omega
  have hnext : hat p a = b := by
    have h := hat_next_after_max n p hp.1 (pre.length + 1 + i)
      (by rw [hmaxidx]; omega) hposi1
    rw [hget i hi] at h
    have hidxeq : pre.length + 1 + i + 1 = pre.length + 1 + (i + 1) := by omega
    rw [hidxeq, hget (i + 1) hi1] at h
    exact h
  have ha : a ∈ p := by
    have h : p.getD (pre.length + 1 + i) 0 ∈ p := by
      rw [List.getD_eq_getElem (l := p) 0 hposi]
      exact List.getElem_mem hposi
    rw [hget i hi] at h
    exact h
  have hbcw : [b, c].Sublist w := by
    have hs : ([⟨i + 1, hi1⟩, ⟨k, hk⟩] : List (Fin w.length)).Pairwise (· < ·) := by
      simp [hik]
    have hs' := List.map_getElem_sublist (l := w) hs
    change [w.getD (i + 1) 0, w.getD k 0].Sublist w
    rw [List.getD_eq_getElem (l := w) 0 hi1,
      List.getD_eq_getElem (l := w) 0 hk]
    simpa using hs'
  have hbc : [b, c].Sublist p := by
    exact List.sublist_append_of_sublist_right (hbcw.cons (n + 1))
  have hcbsub : [c, b].Sublist p := by
    have h := hedge a c ha hai (by simpa [hnext, c, b] using hcb)
    simpa [hnext] using h
  exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb) ⟨hcbsub, hbc⟩

end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp

#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp.hat_last_entry_eq_max
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp.append_max_avoiders_iff
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp.final_cycle_avoid132
