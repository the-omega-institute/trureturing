/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection
   mirror-E: none(waiver:last-cycle-bijection-of-the-arrow-pattern-32-1-to-3)
   anchors: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp]
   utility: none
   digest: Foata edges of the prefix are stable under an arbitrary final cycle, and cannot cross a value selected into that cycle. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp
import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDecomp
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeCatalan
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs

/-- Starting a final cycle at a fresh maximum preserves every Foata edge of the prefix,
even when the cycle has a nonempty tail. -/
theorem hat_append_final_cycle (q w : List ℕ) (m x : ℕ)
    (hm : ∀ y ∈ q, y < m) (hx : x ∈ q) :
    hat (q ++ m :: w) x = hat q x := by
  let i := q.idxOf x
  have hi : i < q.length := List.idxOf_lt_length_of_mem hx
  have hidx : (q ++ m :: w).idxOf x = i := List.idxOf_append_of_mem hx
  have hmax : IsLtrMax (q ++ m :: w) q.length := by
    intro j hj
    have hjq : q.getD j 0 < m := by
      rw [List.getD_eq_getElem (l := q) 0 hj]
      exact hm _ (List.getElem_mem hj)
    rw [List.getD_append q (m :: w) 0 j hj]
    simpa [List.getD_append_right] using hjq
  have hltr (j : ℕ) (hj : j < q.length) :
      IsLtrMax (q ++ m :: w) j ↔ IsLtrMax q j := by
    constructor
    · intro h k hk
      have h' := h k hk
      rwa [List.getD_append q (m :: w) 0 k (by omega),
        List.getD_append q (m :: w) 0 j hj] at h'
    · intro h k hk
      rw [List.getD_append q (m :: w) 0 k (by omega),
        List.getD_append q (m :: w) 0 j hj]
      exact h k hk
  have hgreatest (j : ℕ) (hj : j < q.length) :
      Nat.findGreatest (IsLtrMax (q ++ m :: w)) j =
        Nat.findGreatest (IsLtrMax q) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Nat.findGreatest_succ, Nat.findGreatest_succ]
        by_cases h : IsLtrMax q (j + 1)
        · simp [h, (hltr (j + 1) hj).mpr h]
        · simp [h, (hltr (j + 1) hj).not.mpr h, ih (by omega)]
  have hbranch :
      (i + 1 < (q ++ m :: w).length ∧ ¬ IsLtrMax (q ++ m :: w) (i + 1)) ↔
      (i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)) := by
    constructor
    · rintro ⟨_, hnot⟩
      have hlt : i + 1 < q.length := by
        by_contra h
        have heq : i + 1 = q.length := by omega
        exact hnot (heq ▸ hmax)
      exact ⟨hlt, (hltr _ hlt).mpr.mt hnot⟩
    · rintro ⟨hnext, hnot⟩
      refine ⟨by simp only [List.length_append, List.length_cons]; omega, ?_⟩
      exact (hltr _ hnext).mp.mt hnot
  unfold hat
  rw [hidx]
  change (if i + 1 < (q ++ m :: w).length ∧ ¬ IsLtrMax (q ++ m :: w) (i + 1)
    then (q ++ m :: w).getD (i + 1) 0
    else (q ++ m :: w).getD (Nat.findGreatest (IsLtrMax (q ++ m :: w)) i) 0) =
    (if i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)
    then q.getD (i + 1) 0
    else q.getD (Nat.findGreatest (IsLtrMax q) i) 0)
  by_cases h : i + 1 < q.length ∧ ¬ IsLtrMax q (i + 1)
  · rw [if_pos (hbranch.mpr h), if_pos h]
    exact List.getD_append q (m :: w) 0 (i + 1) h.1
  · have h' : ¬ (i + 1 < (q ++ m :: w).length ∧
        ¬ IsLtrMax (q ++ m :: w) (i + 1)) := fun t => h (hbranch.mp t)
    rw [if_neg h', if_neg h, hgreatest i hi]
    exact List.getD_append q (m :: w) 0 _
      (lt_of_le_of_lt (Nat.findGreatest_le i) hi)

/-- A prefix edge cannot jump over a value lying in the final cycle. -/
theorem no_prefix_edge_crosses_final_cycle (n : ℕ) (q w : List ℕ) (a c : ℕ)
    (hp : q ++ (n + 1) :: w ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3)
    (ha : a ∈ q) (hc : c ∈ w) (hac : a < c) :
    ¬ c < hat q a := by
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
  intro hcb
  let p := q ++ (n + 1) :: w
  have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
  have hqnd : q.Nodup := hnd.of_append_left
  have hdis := (List.nodup_append'.mp hnd).2.2
  have hm : ∀ y ∈ q, y < n + 1 := by
    intro y hy
    have hrange : y ∈ List.range' 1 (n + 1) := hp.1.mem_iff.mp (by
      exact List.mem_append.mpr (Or.inl hy))
    rcases List.mem_range'.mp hrange with ⟨j, hj, hjy⟩
    have hne : y ≠ n + 1 := by
      intro heq
      exact hdis hy (by simp [heq])
    omega
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
  have hgood := (edgeCriterion (n + 1) p).mp hp |>.2
  have hcbsub : [c, hat q a].Sublist p := by
    have h := hgood a c (List.mem_append.mpr (Or.inl ha)) hac
      (by rw [hat_append_final_cycle q w (n + 1) a hm ha]; exact hcb)
    change [c, hat (q ++ (n + 1) :: w) a].Sublist p at h
    rwa [hat_append_final_cycle q w (n + 1) a hm ha] at h
  have hbcsub : [hat q a, c].Sublist p := by
    have hbs : [hat q a].Sublist q := List.singleton_sublist.mpr hb
    have hcs : [c].Sublist ((n + 1) :: w) :=
      (List.singleton_sublist.mpr hc).cons (n + 1)
    simpa using hbs.append hcs
  exact pair_sublist_asymm hnd (Nat.ne_of_lt hcb) ⟨hcbsub, hbcsub⟩

/-- The old prefix inherits the arrow edge condition after the last cycle is
removed, even though its support need not be an initial interval. -/
theorem prefix_edge_condition_of_avoider (n : ℕ) (q w : List ℕ)
    (hp : q ++ (n + 1) :: w ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3) :
    ∀ a c : ℕ, a ∈ q → a < c → c < hat q a →
      [c, hat q a].Sublist q := by
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
  let p := q ++ (n + 1) :: w
  have hnd : p.Nodup := hp.1.nodup_iff.mpr List.nodup_range'
  have hdis := (List.nodup_append'.mp hnd).2.2
  have hm : ∀ y ∈ q, y < n + 1 := by
    intro y hy
    have hrange : y ∈ List.range' 1 (n + 1) := hp.1.mem_iff.mp
      (List.mem_append.mpr (Or.inl hy))
    rcases List.mem_range'.mp hrange with ⟨j, hj, hjy⟩
    have hne : y ≠ n + 1 := by
      intro heq
      exact hdis hy (by simp [heq])
    omega
  intro a c ha hac hcb
  have hbmem : hat q a ∈ q := by
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
  have hsub : [c, hat q a].Sublist p := by
    have h := (edgeCriterion (n + 1) p).mp hp |>.2
    have h' := h a c (List.mem_append.mpr (Or.inl ha)) hac
      (by rw [hat_append_final_cycle q w (n + 1) a hm ha]; exact hcb)
    change [c, hat (q ++ (n + 1) :: w) a].Sublist p at h'
    rwa [hat_append_final_cycle q w (n + 1) a hm ha] at h'
  have hcmem : c ∈ q := by
    have hc : c ∈ p := hsub.subset (by simp)
    rcases List.mem_append.mp hc with hcq | hctail
    · exact hcq
    · rcases List.mem_cons.mp hctail with hce | hcw
      · have hbound := hm _ hbmem
        omega
      · exact False.elim ((no_prefix_edge_crosses_final_cycle n q w a c hp ha hcw hac) hcb)
  apply hsub.of_sublist_append_left
  intro x hx
  have hxq : x ∈ q := by
    rcases (show x = c ∨ x = hat q a from by simpa using hx) with h | h
    · exact h ▸ hcmem
    · exact h ▸ hbmem
  exact hdis hxq

/-- The nontrivial final Foata cycle obeys the arrow edge condition when its last
letter dominates the earlier letters and its complete tail avoids `132`. -/
theorem final_cycle_edge_condition (n : ℕ) (q u : List ℕ) (b : ℕ)
    (hpperm : (q ++ (n + 1) :: (u ++ [b])).Perm (List.range' 1 (n + 1)))
    (hb : ∀ x ∈ u, x < b) (h132 : ¬ Has132 (u ++ [b])) :
    ∀ a ∈ u ++ [b], ∀ c : ℕ, a < c →
      c < hat (q ++ (n + 1) :: (u ++ [b])) a →
        [c, hat (q ++ (n + 1) :: (u ++ [b])) a].Sublist
          (q ++ (n + 1) :: (u ++ [b])) := by
  let w := u ++ [b]
  let p := q ++ (n + 1) :: w
  have hnd : p.Nodup := hpperm.nodup_iff.mpr List.nodup_range'
  have hqnd : q.Nodup := hnd.of_append_left
  have htailnd : ((n + 1) :: w).Nodup := hnd.of_append_right
  have hwnd : w.Nodup := htailnd.of_cons
  have hdis := (List.nodup_append'.mp hnd).2.2
  have hmaxnot : n + 1 ∉ q := by
    intro h
    exact hdis h (by simp)
  have hmaxidx : p.idxOf (n + 1) = q.length := by
    simp [p, List.idxOf_append_of_notMem hmaxnot]
  have hsmall (x : ℕ) (hx : x ∈ w) : x < n + 1 := by
    have hrange : x ∈ List.range' 1 (n + 1) :=
      hpperm.mem_iff.mp (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hx))))
    rcases List.mem_range'.mp hrange with ⟨j, hj, hjx⟩
    have hne : x ≠ n + 1 := by
      intro heq
      exact htailnd.notMem (by simpa [heq] using hx)
    omega
  have hmember (a c d : ℕ) (ha : a ∈ p) (hd : d ∈ p)
      (hac : a < c) (hcd : c < d) : c ∈ p := by
    have hra := hpperm.mem_iff.mp ha
    have hrd := hpperm.mem_iff.mp hd
    have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
    rcases List.mem_range'.mp hrd with ⟨j, hj, hjd⟩
    apply hpperm.mem_iff.mpr
    apply List.mem_range'.mpr
    refine ⟨c - 1, ?_, ?_⟩ <;> omega
  have hpre_before (x : ℕ) (hx : x ∈ q) (y : ℕ) (hy : y ∈ (n + 1) :: w) :
      [x, y].Sublist p := by
    exact (List.singleton_sublist.mpr hx).append (List.singleton_sublist.mpr hy)
  intro a ha c hac hca
  rcases List.mem_append.mp ha with hau | hab
  · let i := u.idxOf a
    have hi : i < u.length := List.idxOf_lt_length_of_mem hau
    have hiw : i < w.length := by simp [w]; omega
    have hinext : i + 1 < w.length := by simp [w]; omega
    have hidx : w.idxOf a = i := by
      simpa [w, i] using (List.idxOf_append_of_mem (l₂ := [b]) hau)
    have hget : w.getD i 0 = a := by
      calc
        w.getD i 0 = w.getD (w.idxOf a) 0 := by rw [hidx]
        _ = a := by
          rw [List.getD_eq_getElem (l := w) 0 (List.idxOf_lt_length_of_mem
            (List.mem_append.mpr (Or.inl hau)))]
          exact List.getElem_idxOf (List.idxOf_lt_length_of_mem
            (List.mem_append.mpr (Or.inl hau)))
    let d := w.getD (i + 1) 0
    have hdmem : d ∈ w := by
      change w.getD (i + 1) 0 ∈ w
      rw [List.getD_eq_getElem (l := w) 0 hinext]
      exact List.getElem_mem hinext
    have hpos : q.length + 1 + i + 1 < p.length := by
      simp [p, w]
      omega
    have hpget (t : ℕ) (ht : t < w.length) :
        p.getD (q.length + 1 + t) 0 = w.getD t 0 := by
      dsimp [p]
      rw [List.getD_append_right q ((n + 1) :: w) 0
        (q.length + 1 + t) (by omega)]
      have heq : q.length + 1 + t - q.length = t + 1 := by omega
      rw [heq, List.getD_eq_getElem (l := (n + 1) :: w) 0 (by simp [ht])]
      change w[t] = w.getD t 0
      rw [List.getD_eq_getElem (l := w) 0 ht]
    have hhat : hat p a = d := by
      have h := hat_next_after_max n p hpperm (q.length + 1 + i)
        (by rw [hmaxidx]; omega) hpos
      rw [hpget i hiw, hget] at h
      have heq : q.length + 1 + i + 1 = q.length + 1 + (i + 1) := by omega
      rw [heq, hpget (i + 1) hinext] at h
      exact h
    rw [hhat] at hca ⊢
    have hc : c ∈ p := hmember a c d
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hau))))))
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hdmem)))) hac hca
    rcases List.mem_append.mp hc with hcq | hctail
    · exact hpre_before c hcq d (by simp [hdmem])
    · rcases List.mem_cons.mp hctail with hcmax | hcw
      · have : d < n + 1 := hsmall d hdmem
        omega
      · rcases pair_sublist_total hwnd (Nat.ne_of_lt hca) hcw hdmem with hcd | hdc
        · exact List.sublist_append_of_sublist_right (hcd.cons (n + 1))
        · have hid : w.idxOf d = i + 1 := by
            change w.idxOf (w.getD (i + 1) 0) = i + 1
            rw [List.getD_eq_getElem (l := w) 0 hinext]
            exact hwnd.idxOf_getElem (i + 1) hinext
          have hk : w.idxOf c < w.length := List.idxOf_lt_length_of_mem hcw
          have hdk : i + 1 < w.idxOf c := by
            rw [← hid]
            obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hdc
            let i₀ : Fin [d, c].length := ⟨0, by simp⟩
            let i₁ : Fin [d, c].length := ⟨1, by simp⟩
            have hdval : d = w[f i₀] := by simpa [i₀] using hf i₀
            have hcval' : c = w[f i₁] := by simpa [i₁] using hf i₁
            rw [hdval, hcval']
            have hfi : w.idxOf w[f i₀] = (f i₀).val := by
              simpa only [List.get_eq_getElem, Fin.getElem_fin] using
                List.get_idxOf hwnd (f i₀)
            have hfj : w.idxOf w[f i₁] = (f i₁).val := by
              simpa only [List.get_eq_getElem, Fin.getElem_fin] using
                List.get_idxOf hwnd (f i₁)
            rw [hfi, hfj]
            exact f.strictMono (by norm_num [i₀, i₁])
          have hcval : w.getD (w.idxOf c) 0 = c := by
            rw [List.getD_eq_getElem (l := w) 0 hk, List.getElem_idxOf hk]
          have hocc : Has132 w := by
            refine ⟨i, i + 1, w.idxOf c, by omega, hdk, hk, ?_, ?_⟩
            · rw [hget, hcval]
              exact hac
            · rw [hcval]
              exact hca
          exact (h132 hocc).elim
  · have hae : a = b := by simpa using hab
    subst a
    have hlast : p.getD (p.length - 1) 0 = b := by simp [p, w]
    have hhat : hat p b = n + 1 := by
      rw [← hlast]
      exact hat_last_entry_eq_max n p hpperm
    rw [hhat] at hca ⊢
    have hc : c ∈ p := hmember b c (n + 1)
      (List.mem_append.mpr (Or.inr (by simp [w])))
      (List.mem_append.mpr (Or.inr (by simp))) hac hca
    rcases List.mem_append.mp hc with hcq | hctail
    · exact hpre_before c hcq (n + 1) (by simp)
    · rcases List.mem_cons.mp hctail with hce | hcw
      · omega
      · rcases List.mem_append.mp hcw with hcu | hcb
        · have := hb c hcu
          omega
        · have : c = b := by simpa using hcb
          omega

/-- Appending a new maximum leaves the `132` status of a word unchanged. -/
theorem has132_append_max_iff (u : List ℕ) (b : ℕ)
    (hb : ∀ x ∈ u, x < b) : Has132 (u ++ [b]) ↔ Has132 u := by
  have hget (i : ℕ) (hi : i < u.length) :
      (u ++ [b]).getD i 0 = u.getD i 0 :=
    List.getD_append u [b] 0 i hi
  constructor
  · rintro ⟨i, j, k, hij, hjk, hk, hik, hkj⟩
    have hkle : k ≤ u.length := by simp at hk; omega
    by_cases hku : k < u.length
    · exact ⟨i, j, k, hij, hjk, hku,
        by simpa only [hget i (by omega), hget k hku] using hik,
        by simpa only [hget k hku, hget j (by omega)] using hkj⟩
    · have hkeq : k = u.length := by omega
      have hlast : (u ++ [b]).getD k 0 = b := by
        subst k
        simp
      have hjmem : u.getD j 0 ∈ u := by
        rw [List.getD_eq_getElem (l := u) 0 (by omega)]
        exact List.getElem_mem (by omega)
      have hjb := hb _ hjmem
      rw [hlast, hget j (by omega)] at hkj
      omega
  · rintro ⟨i, j, k, hij, hjk, hk, hik, hkj⟩
    refine ⟨i, j, k, hij, hjk, by simp; omega, ?_, ?_⟩
    · simpa only [hget i (by omega), hget k hk] using hik
    · simpa only [hget k hk, hget j (by omega)] using hkj

/-- In an avoided nontrivial final cycle, the last letter strictly dominates
every earlier tail letter, while the earlier tail avoids `132`. -/
theorem final_cycle_strict_max_and_avoid132 (n : ℕ) (q u : List ℕ) (b : ℕ)
    (hp : q ++ (n + 1) :: (u ++ [b]) ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3) :
    (∀ x ∈ u, x < b) ∧ ¬ Has132 u := by
  have hnd : (u ++ [b]).Nodup :=
    ((hp.1.nodup_iff.mpr List.nodup_range').of_append_right).of_cons
  have hbnot : b ∉ u := by
    intro h
    have hlast : b ∈ [b] := by simp
    exact (List.nodup_append'.mp hnd).2.2 h hlast
  have hb : ∀ x ∈ u, x < b := by
    intro x hx
    have hle := final_cycle_last_is_max n q u b hp x hx
    have hne : x ≠ b := by
      intro heq
      exact hbnot (heq ▸ hx)
    omega
  refine ⟨hb, ?_⟩
  have hfull := final_cycle_avoid132 n q (u ++ [b]) hp
  intro h
  exact hfull ((has132_append_max_iff u b hb).mpr h)

/-- The avoiders whose last Foata cycle is the singleton maximum are counted by
the avoiders on the remaining initial interval. -/
theorem singleton_final_cycle_count (n : ℕ) :
    {p : List ℕ | p ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ∧
      p.getLast? = some (n + 1)}.ncard = count n := by
  have hset :
      {p : List ℕ | p ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 ∧
        p.getLast? = some (n + 1)} =
      (fun q : List ℕ => q ++ [n + 1]) '' avoiders n [3, 2] [(1, 3)] 3 := by
    ext p
    constructor
    · rintro ⟨hp, hlast⟩
      have hmem : n + 1 ∈ p.getLast? := by simp [hlast]
      have heq : p.dropLast ++ [n + 1] = p :=
        List.dropLast_append_getLast? (l := p) (n + 1) hmem
      refine ⟨p.dropLast, ?_, heq⟩
      exact (append_max_avoiders_iff n p.dropLast).mp (by simpa [heq] using hp)
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(append_max_avoiders_iff n q).mpr hq, by simp⟩
  rw [hset, count]
  exact Set.ncard_image_of_injective _ (fun _ _ h => List.append_cancel_right h)

/-- Local conditions on the prefix and the last cycle suffice to construct a
global arrow avoider. -/
theorem construct_avoider_of_local_conditions (n : ℕ) (q u : List ℕ) (b : ℕ)
    (hpperm : (q ++ (n + 1) :: (u ++ [b])).Perm (List.range' 1 (n + 1)))
    (hq : ∀ a c : ℕ, a ∈ q → a < c → c < hat q a →
      [c, hat q a].Sublist q)
    (hcross : ∀ a ∈ q, ∀ c ∈ u ++ [b], ¬ (a < c ∧ c < hat q a))
    (hb : ∀ x ∈ u, x < b) (h132 : ¬ Has132 u) :
    q ++ (n + 1) :: (u ++ [b]) ∈ avoiders (n + 1) [3, 2] [(1, 3)] 3 := by
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
  let w := u ++ [b]
  let p := q ++ (n + 1) :: w
  have hnd : p.Nodup := hpperm.nodup_iff.mpr List.nodup_range'
  have hdis := (List.nodup_append'.mp hnd).2.2
  have hm : ∀ y ∈ q, y < n + 1 := by
    intro y hy
    have hrange : y ∈ List.range' 1 (n + 1) := hpperm.mem_iff.mp
      (List.mem_append.mpr (Or.inl hy))
    rcases List.mem_range'.mp hrange with ⟨j, hj, hjy⟩
    have hne : y ≠ n + 1 := by
      intro heq
      exact hdis hy (by simp [heq])
    omega
  have hhatmem (v : List ℕ) (x : ℕ) (hx : x ∈ v) : hat v x ∈ v := by
    change (if v.idxOf x + 1 < v.length ∧ ¬ IsLtrMax v (v.idxOf x + 1)
      then v.getD (v.idxOf x + 1) 0
      else v.getD (Nat.findGreatest (IsLtrMax v) (v.idxOf x)) 0) ∈ v
    split_ifs with hbranch
    · rw [List.getD_eq_getElem (l := v) 0 hbranch.1]
      exact List.getElem_mem hbranch.1
    · have hi : v.idxOf x < v.length := List.idxOf_lt_length_of_mem hx
      have hg := lt_of_le_of_lt
        (Nat.findGreatest_le (P := IsLtrMax v) (v.idxOf x)) hi
      rw [List.getD_eq_getElem (l := v) 0 hg]
      exact List.getElem_mem hg
  have hfinal := final_cycle_edge_condition n q u b hpperm hb
    (fun h => h132 ((has132_append_max_iff u b hb).mp h))
  apply (edgeCriterion (n + 1) p).mpr
  refine ⟨hpperm, ?_⟩
  intro a c ha hac hca
  rcases List.mem_append.mp ha with haq | hatail
  · have hhat : hat p a = hat q a := hat_append_final_cycle q w (n + 1) a hm haq
    rw [hhat] at hca ⊢
    have hbmem : hat q a ∈ q := hhatmem q a haq
    have hc : c ∈ p := by
      have hra := hpperm.mem_iff.mp (List.mem_append.mpr (Or.inl haq))
      have hrb := hpperm.mem_iff.mp (List.mem_append.mpr (Or.inl hbmem))
      have ha1 : 1 ≤ a := List.left_le_of_mem_range' hra
      rcases List.mem_range'.mp hrb with ⟨j, hj, hjb⟩
      apply hpperm.mem_iff.mpr
      apply List.mem_range'.mpr
      refine ⟨c - 1, ?_, ?_⟩ <;> omega
    rcases List.mem_append.mp hc with hcq | hctail
    · exact List.sublist_append_of_sublist_left (hq a c haq hac hca)
    · rcases List.mem_cons.mp hctail with hce | hcw
      · have hbound : hat q a < n + 1 := hm _ hbmem
        omega
      · exact ((hcross a haq c hcw) ⟨hac, hca⟩).elim
  · rcases List.mem_cons.mp hatail with hamax | haw
    · have hmem : hat p a ∈ p := hhatmem p a ha
      have hrange := hpperm.mem_iff.mp hmem
      rcases List.mem_range'.mp hrange with ⟨j, hj, hjy⟩
      omega
    · exact hfinal a haw c hac hca

end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection

#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection.no_prefix_edge_crosses_final_cycle
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection.final_cycle_strict_max_and_avoid132
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection.has132_append_max_iff
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection.construct_avoider_of_local_conditions
