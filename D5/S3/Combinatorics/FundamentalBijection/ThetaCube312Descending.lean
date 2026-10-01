/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Descending
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube312Descending
   mirror-E: none(waiver:extremal-first-avoider-forces-descent)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: A 312-avoider beginning with its maximum is the descending permutation. -/
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
import Mathlib.Data.List.Sort
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Edge
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Descending
local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))
open D5.S3.Combinatorics.ArrowWilfDefs
open ThetaBasicSumIndecomp ThetaBasicSumAvoid ThetaCube312Edge
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
set_option maxHeartbeats 1000000 in
theorem successor_gt_one_absurd (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 3 < p.length)
    (hindecomp : ∀ k, 0 < k → k < p.length →
      ∃ x ∈ p.take k, k < x)
    (havoid : ¬ Contains [3, 1, 2] [] 3 p)
    (hBfixed : B (B (B p)) = p)
    (hsuccessor : 1 < p.getD (p.idxOf p.length + 1) 0) : False := by
  have avoid312_first_max_descending (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
      (hfirst : p.getD 0 0 = p.length)
      (havoid : ¬ D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p) :
      p = (List.range' 1 p.length).reverse := by
    have hcontains312 (p : List ℕ) :
        D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p ↔
          ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] > p[k.val] ∧
          p[k.val] > p[j.val] := by
      constructor
      · rintro ⟨x, hlt, _, hsub, _⟩
        change List.Sublist [x 3, x 1, x 2] p at hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        have h0 : p[(f ⟨0, by simp⟩).val] = x 3 := by
          simpa using (hf ⟨0, by simp⟩).symm
        have h1 : p[(f ⟨1, by simp⟩).val] = x 1 := by
          simpa using (hf ⟨1, by simp⟩).symm
        have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
          simpa using (hf ⟨2, by simp⟩).symm
        refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
          f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
        · simpa only [← h0, ← h2] using hlt 2 (by omega) (by omega)
        · simpa only [← h2, ← h1] using hlt 1 (by omega) (by omega)
      · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
        let x : ℕ → ℕ := fun t => if t = 1 then p[j.val] else if t = 2 then p[k.val]
          else p[i.val]
        have hx1 : x 1 = p[j.val] := by simp [x]
        have hx2 : x 2 = p[k.val] := by simp [x]
        have hx3 : x 3 = p[i.val] := by simp [x]
        have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
          let f : Fin 3 → Fin p.length := fun t =>
            if t.val = 0 then i else if t.val = 1 then j else k
          have hf : StrictMono f := by
            intro a b hab
            fin_cases a <;> fin_cases b <;> simp_all [f]; omega
          apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
          refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
          intro t
          fin_cases t <;> simp [f]
        refine ⟨x, ?_, ?_, ?_, by simp⟩
        · intro t ht ht3
          have h : t = 1 ∨ t = 2 := by omega
          rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hkj, hik]
        · intro t ht ht3
          have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
          rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
        · simpa [hx1, hx2, hx3] using hsub
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hbound (i : ℕ) (hi : i < p.length) : p[i] ≤ p.length := by
      have hmem : p[i] ∈ p := List.getElem_mem hi
      obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
      omega
    have hfirst' : p[0] = p.length := by
      simpa only [List.getD_eq_getElem _ 0 hn] using hfirst
    have hstrict (i : ℕ) (hi : 0 < i) (hil : i < p.length) : p[i] < p.length := by
      have hne : p[i] ≠ p[0] := by
        intro heq
        have := (hnodup.getElem_inj_iff).mp heq
        omega
      rw [hfirst'] at hne
      have := hbound i hil
      omega
    have hsorted : p.SortedGT := by
      apply List.sortedGT_iff_getElem_gt_getElem_of_lt.mpr
      intro i j hi hj hji
      by_cases hj0 : j = 0
      · subst j
        rw [hfirst']
        exact hstrict i (by omega) hi
      · have hjpos : 0 < j := by omega
        have hne : p[j] ≠ p[i] := by
          intro heq
          have := (hnodup.getElem_inj_iff).mp heq
          omega
        by_contra hnot
        have hmiddle : p[j] < p[i] := by omega
        apply havoid
        apply (hcontains312 p).mpr
        refine ⟨⟨0, hn⟩, ⟨j, hj⟩, ⟨i, hi⟩, ?_, ?_, ?_, ?_⟩
        · exact hjpos
        · exact hji
        · rw [hfirst']
          exact hstrict i (by omega) hi
        · exact hmiddle
    have hrange : (List.range' 1 p.length).SortedLT :=
      List.sortedLT_range' 1 p.length (s := 1) (by decide)
    exact List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT
      (fun a => hp.mem_iff) hsorted hrange
  have hat_one_block (p : List ℕ) (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
      (x : ℕ) (hx : x ∈ p) :
      hat p x = if p.idxOf x + 1 < p.length then p.getD (p.idxOf x + 1) 0
        else p.getD 0 0 := by
    have hnonrecord (i : ℕ) (hi : 0 < i) (hil : i < p.length) :
        ¬ IsLtrMax p i := by
      intro hrecord
      have hmem : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hil]
        exact List.getElem_mem hil
      exact (not_lt_of_ge (hmax _ hmem)) (hrecord 0 hi)
    have hgreatest (i : ℕ) (hi : i < p.length) :
        Nat.findGreatest (IsLtrMax p) i = 0 := by
      induction i with
      | zero => rfl
      | succ j ih =>
          rw [Nat.findGreatest_succ, if_neg (hnonrecord (j + 1) (by omega) hi)]
          exact ih (by omega)
    have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
    unfold hat
    dsimp only
    by_cases hnext : p.idxOf x + 1 < p.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun h => hnext h.1), if_neg hnext, hgreatest _ hidx]
  have last_one_forces_B_first_max (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
      (hlast : p.getD (p.length - 1) 0 = 1) :
      (B p).getD 0 0 = p.length := by
    have hat_record_block_edges (p : List ℕ) (hp : p.Nodup)
        (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
        (hs : IsLtrMax p s)
        (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
        (hboundary : e = p.length ∨ IsLtrMax p e) :
        (∀ i, s ≤ i → i + 1 < e →
          hat p (p.getD i 0) = p.getD (i + 1) 0) ∧
        hat p (p.getD (e - 1) 0) = p.getD s 0 := by
      have hidx (i : ℕ) (hi : i < p.length) : p.idxOf (p.getD i 0) = i := by
        rw [List.getD_eq_getElem _ 0 hi]
        simpa using (List.get_idxOf hp ⟨i, hi⟩)
      have hstart : s ≤ Nat.findGreatest (IsLtrMax p) (e - 1) :=
        Nat.le_findGreatest (by omega) hs
      have hend : Nat.findGreatest (IsLtrMax p) (e - 1) ≤ e - 1 :=
        Nat.findGreatest_le _
      have hgreatest : Nat.findGreatest (IsLtrMax p) (e - 1) = s := by
        by_contra hne
        have hgt : s < Nat.findGreatest (IsLtrMax p) (e - 1) := by omega
        exact hnon _ hgt (by omega)
          (Nat.findGreatest_spec (Nat.le_sub_one_of_lt hse) hs)
      constructor
      · intro i hsi hie
        have hi : i < p.length := by omega
        have hnext : i + 1 < p.length := by omega
        have hnr : ¬ IsLtrMax p (i + 1) := hnon _ (by omega) hie
        unfold hat
        rw [hidx i hi, if_pos ⟨hnext, hnr⟩]
      · have hlast : e - 1 < p.length := by omega
        have hbranch : ¬ (e - 1 + 1 < p.length ∧ ¬ IsLtrMax p (e - 1 + 1)) := by
          rcases hboundary with h | h
          · intro h'; omega
          · intro h'; exact h'.2 (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ e)] using h)
        unfold hat
        rw [hidx _ hlast, if_neg hbranch, hgreatest]
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have h1mem : 1 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨0, hn, by omega⟩)
    have hnmem : p.length ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨p.length - 1, by omega, by omega⟩)
    have hidx1 : p.idxOf 1 = p.length - 1 := by
      have hh := hnodup.idxOf_getElem (i := p.length - 1) (by omega)
      have hv : p[p.length - 1] = 1 := by
        rw [← List.getD_eq_getElem _ 0 (by omega), hlast]
      rw [hv] at hh
      exact hh
    have hidxn : p.idxOf p.length < p.length :=
      List.idxOf_lt_length_of_mem hnmem
    have hvaln : p.getD (p.idxOf p.length) 0 = p.length := by
      rw [List.getD_eq_getElem _ 0 hidxn]
      exact List.getElem_idxOf hidxn
    have hbound (j : ℕ) (hj : j < p.length) : p.getD j 0 ≤ p.length := by
      have hm : p.getD j 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hj]
        exact List.getElem_mem hj
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
      omega
    have hrecn : D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (p.idxOf p.length) := by
      intro j hj
      have hjlt : j < p.length := by omega
      have hne : p.getD j 0 ≠ p.length := by
        intro he
        have hi : p[j] = p[p.idxOf p.length] := by
          rw [← List.getD_eq_getElem _ 0 hjlt,
            ← List.getD_eq_getElem _ 0 hidxn, he, hvaln]
        exact (by omega : j ≠ p.idxOf p.length)
          ((hnodup.getElem_inj_iff).mp hi)
      rw [hvaln]
      have hle := hbound j hjlt
      omega
    have hnon (j : ℕ) (hj : p.idxOf p.length < j) (hjlt : j < p.length) :
        ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p j := by
      intro hrec
      have hh := hrec (p.idxOf p.length) hj
      rw [hvaln] at hh
      have hle := hbound j hjlt
      omega
    have hclose := (hat_record_block_edges p hnodup
      (p.idxOf p.length) p.length (by omega) (le_refl _) hrecn hnon
      (Or.inl rfl)).2
    rw [show p.length - 1 = p.length - 1 by rfl, hlast, hvaln] at hclose
    have hB : (B p).getD 0 0 =
        D5.S3.Combinatorics.ArrowWilfDefs.hat p 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simp
    exact hB.trans hclose
  have B_recordStaircase (n : ℕ) (hn : 1 < n) :
      B (List.range' 2 (n - 1) ++ [1]) =
        n :: (List.range' 2 (n - 2) ++ [1]) := by
    let p := List.range' 2 (n - 1) ++ [1]
    have hlen : p.length = n := by simp [p]; omega
    have hget (i : ℕ) (hi : i < n) :
        p.getD i 0 = if i < n - 1 then i + 2 else 1 := by
      rw [List.getD_eq_getElem _ 0 (by simpa [hlen] using hi)]
      change (List.range' 2 (n - 1) ++ [1])[i] = _
      rw [List.getElem_append]
      by_cases hfirst : i < n - 1
      · simp [hfirst]
        omega
      · have hieq : i = n - 1 := by omega
        simp [hfirst, hieq]
    have hnot : 1 ∉ List.range' 2 (n - 1) := by
      intro h
      obtain ⟨j, _, heq⟩ := List.mem_range'.mp h
      omega
    have hnodup : p.Nodup := by
      apply List.nodup_append.mpr
      refine ⟨List.nodup_range', by simp, ?_⟩
      intro x hx y hy heq
      simp only [List.mem_singleton] at hy
      have hxone : x = 1 := heq.trans hy
      exact hnot (hxone ▸ hx)
    have hrecord (i : ℕ) (hi : i < n - 1) :
        D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p i := by
      intro j hj
      rw [hget j (by omega), hget i (by omega)]
      simp only [if_pos (by omega : j < n - 1), if_pos hi]
      omega
    have hlastNot :
        ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (n - 1) := by
      intro hr
      have h := hr 0 (by omega : 0 < n - 1)
      rw [hget 0 (by omega), hget (n - 1) (by omega)] at h
      simp [hn] at h
    have hfgLast : Nat.findGreatest
        (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (n - 1) = n - 2 := by
      have hlo := Nat.le_findGreatest (by omega : n - 2 ≤ n - 1)
        (hrecord (n - 2) (by omega))
      have hhi := Nat.findGreatest_le
        (P := D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (n - 1)
      by_contra hne
      have heq : Nat.findGreatest
          (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (n - 1) = n - 1 := by
        omega
      apply hlastNot
      rw [← heq]
      exact Nat.findGreatest_spec (by omega : n - 2 ≤ n - 1)
        (hrecord (n - 2) (by omega))
    apply List.ext_getElem
    · simp [p]
      omega
    · intro i hi hi'
      have hin : i < n := by
        have h := hi
        simp at h
        omega
      have hmem : i + 1 ∈ p := by
        by_cases hz : i = 0
        · subst i
          simp [p]
        · have hr : i + 1 ∈ List.range' 2 (n - 1) :=
            List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩
          simp [p, hr]
      have hidx : p.idxOf (i + 1) = if i = 0 then n - 1 else i - 1 := by
        by_cases hz : i = 0
        · subst i
          rw [if_pos rfl]
          have hpos : n - 1 < p.length := by omega
          have hval : p[n - 1] = 1 := by
            rw [← List.getD_eq_getElem _ 0 hpos, hget (n - 1) (by omega)]
            simp
          have h := hnodup.idxOf_getElem (i := n - 1) hpos
          rw [hval] at h
          simpa using h
        · rw [if_neg hz]
          have hpos : i - 1 < p.length := by omega
          have hval : p[i - 1] = i + 1 := by
            rw [← List.getD_eq_getElem _ 0 hpos, hget (i - 1) (by omega)]
            have : i - 1 < n - 1 := by omega
            simp [this]
            omega
          have h := hnodup.idxOf_getElem (i := i - 1) hpos
          rw [hval] at h
          exact h
      have hleft : (B p)[i] = D5.S3.Combinatorics.ArrowWilfDefs.hat p (i + 1) := by
        simp [Nat.add_comm]
      have hright : (n :: (List.range' 2 (n - 2) ++ [1]))[i] =
          if i = 0 then n else if i + 1 = n then 1 else i + 1 := by
        cases i with
        | zero => simp
        | succ j =>
          simp only [List.getElem_cons_succ]
          rw [List.getElem_append]
          by_cases hlast : j + 2 = n
          · have hieq : j = n - 2 := by omega
            simp [hieq]
            omega
          · have hlt : j < n - 2 := by omega
            have hnot : 1 + (j + 1) ≠ n := by omega
            simp [hlt, hnot, Nat.add_comm, Nat.add_assoc]
            omega
      change (B p)[i] = (n :: (List.range' 2 (n - 2) ++ [1]))[i]
      rw [hleft, hright]
      unfold D5.S3.Combinatorics.ArrowWilfDefs.hat
      rw [hidx]
      by_cases hz : i = 0
      · subst i
        have hnlt : ¬ n - 1 + 1 < p.length := by omega
        simp only [Nat.zero_add, ite_true]
        have hncondition : ¬ (n - 1 + 1 < p.length ∧
            ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (n - 1 + 1)) :=
          fun h => hnlt h.1
        rw [if_neg hncondition, hfgLast, hget (n - 2) (by omega)]
        simp [show n - 2 < n - 1 by omega]
        omega
      · simp only [if_neg hz]
        by_cases hlast : i + 1 = n
        · have hieq : i = n - 1 := by omega
          have hnext : i - 1 + 1 < p.length := by omega
          have hnrec : ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p
              (i - 1 + 1) := by simpa [hieq, show n - 1 - 1 + 1 = n - 1 by omega]
              using hlastNot
          rw [if_pos ⟨hnext, hnrec⟩, hget (i - 1 + 1) (by omega)]
          have hval : i - 1 + 1 = n - 1 := by omega
          simp [hval, hlast]
        · have hnext : i - 1 + 1 < p.length := by omega
          have hrec : D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p
              (i - 1 + 1) := by
            apply hrecord
            omega
          rw [if_neg (by simp [hrec]), Nat.findGreatest_eq
            (hrecord (i - 1) (by omega)), hget (i - 1) (by omega)]
          simp [hlast, show i - 1 < n - 1 by omega]
          omega
  have hat_record_block_edges (p : List ℕ) (hp : p.Nodup)
      (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
      (hs : IsLtrMax p s)
      (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
      (hboundary : e = p.length ∨ IsLtrMax p e) :
      (∀ i, s ≤ i → i + 1 < e →
        hat p (p.getD i 0) = p.getD (i + 1) 0) ∧
      hat p (p.getD (e - 1) 0) = p.getD s 0 := by
    have hidx (i : ℕ) (hi : i < p.length) : p.idxOf (p.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 hi]
      simpa using (List.get_idxOf hp ⟨i, hi⟩)
    have hstart : s ≤ Nat.findGreatest (IsLtrMax p) (e - 1) :=
      Nat.le_findGreatest (by omega) hs
    have hend : Nat.findGreatest (IsLtrMax p) (e - 1) ≤ e - 1 :=
      Nat.findGreatest_le _
    have hgreatest : Nat.findGreatest (IsLtrMax p) (e - 1) = s := by
      by_contra hne
      have hgt : s < Nat.findGreatest (IsLtrMax p) (e - 1) := by omega
      exact hnon _ hgt (by omega)
        (Nat.findGreatest_spec (Nat.le_sub_one_of_lt hse) hs)
    constructor
    · intro i hsi hie
      have hi : i < p.length := by omega
      have hnext : i + 1 < p.length := by omega
      have hnr : ¬ IsLtrMax p (i + 1) := hnon _ (by omega) hie
      unfold hat
      rw [hidx i hi, if_pos ⟨hnext, hnr⟩]
    · have hlast : e - 1 < p.length := by omega
      have hbranch : ¬ (e - 1 + 1 < p.length ∧ ¬ IsLtrMax p (e - 1 + 1)) := by
        rcases hboundary with h | h
        · intro h'; omega
        · intro h'; exact h'.2 (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ e)] using h)
      unfold hat
      rw [hidx _ hlast, if_neg hbranch, hgreatest]
  have B_descending (n : ℕ) (hn : 0 < n) :
      B ((List.range' 1 n).reverse) = n :: List.range' 1 (n - 1) := by
    let p := (List.range' 1 n).reverse
    have hlen : p.length = n := by simp [p]
    have hget (i : ℕ) (hi : i < n) : p.getD i 0 = n - i := by
      rw [List.getD_eq_getElem _ 0 (by simpa [p] using hi)]
      change (List.range' 1 n).reverse[i] = n - i
      rw [List.getElem_reverse]
      simp only [List.length_range']
      rw [List.getElem_range'_1]
      omega
    have hmax : ∀ y ∈ p, y ≤ p.getD 0 0 := by
      intro y hy
      have hy' : y ∈ List.range' 1 n := by simpa [p] using hy
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp hy'
      rw [hget 0 hn]
      omega
    have hnodup : p.Nodup := by
      exact List.nodup_reverse.mpr (show (List.range' 1 n).Nodup from List.nodup_range')
    apply List.ext_getElem
    · simp [p]
      omega
    · intro i hi hi'
      have hin : i < n := by simpa [hlen] using hi
      have hidxval : p.getD (n - (i + 1)) 0 = i + 1 := by
        apply (hget (n - (i + 1)) (by omega)).trans
        omega
      have hidx : p.idxOf (i + 1) = n - (i + 1) := by
        have hpos : n - (i + 1) < p.length := by omega
        have hval : p[n - (i + 1)] = i + 1 := by
          simpa only [List.getD_eq_getElem _ 0 hpos] using hidxval
        have h := hnodup.idxOf_getElem (i := n - (i + 1)) hpos
        rw [hval] at h
        exact h
      have hmem : i + 1 ∈ p := by
        have hr : i + 1 ∈ List.range' 1 n :=
          List.mem_range'.mpr ⟨i, hin, by omega⟩
        simpa [p] using hr
      have hleft : (B p)[i] = D5.S3.Combinatorics.ArrowWilfDefs.hat p (i + 1) := by
        simp [Nat.add_comm]
      have hright : (n :: List.range' 1 (n - 1))[i] =
          if i = 0 then n else i := by
        cases i with
        | zero => simp
        | succ j => simp [Nat.add_comm]
      change (B p)[i] = (n :: List.range' 1 (n - 1))[i]
      rw [hleft, hright, hat_one_block p hmax (i + 1) hmem, hidx]
      by_cases hz : i = 0
      · subst i
        have hlast : n - 1 + 1 = n := by omega
        rw [hlast, if_neg (by omega : ¬ n < p.length), if_pos rfl]
        exact hget 0 hn
      · have hnext : n - (i + 1) + 1 < p.length := by omega
        rw [if_pos hnext, if_neg hz]
        have harg : n - (i + 1) + 1 = n - i := by omega
        rw [harg, hget (n - i) (by omega)]
        omega
  have B_perm (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (B p).Perm (List.range' 1 p.length) := by
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hmem (x : ℕ) (hx : x ∈ p) : hat p x ∈ p := by
      have hi : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      unfold hat
      dsimp only
      split_ifs with h
      · rw [List.getD_eq_getElem _ 0 h.1]
        exact List.getElem_mem h.1
      · have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf x) < p.length :=
          lt_of_le_of_lt (Nat.findGreatest_le _) hi
        rw [List.getD_eq_getElem _ 0 hg]
        exact List.getElem_mem hg
    have hmapNodup : (p.map (hat p)).Nodup := hnodup.map_on (hat_inj_on p hnodup)
    have hsubset : (p.map (hat p)).toFinset ⊆ p.toFinset := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr (hmem a ha)
    have hcard : (p.map (hat p)).toFinset.card = p.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapNodup,
        List.dedup_eq_self.mpr hnodup]
    have heq : (p.map (hat p)).toFinset = p.toFinset :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hperm : (p.map (hat p)).Perm p :=
      List.perm_of_nodup_nodup_toFinset_eq hmapNodup hnodup heq
    exact ((hp.symm.map _).trans hperm).trans hp
  have B_successorWord (n : ℕ) (hn : 1 < n) :
      B (n :: List.range' 1 (n - 1)) = List.range' 2 (n - 1) ++ [1] := by
    let p := n :: List.range' 1 (n - 1)
    have hlen : p.length = n := by simp [p]; omega
    have hget (i : ℕ) (hi : i < n) : p.getD i 0 = if i = 0 then n else i := by
      cases i with
      | zero => simp [p]
      | succ j =>
          have hj : j < n - 1 := by omega
          rw [List.getD_eq_getElem _ 0 (by simpa [hlen] using hi)]
          simp [p, List.getElem_range'_1, Nat.add_comm]
    have hmax : ∀ y ∈ p, y ≤ p.getD 0 0 := by
      intro y hy
      have hzero : p.getD 0 0 = n := by simpa using hget 0 (by omega)
      rw [hzero]
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · obtain ⟨a, ha, heq⟩ := List.mem_range'.mp hy
        omega
    have hnodup : p.Nodup := by
      have hnnot : n ∉ List.range' 1 (n - 1) := by
        intro h
        obtain ⟨a, ha, heq⟩ := List.mem_range'.mp h
        omega
      exact List.nodup_cons.mpr ⟨hnnot, List.nodup_range'⟩
    apply List.ext_getElem
    · simp [p]
    · intro i hi hi'
      have hin : i < n := by
        have h := hi
        simp at h
        omega
      have hmem : i + 1 ∈ p := by
        by_cases hlast : i + 1 = n
        · simp [p, hlast]
        · have hr : i + 1 ∈ List.range' 1 (n - 1) :=
            List.mem_range'.mpr ⟨i, by omega, by omega⟩
          simp [p, hr]
      have hidx : p.idxOf (i + 1) = if i + 1 = n then 0 else i + 1 := by
        by_cases hlast : i + 1 = n
        · rw [if_pos hlast]
          have hval : p[0] = i + 1 := by simp [p, hlast]
          have h := hnodup.idxOf_getElem (i := 0) (by simp [p])
          rw [hval] at h
          exact h
        · rw [if_neg hlast]
          have hpos : i + 1 < p.length := by omega
          have hval : p[i + 1] = i + 1 := by
            rw [← List.getD_eq_getElem _ 0 hpos, hget (i + 1) (by omega)]
            simp [hlast]
          have h := hnodup.idxOf_getElem (i := i + 1) hpos
          rw [hval] at h
          exact h
      have hleft : (B p)[i] = D5.S3.Combinatorics.ArrowWilfDefs.hat p (i + 1) := by
        simp [Nat.add_comm]
      have hright : (List.range' 2 (n - 1) ++ [1])[i] =
          if i + 1 = n then 1 else i + 2 := by
        rw [List.getElem_append]
        by_cases hlast : i + 1 = n
        · have hieq : i = n - 1 := by omega
          simp [hieq]
          omega
        · have hlt : i < n - 1 := by omega
          simp [hlt, hlast]
          omega
      change (B p)[i] = (List.range' 2 (n - 1) ++ [1])[i]
      rw [hleft, hright, hat_one_block p hmax (i + 1) hmem, hidx]
      by_cases hlast : i + 1 = n
      · simp only [if_pos hlast]
        have hnext : 1 < p.length := by omega
        simp [hnext, hget 1 (by omega)]
        simp [p]
      · simp only [if_neg hlast]
        have hnext : i + 1 + 1 < p.length ∨ i + 1 + 1 = p.length := by omega
        rcases hnext with hnext | hnext
        · rw [if_pos hnext, hget (i + 2) (by omega)]
          simp
        · rw [if_neg (by omega : ¬ i + 1 + 1 < p.length), hget 0 (by omega)]
          simp
          omega
  have predecessor_of_one (q : List ℕ)
      (hq : q.Perm (List.range' 1 q.length))
      (hmax : ∀ y ∈ q, y ≤ q.getD 0 0)
      (b c : ℕ) (hb : b < q.length) (hc : 0 < c ∧ c < q.length)
      (hqc : q.getD c 0 = 1) (hrb : (B q).getD b 0 = 1) :
      q.getD (c - 1) 0 = b + 1  := by
    have one_block_predecessor (p : List ℕ)
        (hp : p.Perm (List.range' 1 p.length))
        (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
        (x y c : ℕ) (hx : x ∈ p)
        (hc : 0 < c ∧ c < p.length)
        (hy : p.getD c 0 = y)
        (hedge : D5.S3.Combinatorics.ArrowWilfDefs.hat p x = y) :
        p.getD (c - 1) 0 = x := by
      have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
      have hix : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      have hvalx : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hix]
        exact List.getElem_idxOf hix
      have hh := hat_one_block p hmax x hx
      rw [hedge] at hh
      have hnext : p.idxOf x + 1 < p.length := by
        by_contra hnot
        rw [if_neg (by omega : ¬ p.idxOf x + 1 < p.length)] at hh
        have helem : p[0] = p[c] := by
          rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length),
            ← List.getD_eq_getElem _ 0 hc.2]
          exact hh.symm.trans hy.symm
        exact (by omega : 0 ≠ c) ((hnodup.getElem_inj_iff).mp helem)
      rw [if_pos hnext] at hh
      have hidx : p.idxOf x + 1 = c := by
        have helem : p[p.idxOf x + 1] = p[c] := by
          rw [← List.getD_eq_getElem _ 0 hnext,
            ← List.getD_eq_getElem _ 0 hc.2]
          exact hh.symm.trans hy.symm
        exact (hnodup.getElem_inj_iff).mp helem
      have heq : c - 1 = p.idxOf x := by omega
      rw [heq]
      exact hvalx
    have hx : b + 1 ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨b, hb, by omega⟩)
    have hedge : D5.S3.Combinatorics.ArrowWilfDefs.hat q (b + 1) = 1 := by
      rw [List.getD_eq_getElem _ 0 (by simpa using hb)] at hrb
      simpa [Nat.add_comm] using hrb
    exact one_block_predecessor q hq hmax (b + 1) 1 c hx hc hqc hedge
  have B_getD_hat (p : List ℕ) (x : ℕ) (hx : 0 < x)
      (hxle : x ≤ p.length) :
      (B p).getD (x - 1) 0 = hat p x := by
    have hi : x - 1 < (B p).length := by simp; omega
    rw [List.getD_eq_getElem _ 0 hi]
    simp only [List.getElem_map, List.getElem_range'_1]
    congr 1
    omega
  have one_block_B_at (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
      (x : ℕ) (hx : x ∈ p) (i : ℕ) (hi : i < p.length)
      (hidx : p.idxOf x = i) :
      (B p).getD (x - 1) 0 =
        if i + 1 < p.length then p.getD (i + 1) 0 else p.getD 0 0 := by
    rw [B_getD_hat p x (by
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hx)
      omega) (by
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hx)
      omega)]
    rw [hat_one_block p hmax x hx, hidx]
  have B_first_of_final_max_one (r : List ℕ)
      (hr : r.Perm (List.range' 1 r.length)) (hn : 2 < r.length)
      (hmax : r.getD (r.length - 2) 0 = r.length)
      (hone : r.getD (r.length - 1) 0 = 1) :
      (B r).getD 0 0 = r.length := by
    exact last_one_forces_B_first_max r hr (by omega) hone
  let n := p.length
  let q := B p
  let r := B q
  have hn0 : 0 < n := by dsimp [n]; omega
  have hlast : p.getD (n - 1) 0 = 1 :=
    (avoid312_indecomp_iff_last_one p hp (by omega) havoid).mp hindecomp
  have hqfirst : q.getD 0 0 = n :=
    last_one_forces_B_first_max p hp (by omega) hlast
  have hqperm : q.Perm (List.range' 1 n) := by
    dsimp [q, n]
    exact B_perm p hp
  have hrperm : r.Perm (List.range' 1 n) := by
    dsimp [r]
    have hqlen : q.length = n := by simp [q, n]
    have hqperm' : q.Perm (List.range' 1 q.length) := by
      rw [hqlen]
      exact hqperm
    have htmp := B_perm q hqperm'
    simpa [q, n, hqlen] using htmp
  have hpr : B r = p := by simpa [r, q] using hBfixed
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hqnodup : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
  have hrnodup : r.Nodup := hrperm.nodup_iff.mpr List.nodup_range'
  have h1mem : 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, hn0, by omega⟩)
  have hnmem : n ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  let tn := p.idxOf n
  have htn : tn < n := by
    dsimp [tn]
    exact List.idxOf_lt_length_of_mem hnmem
  have htnlast : tn < n - 1 := by
    by_contra h
    have heq : tn = n - 1 := by omega
    have hv : p.getD tn 0 = n := by
      rw [List.getD_eq_getElem _ 0 htn]
      exact List.getElem_idxOf htn
    rw [heq, hlast] at hv
    omega
  have hrecn : IsLtrMax p tn := by
    intro j hj
    have hjlt : j < n := by omega
    have hmem : p.getD j 0 ∈ p := by
      rw [List.getD_eq_getElem _ 0 hjlt]
      exact List.getElem_mem hjlt
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
    have hneq : p.getD j 0 ≠ n := by
      intro he
      have hv : p.getD tn 0 = n := by
        rw [List.getD_eq_getElem _ 0 htn]
        exact List.getElem_idxOf htn
      have helem : p[j] = p[tn] := by
        rw [← List.getD_eq_getElem _ 0 hjlt,
          ← List.getD_eq_getElem _ 0 htn, he, hv]
      exact (by omega : j ≠ tn) ((hpnodup.getElem_inj_iff).mp helem)
    have hnv : p.getD tn 0 = n := by
      rw [List.getD_eq_getElem _ 0 htn]
      exact List.getElem_idxOf htn
    rw [hnv]
    omega
  have hnon_after (j : ℕ) (hj : tn < j) (hjlt : j < n) :
      ¬ IsLtrMax p j := by
    intro hjrec
    have hval : p.getD j 0 < n := by
      have hmem : p.getD j 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hjlt]
        exact List.getElem_mem hjlt
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
      have hne : p.getD j 0 ≠ n := by
        intro he
        have hnv : p.getD tn 0 = n := by
          rw [List.getD_eq_getElem _ 0 htn]
          exact List.getElem_idxOf htn
        have helem : p[j] = p[tn] := by
          rw [← List.getD_eq_getElem _ 0 hjlt,
            ← List.getD_eq_getElem _ 0 htn, he, hnv]
        exact (by omega : j ≠ tn) ((hpnodup.getElem_inj_iff).mp helem)
      omega
    have hprior := hjrec tn hj
    have hnv : p.getD tn 0 = n := by
      rw [List.getD_eq_getElem _ 0 htn]
      exact List.getElem_idxOf htn
    rw [hnv] at hprior
    omega
  have hnextn : tn + 1 < n := by omega
  have hq_n : q.getD (n - 1) 0 = p.getD (tn + 1) 0 := by
    have hedges := hat_record_block_edges p hpnodup tn n (by omega) (by rfl)
      hrecn hnon_after (Or.inl rfl)
    have h := hedges.1 tn (by omega) hnextn
    have hnv : p.getD tn 0 = n := by
      rw [List.getD_eq_getElem _ 0 htn]
      exact List.getElem_idxOf htn
    change (B p).getD (n - 1) 0 = p.getD (tn + 1) 0
    rw [B_getD_hat p n (by omega) (by omega)]
    rw [hnv] at h
    exact h
  have hq_n' : q.getD (n - 1) 0 = p.getD (tn + 1) 0 := hq_n
  let b := p.getD (tn + 1) 0
  have hq_last : q.getD (n - 1) 0 = b := by simpa [b] using hq_n'
  let hc : ℕ := p.getD (n - 2) 0
  have hq_c : q.getD (hc - 1) 0 = 1 := by
    have hedges := hat_record_block_edges p hpnodup tn n (by omega) (by rfl)
      hrecn hnon_after (Or.inl rfl)
    have h := hedges.1 (n - 2) (by omega) (by omega)
    have hcv : hc = p.getD (n - 2) 0 := by rfl
    have hmemc : hc ∈ p := by
      rw [hcv, List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by omega)
    have hidxc : hc - 1 < n := by
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hmemc)
      have hna : a < n := by simpa [n] using ha
      omega
    have hcp : 0 < hc := by
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hmemc)
      omega
    rw [B_getD_hat p hc hcp (by omega)]
    rw [← hcv] at h
    have hidx : n - 2 + 1 = n - 1 := by omega
    rw [hidx, hlast] at h
    exact h
  have hbmem : b ∈ p := by
    rw [show b = p.getD (tn + 1) 0 by rfl,
      List.getD_eq_getElem _ 0 (by omega)]
    exact List.getElem_mem (by omega)
  have hbpos : 0 < b := by
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hbmem)
    omega
  have hble : b ≤ n := by
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hbmem)
    omega
  have hbn : b < n := by
    by_contra hnot
    have heq : b = n := by omega
    have hval : p.getD (tn + 1) 0 = n := by simpa [b, heq]
    have hnv : p.getD tn 0 = n := by
      rw [List.getD_eq_getElem _ 0 htn]
      exact List.getElem_idxOf htn
    have helem : p[tn + 1] = p[tn] := by
      rw [← List.getD_eq_getElem _ 0 (by omega),
        ← List.getD_eq_getElem _ 0 htn, hval, hnv]
    exact (by omega : tn + 1 ≠ tn) ((hpnodup.getElem_inj_iff).mp helem)
  have hcmem : hc ∈ p := by
    rw [show hc = p.getD (n - 2) 0 by rfl,
      List.getD_eq_getElem _ 0 (by omega)]
    exact List.getElem_mem (by omega)
  have hcpos : 0 < hc := by
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hcmem)
    omega
  have hcle : hc ≤ n := by
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hcmem)
    omega
  have hcneone : hc ≠ 1 := by
    intro heq
    have hv : p.getD (n - 2) 0 = 1 := by simpa [hc] using heq
    exact (by
      have hlastidx : n - 1 < n := by omega
      have hne : p[n - 2] ≠ p[n - 1] := by
        intro hval
        exact (by omega : n - 2 ≠ n - 1) ((hpnodup.getElem_inj_iff).mp hval)
      apply hne
      rw [← List.getD_eq_getElem _ 0 (by omega),
        ← List.getD_eq_getElem _ 0 hlastidx, hv, hlast])
  have hqmax : ∀ y ∈ q, y ≤ q.getD 0 0 := by
    intro y hy
    rw [hqfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hqperm.mem_iff.mp hy)
    omega
  have hbqmem : b ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨b - 1, by omega, by omega⟩)
  have hqidxb : q.idxOf b = n - 1 := by
    have hpos : n - 1 < q.length := by simp [q, n]; omega
    have hval : q[n - 1] = b := by simpa only [List.getD_eq_getElem _ 0 hpos] using hq_last
    have hi := hqnodup.idxOf_getElem (i := n - 1) hpos
    rw [hval] at hi
    exact hi
  have hr_blast : r.getD (b - 1) 0 = n := by
    have hqlen : q.length = n := by simp [q, n]
    have hqperm' : q.Perm (List.range' 1 q.length) := by
      rw [hqlen]
      exact hqperm
    have h := one_block_B_at q hqperm' hqmax b hbqmem (n - 1)
      (by simp [q, n]; omega) hqidxb
    have hnend : ¬ n - 1 + 1 < q.length := by simp [q, n]; omega
    rw [if_neg hnend, hqfirst] at h
    simpa [r] using h
  have hridxn : r.idxOf n = b - 1 := by
    rw [← hr_blast, List.getD_eq_getElem _ 0 (by simp [r, q, n]; omega)]
    exact hrnodup.idxOf_getElem (i := b - 1) (by simp [r, q, n]; omega)
  have hhat_r_n : hat r n = 1 := by
    have hlastpr := congrArg (fun l : List ℕ => l.getD (n - 1) 0) hpr
    have hlastpr' : (B r).getD (n - 1) 0 = 1 := by
      rw [hlast] at hlastpr
      exact hlastpr
    exact (B_getD_hat r n (by omega) (by simp [r, q, n])).symm.trans hlastpr'
  have hr_b : r.getD b 0 = 1 := by
    have hnext : (b - 1) + 1 < r.length := by
      simp [r, q, n]
      omega
    have hrec : ¬ IsLtrMax r ((b - 1) + 1) := by
      intro hrec
      have hgt := hrec (b - 1) (by omega)
      rw [hr_blast] at hgt
      have hmem : r.getD ((b - 1) + 1) 0 ∈ r := by
        rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_mem (by omega)
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hmem)
      omega
    unfold hat at hhat_r_n
    rw [hridxn, if_pos ⟨hnext, hrec⟩] at hhat_r_n
    simpa only [show (b - 1) + 1 = b by omega] using hhat_r_n
  have hqp : q.getD (hc - 2) 0 = b + 1 := by
    have hq_c' : q.getD (hc - 1) 0 = 1 := hq_c
    have hq_cidx : 0 < hc - 1 ∧ hc - 1 < q.length := by
      simp [q, n]
      omega
    have hqlen : q.length = n := by simp [q, n]
    have hqperm' : q.Perm (List.range' 1 q.length) := by
      rw [hqlen]
      exact hqperm
    have h := predecessor_of_one q hqperm' hqmax b (hc - 1)
      (by omega) hq_cidx hq_c' (by
        simpa [r, show b < q.length by simp [q, n]; omega] using hr_b)
    simpa only [show hc - 1 - 1 = hc - 2 by omega] using h
  have hxmemp : hc - 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨hc - 2, by omega, by omega⟩)
  have hhatx : hat p (hc - 1) = b + 1 := by
    have hmap := B_getD_hat p (hc - 1) (by omega) (by omega)
    change (B p).getD (hc - 2) 0 = hat p (hc - 1) at hmap
    rw [← hmap]
    exact hqp
  have hbgt : 1 < b := hsuccessor
  have hb1 : b ≠ 1 := by omega
  have hcb : hc ≤ b := by
    by_cases heq : tn + 1 = n - 2
    · have hval : b = hc := by
        rw [show b = p.getD (tn + 1) 0 by rfl, heq]
      omega
    · have hnotlast : tn + 1 ≠ n - 1 := by
        intro heq'
        have hb' : b = 1 := by
          rw [show b = p.getD (tn + 1) 0 by rfl, heq', hlast]
        exact hb1 hb'
      have hlt : tn + 1 < n - 2 := by omega
      have hdec := avoid312_record_block_decreasing p hp havoid tn n
        (by omega) (by omega) hrecn hnon_after (tn + 1) (n - 2)
        (by omega) hlt (by omega)
      have hdec' : hc < b := by
        calc
          hc = p.getD (n - 2) 0 := by rfl
          _ < p.getD (tn + 1) 0 := hdec
          _ = b := by rfl
      omega
  by_cases hc2 : hc = 2
  · have hqzero : q.getD 0 0 = b + 1 := by simpa [hc2] using hqp
    have hbrel : b + 1 = n := by
      rw [hqfirst] at hqzero
      exact hqzero.symm
    have hbval : b = n - 1 := by omega
    have hqone : q.getD 1 0 = 1 := by simpa [hc2] using hq_c
    have hrmax : r.getD (n - 2) 0 = n := by
      have h := hr_blast
      rw [hbval] at h
      simpa only [show n - 1 - 1 = n - 2 by omega] using h
    have hqnmem : n ∈ q := hqperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
    have hqidxn : q.idxOf n = 0 := by
      have hq0lt : 0 < q.length := by simp [q, n]; omega
      have hi := hqnodup.idxOf_getElem (i := 0) hq0lt
      have hv : q[0] = n := by
        rw [← List.getD_eq_getElem _ 0 hq0lt]
        exact hqfirst
      rw [hv] at hi
      exact hi
    have hrlast : r.getD (n - 1) 0 = 1 := by
      have hqlen : q.length = n := by simp [q, n]
      have hqperm' : q.Perm (List.range' 1 q.length) := by
        rw [hqlen]
        exact hqperm
      have h := one_block_B_at q hqperm' hqmax n hqnmem 0
        (by simp [q, n]; omega) hqidxn
      rw [if_pos (by simp [q, n]; omega)] at h
      change r.getD (n - 1) 0 = q.getD 1 0 at h
      rw [hqone] at h
      exact h
    have hpfirst : p.getD 0 0 = n := by
      have h := congrArg (fun l : List ℕ => l.getD 0 0) hpr
      have hrlen : r.length = n := by simp [r, q, n]
      have hrperm' : r.Perm (List.range' 1 r.length) := by
        rw [hrlen]
        exact hrperm
      have hrmax' : r.getD (r.length - 2) 0 = r.length := by
        rw [hrlen]
        exact hrmax
      have hrlast' : r.getD (r.length - 1) 0 = 1 := by
        rw [hrlen]
        exact hrlast
      rw [B_first_of_final_max_one r hrperm' (by rw [hrlen]; omega)
        hrmax' hrlast'] at h
      omega
    have hdesc := avoid312_first_max_descending p hp (by omega) hpfirst havoid
    have hfixed' : B (B (B ((List.range' 1 n).reverse))) =
        (List.range' 1 n).reverse := by
      have hfixed0 := hBfixed
      rw [hdesc] at hfixed0
      change B (B (B ((List.range' 1 n).reverse))) =
        (List.range' 1 n).reverse at hfixed0
      exact hfixed0
    rw [B_descending n (by omega), B_successorWord n (by omega),
      B_recordStaircase n (by omega)] at hfixed'
    have hsecond := congrArg (fun l : List ℕ => l.getD 1 0) hfixed'
    have hleft : (n :: (List.range' 2 (n - 2) ++ [1])).getD 1 0 = 2 := by
      have hi : 1 < (n :: (List.range' 2 (n - 2) ++ [1])).length := by simp
      rw [List.getD_eq_getElem _ 0 hi]
      simp only [List.getElem_cons_succ]
      rw [List.getElem_append]
      simp [show 0 < n - 2 by omega]
    have hright : ((List.range' 1 n).reverse).getD 1 0 = n - 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_reverse]
      simp only [List.length_range']
      rw [List.getElem_range'_1]
      omega
    rw [hleft, hright] at hsecond
    omega
  · have hxz : hc - 1 < hc ∧ hc < b + 1 := by omega
    have hidxc : p.idxOf hc = n - 2 := by
      have hi : n - 2 < p.length := by simp [n]; omega
      have hv : p[n - 2] = hc := by
        rw [← List.getD_eq_getElem _ 0 hi]
      have hi' := hpnodup.idxOf_getElem (i := n - 2) hi
      rw [hv] at hi'
      exact hi'
    have hidxx : p.idxOf (hc - 1) < n - 2 := by
      have hi := List.idxOf_lt_length_of_mem hxmemp
      by_contra hnot
      have hcases : p.idxOf (hc - 1) = n - 2 ∨ p.idxOf (hc - 1) = n - 1 := by omega
      rcases hcases with heq | heq
      · have hval : p.getD (p.idxOf (hc - 1)) 0 = hc - 1 := by
          rw [List.getD_eq_getElem _ 0 hi]
          exact List.getElem_idxOf hi
        rw [heq] at hval
        have hv : p.getD (n - 2) 0 = hc := by rfl
        rw [hv] at hval
        omega
      · have hval : p.getD (p.idxOf (hc - 1)) 0 = hc - 1 := by
          rw [List.getD_eq_getElem _ 0 hi]
          exact List.getElem_idxOf hi
        rw [heq, hlast] at hval
        omega
    have hxz' : hc - 1 < hc ∧ hc < hat p (hc - 1) := by simpa [hhatx] using hxz
    have hidxx' : p.idxOf (hc - 1) < p.idxOf hc := by
      rw [hidxc]
      exact hidxx
    exact no_upward_edge_over_later_value p hp havoid (hc - 1) hc
      hxmemp hcmem hxz' hidxx'

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Descending
