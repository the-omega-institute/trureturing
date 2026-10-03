/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Classify
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube312Classify
   mirror-E: none(waiver:312-indecomposable-cube-classification)
   anchors: []
   utility: none
   digest: Indecomposable 312-avoiders fixed by the third iterate are classified. -/
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Descending
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Edge
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Suffix
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Final
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Classify
local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))
open D5.S3.Combinatorics
open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumAvoid
open D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Edge
open D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Descending
open ThetaBasicInverse
set_option maxHeartbeats 4000000 in
-- The nested permutation and record-block chase needs more simplifier budget.
theorem fixed312_large_absurd (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 3 < p.length)
    (hindecomp : ∀ k, 0 < k → k < p.length →
      ∃ x ∈ p.take k, k < x)
    (havoid : ¬ Contains [3, 1, 2] [] 3 p)
    (hBfixed : B (B (B p)) = p) : False := by
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
  have hcontains312 (p : List ℕ) :
      D5.S3.Combinatorics.ArrowWilfDefs.Contains [3, 1, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] > p[k.val] ∧
        p[k.val] > p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 3, x 1, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 3 := by simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 1 := by simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by simpa using (hf ⟨2, by simp⟩).symm
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
  by_cases hb1 : b = 1
  · have hc_n : hc = n := by
      have hq_end : q.getD (n - 1) 0 = 1 := by simpa [hb1] using hq_last
      have hi : hc - 1 < q.length := by simp [q, n]; omega
      have hj : n - 1 < q.length := by simp [q, n]; omega
      have helem : q[hc - 1] = q[n - 1] := by
        rw [← List.getD_eq_getElem _ 0 hi,
          ← List.getD_eq_getElem _ 0 hj, hq_c, hq_end]
      have heq := (hqnodup.getElem_inj_iff).mp helem
      omega
    have hp_penult : p.getD (n - 2) 0 = n := by simpa [hc] using hc_n
    have hq_penult : q.getD (n - 2) 0 = 2 := by
      have h := hqp
      rw [hc_n, hb1] at h
      simpa only [show n - 2 = n - 2 by rfl] using h
    have hq_last_one : q.getD (n - 1) 0 = 1 := by simpa [hb1] using hq_last
    have hr_first : r.getD 0 0 = n := by
      have h := hr_blast
      rw [hb1] at h
      simpa using h
    have hr_second : r.getD 1 0 = 1 := by simpa [hb1] using hr_b
    have hhat_nm1 : hat p (n - 1) = 2 := by
      have h := hhatx
      rw [hc_n, hb1] at h
      exact h
    have hnm1mem : n - 1 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
    let i := p.idxOf (n - 1)
    have hi : i < n := List.idxOf_lt_length_of_mem hnm1mem
    have hival : p.getD i 0 = n - 1 := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_idxOf hi
    have hnexti : i + 1 < n := by
      by_contra hnot
      have heq : i = n - 1 := by omega
      rw [heq, hlast] at hival
      omega
    have hi_before_n : i < n - 2 := by
      have hne : i ≠ n - 2 := by
        intro heq
        rw [heq, hp_penult] at hival
        omega
      omega
    have hrec_i : IsLtrMax p i := by
      intro j hj
      have hjlt : j < n := by omega
      have hmem : p.getD j 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hjlt]
        exact List.getElem_mem hjlt
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hmem)
      have hne_nm1 : p.getD j 0 ≠ n - 1 := by
        intro he
        have helem : p[j] = p[i] := by
          rw [← List.getD_eq_getElem _ 0 hjlt,
            ← List.getD_eq_getElem _ 0 hi, he, hival]
        exact (by omega : j ≠ i) ((hpnodup.getElem_inj_iff).mp helem)
      have hne_n : p.getD j 0 ≠ n := by
        intro he
        have helem : p[j] = p[n - 2] := by
          rw [← List.getD_eq_getElem _ 0 hjlt,
            ← List.getD_eq_getElem _ 0 (by omega), he, hp_penult]
        exact (by omega : j ≠ n - 2) ((hpnodup.getElem_inj_iff).mp helem)
      rw [hival]
      omega
    have hnonnext : ¬ IsLtrMax p (i + 1) := by
      intro hrec
      have hg : Nat.findGreatest (IsLtrMax p) i = i := by
        apply le_antisymm (Nat.findGreatest_le _)
        exact Nat.le_findGreatest (le_refl _) hrec_i
      have hclose : hat p (n - 1) = n - 1 := by
        unfold hat
        change (if i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)
          then p.getD (i + 1) 0
          else p.getD (Nat.findGreatest (IsLtrMax p) i) 0) = n - 1
        rw [if_neg (by intro h; exact h.2 hrec), hg, hival]
      rw [hclose] at hhat_nm1
      omega
    have hnexttwo : p.getD (i + 1) 0 = 2 := by
      unfold hat at hhat_nm1
      change (if i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)
        then p.getD (i + 1) 0
        else p.getD (Nat.findGreatest (IsLtrMax p) i) 0) = 2 at hhat_nm1
      rw [if_pos ⟨hnexti, hnonnext⟩] at hhat_nm1
      exact hhat_nm1
    have hpair_before_n : i + 1 < n - 2 := by
      have hne : i + 1 ≠ n - 2 := by
        intro heq
        rw [heq, hp_penult] at hnexttwo
        omega
      omega
    have hno_gap : i + 2 = n - 2 := by
      by_contra hne
      have hmiddle : i + 2 < n - 2 := by omega
      let z := p.getD (i + 2) 0
      have hzmem : z ∈ p := by
        rw [show z = p.getD (i + 2) 0 by rfl,
          List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_mem (by omega)
      obtain ⟨a, ha, hza⟩ := List.mem_range'.mp (hp.mem_iff.mp hzmem)
      have hzne (j : ℕ) (hj : j < n) (hji : j ≠ i + 2) :
          z ≠ p.getD j 0 := by
        intro he
        have he' : p.getD (i + 2) 0 = p.getD j 0 := by simpa [z] using he
        have helem : p[i + 2] = p[j] := by
          rw [← List.getD_eq_getElem _ 0 (by omega),
            ← List.getD_eq_getElem _ 0 hj, he']
        exact hji.symm ((hpnodup.getElem_inj_iff).mp helem)
      have hz3 : 2 < z := by
        have hz1 : z ≠ 1 := by
          intro he
          exact hzne (n - 1) (by omega) (by omega) (he.trans hlast.symm)
        have hz2 : z ≠ 2 := by
          intro he
          exact hzne (i + 1) (by omega) (by omega) (he.trans hnexttwo.symm)
        have hzpos : 0 < z := by omega
        omega
      have hznm1 : z < n - 1 := by
        have hzne1 : z ≠ n - 1 := by
          intro he
          exact hzne i hi (by omega) (he.trans hival.symm)
        have hzne2 : z ≠ n := by
          intro he
          exact hzne (n - 2) (by omega) (by omega) (he.trans hp_penult.symm)
        omega
      apply havoid
      apply (hcontains312 p).mpr
      refine ⟨⟨i, hi⟩, ⟨i + 1, hnexti⟩, ⟨i + 2, by omega⟩,
        (by change i < i + 1; omega),
        (by change i + 1 < i + 2; omega), ?_, ?_⟩
      · rw [← List.getD_eq_getElem _ 0 hi,
          ← List.getD_eq_getElem _ 0 (by omega), hival]
        exact hznm1
      · rw [← List.getD_eq_getElem _ 0 hnexti,
          ← List.getD_eq_getElem _ 0 (by omega), hnexttwo]
        exact hz3
    have hi_shape : i = n - 4 := by omega
    have hq_two : q.getD 1 0 = n - 1 := by
      have hrecn' : IsLtrMax p (i + 2) := by
        have heq : i + 2 = tn := by
          have htne : tn = n - 2 := by
            have hj := hpnodup.idxOf_getElem (i := n - 2) (by omega : n - 2 < p.length)
            have hv : p[n - 2] = n := by
              rw [← List.getD_eq_getElem _ 0 (by omega), hp_penult]
            rw [hv] at hj
            exact hj
          omega
        rw [heq]
        exact hrecn
      have hedges := hat_record_block_edges p hpnodup i (i + 2)
        (by omega) (by omega) hrec_i (by
          intro j hj1 hj2
          have hj : j = i + 1 := by omega
          simpa [hj] using hnonnext) (Or.inr hrecn')
      have hclose := hedges.2
      have hval : p.getD (i + 1) 0 = 2 := hnexttwo
      rw [show i + 2 - 1 = i + 1 by omega, hval, hival] at hclose
      have hmap := B_getD_hat p 2 (by omega) (by omega)
      change q.getD 1 0 = hat p 2 at hmap
      exact hmap.trans hclose
    have hr_last_nm1 : r.getD (n - 1) 0 = n - 1 := by
      have hqnmem : n ∈ q := hqperm.mem_iff.mpr
        (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
      have hqidxn : q.idxOf n = 0 := by
        have hq0 : 0 < q.length := by simp [q, n]; omega
        have hj := hqnodup.idxOf_getElem (i := 0) hq0
        have hv : q[0] = n := by
          rw [← List.getD_eq_getElem _ 0 hq0, hqfirst]
        rw [hv] at hj
        exact hj
      have hqlen : q.length = n := by simp [q, n]
      have hqperm' : q.Perm (List.range' 1 q.length) := by
        rw [hqlen]
        exact hqperm
      have h := one_block_B_at q hqperm' hqmax n hqnmem 0
        (by rw [hqlen]; omega) hqidxn
      rw [if_pos (by rw [hqlen]; omega)] at h
      change r.getD (n - 1) 0 = q.getD 1 0 at h
      exact h.trans hq_two
    have hq_third : q.getD 2 0 = n - 3 := by
      have hxmem : n - 3 ∈ r := hrperm.mem_iff.mpr
        (List.mem_range'.mpr ⟨n - 4, by omega, by omega⟩)
      let t := r.idxOf (n - 3)
      have ht : t < n := by
        have hh := List.idxOf_lt_length_of_mem hxmem
        simpa [t, r, q, n] using hh
      have hrmax : ∀ y ∈ r, y ≤ r.getD 0 0 := by
        intro y hy
        rw [hr_first]
        obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hy)
        omega
      have hrlen : r.length = n := by simp [r, q, n]
      have hrperm' : r.Perm (List.range' 1 r.length) := by
        rw [hrlen]
        exact hrperm
      have hp_nm3 : p.getD (n - 4) 0 = n - 1 := by
        rw [← hi_shape]
        exact hival
      have hBr : (B r).getD (n - 4) 0 = n - 1 := by
        rw [hpr]
        exact hp_nm3
      have h := one_block_B_at r hrperm' hrmax (n - 3) hxmem t
        (by rw [hrlen]; omega) rfl
      have hindex : n - 3 - 1 = n - 4 := by omega
      rw [hindex, hrlen] at h
      have htnotlast : t + 1 < n := by
        by_contra hnot
        have hno : ¬ t + 1 < n := by omega
        rw [if_neg hno, hr_first] at h
        rw [hBr] at h
        omega
      rw [if_pos htnotlast, hBr] at h
      have hindexlast : t + 1 = n - 1 := by
        have hi1 : t + 1 < r.length := by rw [hrlen]; exact htnotlast
        have hi2 : n - 1 < r.length := by rw [hrlen]; omega
        have helem : r[t + 1] = r[n - 1] := by
          calc
            r[t + 1] = r.getD (t + 1) 0 :=
              (List.getD_eq_getElem _ 0 hi1).symm
            _ = n - 1 := h.symm
            _ = r.getD (n - 1) 0 := hr_last_nm1.symm
            _ = r[n - 1] := List.getD_eq_getElem _ 0 hi2
        exact (hrnodup.getElem_inj_iff).mp helem
      have hr_nm2 : r.getD (n - 2) 0 = n - 3 := by
        have hv : r.getD t 0 = n - 3 := by
          rw [List.getD_eq_getElem _ 0 (by rw [hrlen]; omega)]
          exact List.getElem_idxOf (by rw [hrlen]; omega)
        have heq : t = n - 2 := by omega
        rw [← heq]
        exact hv
      have hqidxnm1 : q.idxOf (n - 1) = 1 := by
        have hq1 : 1 < q.length := by simp [q, n]; omega
        have hj := hqnodup.idxOf_getElem (i := 1) hq1
        have hv : q[1] = n - 1 := by
          rw [← List.getD_eq_getElem _ 0 hq1, hq_two]
        rw [hv] at hj
        exact hj
      have hqnm1mem : n - 1 ∈ q := hqperm.mem_iff.mpr
        (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
      have hqlen : q.length = n := by simp [q, n]
      have hqperm' : q.Perm (List.range' 1 q.length) := by
        rw [hqlen]
        exact hqperm
      have hqinv := one_block_B_at q hqperm' hqmax (n - 1) hqnm1mem 1
        (by rw [hqlen]; omega) hqidxnm1
      rw [if_pos (by rw [hqlen]; omega)] at hqinv
      have hindex2 : n - 1 - 1 = n - 2 := by omega
      rw [hindex2] at hqinv
      change r.getD (n - 2) 0 = q.getD 2 0 at hqinv
      exact hqinv.symm.trans hr_nm2
    have hn6 : 6 ≤ n := by
      by_contra hnot
      have hlen : q.length = n := by simpa using hqperm.length_eq
      have hnodup : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
      have hcases : n = 4 ∨ n = 5 := by omega
      rcases hcases with hfour | hfive
      · rw [hfour] at hq_third hq_penult
        norm_num at hq_third hq_penult
        omega
      · rw [hfive] at hq_third hq_penult hlen
        have hq2 : q.getD 2 0 = 2 := by simpa using hq_third
        have hq3 : q.getD 3 0 = 2 := by simpa using hq_penult
        have helem : q[2] = q[3] := by
          rw [← List.getD_eq_getElem _ 0 (by omega),
            ← List.getD_eq_getElem _ 0 (by omega), hq2, hq3]
        have heq := (hnodup.getElem_inj_iff).mp helem
        omega
    by_cases hn6eq : n = 6
    · have hqfixed : B (B (B q)) = q := by
        have hh := congrArg B hpr
        simpa [q, r] using hh
      have hqperm6 : q.Perm (List.range' 1 6) := by simpa [hn6eq] using hqperm
      have h0 : q.getD 0 0 = 6 := by simpa [hn6eq] using hqfirst
      have h1 : q.getD 1 0 = 5 := by simpa [hn6eq] using hq_two
      have h2 : q.getD 2 0 = 3 := by simpa [hn6eq] using hq_third
      have h4 : q.getD 4 0 = 2 := by simpa [hn6eq] using hq_penult
      have h5 : q.getD 5 0 = 1 := by simpa [hn6eq] using hq_last_one
      have hlen : q.length = 6 := by simpa using hqperm6.length_eq
      have hnodup : q.Nodup := hqperm6.nodup_iff.mpr List.nodup_range'
      have h4mem : 4 ∈ q := hqperm6.mem_iff.mpr
        (List.mem_range'.mpr ⟨3, by omega, by omega⟩)
      obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp h4mem
      have hget : q.getD j 0 = 4 := by
        rw [List.getD_eq_getElem _ 0 hj]
        exact hval
      have hj3 : j = 3 := by
        have hjlt : j < 6 := by omega
        have hnot (t : ℕ) (ht : t < 6) (hne : j = t)
            (hval_t : q.getD t 0 ≠ 4) : False := by
          rw [hne] at hget
          exact hval_t hget
        have hne0 : j ≠ 0 := by
          intro he; exact hnot 0 (by omega) he (by omega)
        have hne1 : j ≠ 1 := by
          intro he; exact hnot 1 (by omega) he (by omega)
        have hne2 : j ≠ 2 := by
          intro he; exact hnot 2 (by omega) he (by omega)
        have hne4 : j ≠ 4 := by
          intro he; exact hnot 4 (by omega) he (by omega)
        have hne5 : j ≠ 5 := by
          intro he; exact hnot 5 (by omega) he (by omega)
        omega
      have h3 : q.getD 3 0 = 4 := by rw [← hj3]; exact hget
      have hqexact : q = [6, 5, 3, 4, 2, 1] := by
        apply List.ext_getElem
        · simp [hlen]
        · intro k hk hk'
          have hkl : k < 6 := by omega
          have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
          rcases hcases with h | h | h | h | h | h
          all_goals subst k
          all_goals simp_all
      rw [hqexact] at hqfixed
      have hfalse : B
          (B (B [6, 5, 3, 4, 2, 1])) ≠
          [6, 5, 3, 4, 2, 1] := by decide
      exact hfalse hqfixed
    have hn7 : 7 ≤ n := by omega
    have hhat_three : hat p 3 = n - 3 := by
      have hh := B_getD_hat p 3 (by omega) (by omega)
      change q.getD (3 - 1) 0 = hat p 3 at hh
      simpa only [show 3 - 1 = 2 by omega, hq_third] using hh.symm
    have hpen : p.getD (n - 4) 0 = n - 1 := by
      rw [← hi_shape]
      exact hival
    have htwo : p.getD (n - 3) 0 = 2 := by
      have heq : i + 1 = n - 3 := by omega
      rw [← heq]
      exact hnexttwo
    have hpair := ThetaCube312Suffix.terminal_pair_positions p n hp hn7
      havoid hpen htwo hp_penult hlast hhat_three
    exact ThetaCube312Final.terminal_collision p n hp hn7 hpair.2 hpen htwo
      hp_penult hqfirst hq_third hq_penult hr_first hBfixed
  · exact ThetaCube312Descending.successor_gt_one_absurd p hp hn
      hindecomp havoid hBfixed (by change 1 < b; omega)

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Classify
