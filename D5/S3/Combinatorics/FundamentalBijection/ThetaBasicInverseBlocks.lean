/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseBlocks
   mirror-E: none(waiver:record-block-orbits-use-positional-permutation-data)
   anchors: []
   utility: none
   digest: Record-block edges yield exact orbits of the inverse fundamental bijection. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

/-- The cycle extracted at a record is exactly the interval up to the next
record, with no early return to its initial letter. -/
theorem cycleFrom_B_record_block (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length))
    (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
    (hs : IsLtrMax p s)
    (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
    (hboundary : e = p.length ∨ IsLtrMax p e) :
    ThetaFixedDefs.cycleFrom (B p) (p.getD s 0) =
      (p.drop s).take (e - s) := by
  have inverse_record_block_orbit (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
      (hs : IsLtrMax p s)
      (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
      (hboundary : e = p.length ∨ IsLtrMax p e) :
      (∀ j < e - s,
        (D5.S3.Combinatorics.ArcherCyclicDefs.image (B p))^[j] (p.getD s 0) =
          p.getD (s + j) 0) ∧
      (D5.S3.Combinatorics.ArcherCyclicDefs.image (B p))^[e - s] (p.getD s 0) =
        p.getD s 0 := by
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
    have hedges := hat_record_block_edges p hnodup s e hse he hs hnon hboundary
    have himage (i : ℕ) (hi : i < p.length) :
        D5.S3.Combinatorics.ArcherCyclicDefs.image (B p) (p.getD i 0) =
          hat p (p.getD i 0) := by
      have hx : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hi]
        exact List.getElem_mem hi
      obtain ⟨j, hj, hval⟩ := List.mem_range'.mp (hp.mem_iff.mp hx)
      have hindex : p.getD i 0 - 1 = j := by omega
      have hB : j < (B p).length := by simpa using hj
      unfold D5.S3.Combinatorics.ArcherCyclicDefs.image
      rw [hindex, List.getD_eq_getElem _ 0 hB]
      simp only [List.getElem_map, List.getElem_range'_1]
      simpa only [one_mul] using congrArg (hat p) hval.symm
    have hsteps : ∀ j < e - s,
        (D5.S3.Combinatorics.ArcherCyclicDefs.image (B p))^[j] (p.getD s 0) =
          p.getD (s + j) 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          intro hj
          have hj' : j < e - s := by omega
          rw [Function.iterate_succ_apply', ih hj']
          rw [himage (s + j) (by omega)]
          simpa only [Nat.add_assoc] using hedges.1 (s + j) (by omega) (by omega)
    refine ⟨hsteps, ?_⟩
    have hprev : e - s - 1 < e - s := by omega
    have heq : s + (e - s - 1) = e - 1 := by omega
    have hlen : e - s = (e - s - 1) + 1 := by omega
    rw [hlen, Function.iterate_succ_apply', hsteps _ hprev, heq,
      himage (e - 1) (by omega), hedges.2]
  let f := D5.S3.Combinatorics.ArcherCyclicDefs.image (B p)
  let m := p.getD s 0
  let L := e - s
  let q := (List.range p.length).map (fun i => f^[i + 1] m)
  have horbit := inverse_record_block_orbit p hp s e hse he hs hnon hboundary
  have hL : 0 < L := by dsimp [L]; omega
  have hLle : L ≤ p.length := by dsimp [L]; omega
  have hqLen : q.length = p.length := by simp [q]
  have hqhit : q[L - 1]'(by omega : L - 1 < q.length) = m := by
    simp only [q, List.getElem_map, List.getElem_range]
    have heq : L - 1 + 1 = L := by omega
    simpa [f, m, L, heq] using horbit.2
  have hqprefix : q.take (L - 1) = (p.drop (s + 1)).take (L - 1) := by
    apply List.ext_getElem
    · simp only [List.length_take, hqLen, List.length_drop]
      omega
    · intro i hi hi'
      have hii : i < L - 1 := by
        simpa [List.length_take, hqLen, Nat.min_eq_left (by omega : L - 1 ≤ p.length)]
          using hi
      have his : s + 1 + i < p.length := by dsimp [L] at hii; omega
      simp only [List.getElem_take, q, List.getElem_map, List.getElem_range,
        List.getElem_drop]
      have hstep := horbit.1 (i + 1) (by dsimp [L] at hii ⊢; omega)
      rw [List.getD_eq_getElem _ 0 (by omega : s + (i + 1) < p.length)] at hstep
      simpa only [f, m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hslen : s < p.length := by omega
  have hdrop : p.drop s = m :: p.drop (s + 1) := by
    calc
      p.drop s = p[s]'hslen :: p.drop (s + 1) := List.drop_eq_getElem_cons hslen
      _ = m :: p.drop (s + 1) :=
        congrArg (fun x => x :: p.drop (s + 1))
          (List.getD_eq_getElem p 0 hslen).symm
  have hnotmem : m ∉ p.drop (s + 1) := by
    have hn : (p.drop s).Nodup := hnodup.drop
    rw [hdrop] at hn
    exact (List.nodup_cons.mp hn).1
  have hqgood : ∀ y ∈ q.take (L - 1), decide (y ≠ m) = true := by
    intro y hy
    rw [hqprefix] at hy
    have hymem : y ∈ p.drop (s + 1) := List.mem_of_mem_take hy
    have hyne : y ≠ m := by
      intro h
      exact hnotmem (h ▸ hymem)
    simp [hyne]
  have hqtake : q.takeWhile (· ≠ m) = q.take (L - 1) := by
    conv_lhs => rw [← List.take_append_drop (L - 1) q]
    rw [List.takeWhile_append_of_pos hqgood,
      List.drop_eq_getElem_cons (by omega : L - 1 < q.length), hqhit]
    simp
  unfold ThetaFixedDefs.cycleFrom
  have hBlen : (B p).length = p.length := by simp
  simp only [hBlen]
  change m :: q.takeWhile (· ≠ m) = (p.drop s).take L
  rw [hqtake, hqprefix, hdrop]
  have hlength : L = (L - 1) + 1 := by omega
  rw [hlength]
  simp

/-- A non-record entry's cycle contains its larger starting record, so it
cannot be a leader. -/
theorem nonrecord_not_B_leader (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (x : ℕ) (hx : x ∈ p)
    (hnon : ¬ IsLtrMax p (p.idxOf x)) :
    ¬ ThetaFixedDefs.IsLeader (B p) x := by
  have inverse_record_block_orbit (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
      (hs : IsLtrMax p s)
      (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
      (hboundary : e = p.length ∨ IsLtrMax p e) :
      (∀ j < e - s,
        (D5.S3.Combinatorics.ArcherCyclicDefs.image (B p))^[j] (p.getD s 0) =
          p.getD (s + j) 0) ∧
      (D5.S3.Combinatorics.ArcherCyclicDefs.image (B p))^[e - s] (p.getD s 0) =
        p.getD s 0 := by
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
    have hedges := hat_record_block_edges p hnodup s e hse he hs hnon hboundary
    have himage (i : ℕ) (hi : i < p.length) :
        D5.S3.Combinatorics.ArcherCyclicDefs.image (B p) (p.getD i 0) =
          hat p (p.getD i 0) := by
      have hx : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hi]
        exact List.getElem_mem hi
      obtain ⟨j, hj, hval⟩ := List.mem_range'.mp (hp.mem_iff.mp hx)
      have hindex : p.getD i 0 - 1 = j := by omega
      have hB : j < (B p).length := by simpa using hj
      unfold D5.S3.Combinatorics.ArcherCyclicDefs.image
      rw [hindex, List.getD_eq_getElem _ 0 hB]
      simp only [List.getElem_map, List.getElem_range'_1]
      simpa only [one_mul] using congrArg (hat p) hval.symm
    have hsteps : ∀ j < e - s,
        (D5.S3.Combinatorics.ArcherCyclicDefs.image (B p))^[j] (p.getD s 0) =
          p.getD (s + j) 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          intro hj
          have hj' : j < e - s := by omega
          rw [Function.iterate_succ_apply', ih hj']
          rw [himage (s + j) (by omega)]
          simpa only [Nat.add_assoc] using hedges.1 (s + j) (by omega) (by omega)
    refine ⟨hsteps, ?_⟩
    have hprev : e - s - 1 < e - s := by omega
    have heq : s + (e - s - 1) = e - 1 := by omega
    have hlen : e - s = (e - s - 1) + 1 := by omega
    rw [hlen, Function.iterate_succ_apply', hsteps _ hprev, heq,
      himage (e - 1) (by omega), hedges.2]
  have mem_cycleFrom_of_no_early_return (p : List ℕ) (x y d : ℕ)
      (hd : 0 < d) (hdle : d ≤ p.length)
      (havoid : ∀ j, 0 < j → j ≤ d →
        (D5.S3.Combinatorics.ArcherCyclicDefs.image p)^[j] x ≠ x)
      (hy : (D5.S3.Combinatorics.ArcherCyclicDefs.image p)^[d] x = y) :
      y ∈ ThetaFixedDefs.cycleFrom p x := by
    let f := D5.S3.Combinatorics.ArcherCyclicDefs.image p
    let q := (List.range p.length).map (fun i => f^[i + 1] x)
    have hlen : q.length = p.length := by simp [q]
    have hgood : ∀ z ∈ q.take d, decide (z ≠ x) = true := by
      intro z hz
      obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
      have hid : i < d := by simpa [hlen, hdle] using hi
      have hq : (q.take d)[i] = f^[i + 1] x := by
        simp only [List.getElem_take, q, List.getElem_map, List.getElem_range]
      rw [← hzi, hq]
      exact decide_eq_true (havoid (i + 1) (by omega) (by omega))
    have hmem : y ∈ q.take d := by
      have hi : d - 1 < (q.take d).length := by simp [hlen, hdle]; omega
      have hq : (q.take d)[d - 1] = y := by
        simp only [List.getElem_take, q, List.getElem_map, List.getElem_range]
        rw [show d - 1 + 1 = d by omega]
        exact hy
      rw [← hq]
      exact List.getElem_mem hi
    unfold ThetaFixedDefs.cycleFrom
    change y ∈ x :: q.takeWhile (· ≠ x)
    right
    rw [← List.take_append_drop d q]
    rw [List.takeWhile_append_of_pos hgood]
    exact List.mem_append_left _ hmem
  let t := p.idxOf x
  change ¬ IsLtrMax p t at hnon
  have ht : t < p.length := List.idxOf_lt_length_of_mem hx
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hzero : IsLtrMax p 0 := by
    intro j hj
    omega
  let s := Nat.findGreatest (IsLtrMax p) t
  have hrec : IsLtrMax p s := Nat.findGreatest_spec (Nat.zero_le t) hzero
  have hst : s ≤ t := Nat.findGreatest_le t
  have hst' : s < t := by
    by_contra h
    have heq : s = t := by omega
    exact hnon (heq ▸ hrec)
  have hnext : ∃ e, s < e ∧ e ≤ p.length ∧
      (∀ j, s < j → j < e → ¬ IsLtrMax p j) ∧
      (e = p.length ∨ IsLtrMax p e) := by
    let Q : ℕ → Prop := fun e => s < e ∧ e ≤ p.length ∧
      (e = p.length ∨ IsLtrMax p e)
    have hex : ∃ e, Q e := ⟨p.length, by omega, le_refl _, Or.inl rfl⟩
    let e := Nat.find hex
    have he : Q e := Nat.find_spec hex
    refine ⟨e, he.1, he.2.1, ?_, he.2.2⟩
    intro j hsj hje hr
    have hjQ : Q j := ⟨hsj, by omega, Or.inr hr⟩
    have hmin : e ≤ j := Nat.find_min' hex hjQ
    omega
  obtain ⟨e, hse, he, hinside, hboundary⟩ := hnext
  have hte : t < e := by
    by_contra h
    have hele : e ≤ t := by omega
    rcases hboundary with hend | hr
    · omega
    · have hbelow : e ≤ s := by
        simpa only [s] using Nat.le_findGreatest hele hr
      omega
  let f := D5.S3.Combinatorics.ArcherCyclicDefs.image (B p)
  let m := p.getD s 0
  let u := t - s
  let d := e - t
  have hblock := inverse_record_block_orbit p hp s e hse he hrec hinside hboundary
  have hget : p.getD t 0 = x := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_idxOf ht
  have htget : p[t] = x := List.getElem_idxOf ht
  have hu : f^[u] m = x := by
    have h := hblock.1 u (by dsimp [u]; omega)
    simpa only [f, m, u, Nat.add_sub_of_le hst, hget] using h
  have hd : 0 < d := by dsimp [d]; omega
  have hdle : d ≤ (B p).length := by simp [d]; omega
  have hadd : d + u = e - s := by dsimp [d, u]; omega
  have hdm : f^[d] x = m := by
    calc
      f^[d] x = f^[d] (f^[u] m) := by rw [hu]
      _ = f^[d + u] m := (Function.iterate_add_apply f d u m).symm
      _ = m := by rw [hadd]; exact hblock.2
  have hne : m ≠ x := by
    intro heq
    have hsget : p[s] = p[t] := by
      rw [show m = p[s] by exact List.getD_eq_getElem _ 0 (by omega)] at heq
      exact heq.trans htget.symm
    have := (hnodup.getElem_inj_iff).mp hsget
    omega
  have hbefore : ∀ j, 0 < j → j < d → f^[j] x ≠ x := by
    intro j hj hjd
    have huj : u + j < e - s := by dsimp [u, d] at *; omega
    have hstep := hblock.1 (u + j) huj
    have hidx : t + j < p.length := by omega
    have horbit : f^[j] x = p.getD (t + j) 0 := by
      calc
        f^[j] x = f^[j] (f^[u] m) := by rw [hu]
        _ = f^[j + u] m := (Function.iterate_add_apply f j u m).symm
        _ = p.getD (t + j) 0 := by
          rw [Nat.add_comm j u]
          rw [show s + (u + j) = t + j by dsimp [u]; omega] at hstep
          exact hstep
    rw [horbit]
    intro heq
    have hgeteq : p[t + j] = p[t] := by
      rw [List.getD_eq_getElem _ 0 hidx] at heq
      exact heq.trans htget.symm
    have := (hnodup.getElem_inj_iff).mp hgeteq
    omega
  have havoid : ∀ j, 0 < j → j ≤ d → f^[j] x ≠ x := by
    intro j hj hjd
    by_cases h : j = d
    · subst j
      rwa [hdm]
    · exact hbefore j hj (by omega)
  have hmcycle : m ∈ ThetaFixedDefs.cycleFrom (B p) x :=
    mem_cycleFrom_of_no_early_return (B p) x m d hd hdle havoid hdm
  have hle : x ≤ m := by
    simpa only [hget, m, s] using last_record_bounds_prefix p t ht t (le_refl t)
  have hlt : x < m := by omega
  intro hleader
  exact (not_le_of_gt hlt) (hleader m hmcycle)

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
