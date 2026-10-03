/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseTail
   mirror-E: none(waiver:final-cycle-in-standard-cycle-word)
   anchors: []
   utility: none
   digest: The maximal-label cycle is the final block of the standard cycle word. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail

open D5.S3.Combinatorics.ArrowWilfDefs

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))


/-- If the inverse word sends the first label to the maximum, its cycle
word ends at the first label. -/
theorem B_first_max_forces_last_one (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
    (hfirst : (B p).getD 0 0 = p.length) :
    p.getD (p.length - 1) 0 = 1 := by
  have hat_record_target_is_closing (p : List ℕ) (hp : p.Nodup)
      (x : ℕ) (hx : x ∈ p)
      (hrecord : IsLtrMax p (p.idxOf (hat p x))) :
      p.idxOf x + 1 = p.length ∨ IsLtrMax p (p.idxOf x + 1) := by
    have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
    by_cases hnext : p.idxOf x + 1 < p.length
    · right
      by_contra hnon
      have hhat : hat p x = p.getD (p.idxOf x + 1) 0 := by
        unfold hat
        exact if_pos ⟨hnext, hnon⟩
      have htarget : p.idxOf (hat p x) = p.idxOf x + 1 := by
        rw [hhat, List.getD_eq_getElem _ 0 hnext]
        simpa using (List.get_idxOf hp ⟨p.idxOf x + 1, hnext⟩)
      exact hnon (htarget ▸ hrecord)
    · left
      omega
  open ThetaBasicInverse in
  have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have h1mem : 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨0, hn, by omega⟩)
  have hnmem : p.length ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨p.length - 1, by omega, by omega⟩)
  have hidx1 : p.idxOf 1 < p.length := List.idxOf_lt_length_of_mem h1mem
  have hidxn : p.idxOf p.length < p.length := List.idxOf_lt_length_of_mem hnmem
  have hval1 : p.getD (p.idxOf 1) 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 hidx1]
    exact List.getElem_idxOf hidx1
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
  have hhat : D5.S3.Combinatorics.ArrowWilfDefs.hat p 1 = p.length := by
    have hh : (B p).getD 0 0 =
        D5.S3.Combinatorics.ArrowWilfDefs.hat p 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simp
    exact hh.symm.trans hfirst
  have htarget : p.idxOf (D5.S3.Combinatorics.ArrowWilfDefs.hat p 1) =
      p.idxOf p.length := by rw [hhat]
  have hclose := hat_record_target_is_closing p hnodup 1
    h1mem (by rw [htarget]; exact hrecn)
  have hbranch : ¬ (p.idxOf 1 + 1 < p.length ∧
      ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (p.idxOf 1 + 1)) := by
    rcases hclose with he | he
    · intro h; omega
    · intro h; exact h.2 he
  have hgreat : p.getD
      (Nat.findGreatest (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p)
        (p.idxOf 1)) 0 = p.length := by
    have hh := hhat
    unfold D5.S3.Combinatorics.ArrowWilfDefs.hat at hh
    dsimp only at hh
    rw [if_neg hbranch] at hh
    exact hh
  have hglt : Nat.findGreatest
      (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (p.idxOf 1) < p.length :=
    lt_of_le_of_lt (Nat.findGreatest_le _) hidx1
  have hidxgreat : Nat.findGreatest
      (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (p.idxOf 1) =
      p.idxOf p.length := by
    have hi : p.getD
        (Nat.findGreatest (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p)
          (p.idxOf 1)) 0 = p.getD (p.idxOf p.length) 0 :=
      hgreat.trans hvaln.symm
    have helem : p[Nat.findGreatest
        (D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p) (p.idxOf 1)] =
        p[p.idxOf p.length] := by
      rw [← List.getD_eq_getElem _ 0 hglt,
        ← List.getD_eq_getElem _ 0 hidxn, hi]
    exact (hnodup.getElem_inj_iff).mp helem
  have hn_before : p.idxOf p.length ≤ p.idxOf 1 := by
    rw [← hidxgreat]
    exact Nat.findGreatest_le _
  have hlastidx : p.idxOf 1 + 1 = p.length := by
    rcases hclose with he | hrec
    · exact he
    · by_cases hnextlt : p.idxOf 1 + 1 < p.length
      · have hh := hrec (p.idxOf p.length) (by omega)
        rw [hvaln] at hh
        have hle := hbound (p.idxOf 1 + 1) hnextlt
        have hne : p.getD (p.idxOf 1 + 1) 0 ≠ p.length := by
          intro heq
          have helem : p[p.idxOf 1 + 1] = p[p.idxOf p.length] := by
            rw [← List.getD_eq_getElem _ 0 hnextlt,
              ← List.getD_eq_getElem _ 0 hidxn, heq, hvaln]
          exact (by omega : p.idxOf 1 + 1 ≠ p.idxOf p.length)
            ((hnodup.getElem_inj_iff).mp helem)
        omega
      · omega
  have hidxlast : p.idxOf 1 = p.length - 1 := by omega
  rw [← hidxlast]
  exact hval1

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail
