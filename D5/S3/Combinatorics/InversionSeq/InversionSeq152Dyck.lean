/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Dyck
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Dyck
   mirror-E: none(waiver:explicit-mono-dyck-bijection)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: East-count encoding bijects nondecreasing inversion sequences with Dyck words. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck

open DyckStep

def eastCounts (east : ℕ) : List DyckStep → List ℕ
  | [] => []
  | U :: rest => east :: eastCounts east rest
  | D :: rest => eastCounts (east + 1) rest

def dyckSteps (size east : ℕ) : List ℕ → List DyckStep
  | [] => List.replicate (size - east) D
  | value :: rest =>
    List.replicate (value - east) D ++ U :: dyckSteps size value rest

theorem monoDyckEquiv (size : ℕ) :
    ∃ equiv :
      {word : List ℕ // word.length = size ∧ InversionSeqDefs.IsInversionSeq word ∧
        word.Pairwise (· ≤ ·)} ≃
      {path : DyckWord // path.semilength = size},
      (∀ word, (equiv word).val.toList = dyckSteps size 0 word.val) ∧
      (∀ path, (equiv.symm path).val = eastCounts 0 path.val.toList) ∧
      (∀ word, (((equiv word).val.toList.reverse).takeWhile (· == D)).length =
        size - word.val.foldr max 0) ∧
      (∀ word, ((((equiv word).val.toList.splitOn U).map List.length).filter
          (· != 0)).dropLast =
        (List.zipWith (· - ·) word.val (0 :: word.val)).filter (· != 0)) := by
  have hread : ∀ steps : List DyckStep, ∀ east north : ℕ,
      (∀ index, (steps.take index).count D + east ≤
        (steps.take index).count U + north) →
      (eastCounts east steps).length = steps.count U ∧
      (eastCounts east steps).Pairwise (· ≤ ·) ∧
      (∀ value ∈ eastCounts east steps, east ≤ value) ∧
      (∀ index < (eastCounts east steps).length,
        (eastCounts east steps).getD index 0 ≤ north + index) := by
    intro steps
    induction steps with
    | nil => intro east north h; simp [eastCounts]
    | cons step rest ih =>
      intro east north h
      cases step with
      | U =>
        have ht : ∀ index, (rest.take index).count D + east ≤
            (rest.take index).count U + (north + 1) := by
          intro index
          have hh := h (index + 1)
          simpa [List.take_succ_cons, List.count_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hh
        obtain ⟨hlen, hsorted, hlower, hbound⟩ := ih east (north + 1) ht
        refine ⟨by simp [eastCounts, hlen], ?_, ?_, ?_⟩
        · simpa [eastCounts, List.pairwise_cons] using And.intro hlower hsorted
        · intro value hv
          simp only [eastCounts, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact le_rfl
          · exact hlower value hv
        · intro index hi
          cases index with
          | zero => simpa [eastCounts] using h 0
          | succ index =>
            have hi' : index < (eastCounts east rest).length := by
              simpa [eastCounts] using hi
            simpa [eastCounts, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hbound index hi'
      | D =>
        have ht : ∀ index, (rest.take index).count D + (east + 1) ≤
            (rest.take index).count U + north := by
          intro index
          have hh := h (index + 1)
          simpa [List.take_succ_cons, List.count_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hh
        obtain ⟨hlen, hsorted, hlower, hbound⟩ := ih (east + 1) north ht
        refine ⟨by simpa [eastCounts] using hlen, hsorted, ?_, hbound⟩
        intro value hv
        exact (Nat.le_succ east).trans (hlower value hv)
  have hwrite : ∀ word : List ℕ, ∀ east north : ℕ,
      east ≤ north → word.Pairwise (· ≤ ·) →
      (∀ value ∈ word, east ≤ value) →
      (∀ index < word.length, word.getD index 0 ≤ north + index) →
      (dyckSteps (north + word.length) east word).count U = word.length ∧
      (dyckSteps (north + word.length) east word).count D + east =
        north + word.length ∧
      (∀ index, ((dyckSteps (north + word.length) east word).take index).count D +
        east ≤ ((dyckSteps (north + word.length) east word).take index).count U +
          north) := by
    intro word
    induction word with
    | nil =>
      intro east north hen hsorted hlower hbound
      refine ⟨by simp [dyckSteps, List.count_replicate], ?_, ?_⟩
      · simp [dyckSteps]
        omega
      · intro index
        simp [dyckSteps, List.take_replicate, List.count_replicate]
        omega
    | cons value rest ih =>
      intro east north hen hsorted hlower hbound
      have hev : east ≤ value := hlower value (by simp)
      have hvn : value ≤ north := by simpa using hbound 0 (by simp)
      obtain ⟨htlower, htsorted⟩ := List.pairwise_cons.mp hsorted
      have htbound : ∀ index < rest.length, rest.getD index 0 ≤ north + 1 + index := by
        intro index hi
        have hh := hbound (index + 1) (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      obtain ⟨hu, hd, hp⟩ := ih value (north + 1) (by omega) htsorted htlower htbound
      have hsize : north + (value :: rest).length = north + 1 + rest.length := by
        simp; omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [dyckSteps, hsize, List.count_append, List.count_cons,
          List.count_replicate]
        simp [hu]
      · simp [dyckSteps, hsize] at *
        omega
      · intro index
        by_cases hi : index ≤ value - east
        · simp [dyckSteps, List.take_append, List.take_replicate,
            Nat.min_eq_left hi, Nat.sub_eq_zero_of_le hi]
          omega
        · have hlt : value - east < index := by omega
          have hpos : index - (value - east) =
              (index - (value - east) - 1) + 1 := by omega
          have hh := hp (index - (value - east) - 1)
          simp only [dyckSteps, hsize, List.take_append, List.take_replicate,
            List.length_replicate,
            Nat.min_eq_right (le_of_lt hlt)]
          rw [hpos, List.take_succ_cons]
          simp only [List.count_append, List.count_replicate, List.count_cons]
          simp at *
          omega
  have hdowns : ∀ count east : ℕ, ∀ steps : List DyckStep,
      eastCounts east (List.replicate count D ++ steps) = eastCounts (east + count) steps := by
    intro count
    induction count with
    | zero => intro east steps; simp
    | succ count ih =>
      intro east steps
      simpa [List.replicate_succ, eastCounts, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (east + 1) steps
  have hleft : ∀ word : List ℕ, ∀ size east : ℕ,
      word.Pairwise (· ≤ ·) → (∀ value ∈ word, east ≤ value) →
      eastCounts east (dyckSteps size east word) = word := by
    intro word
    induction word with
    | nil =>
      intro size east hsorted hlower
      simpa [dyckSteps, eastCounts] using hdowns (size - east) east []
    | cons value rest ih =>
      intro size east hsorted hlower
      have hev := hlower value (by simp)
      obtain ⟨htlower, htsorted⟩ := List.pairwise_cons.mp hsorted
      rw [dyckSteps, hdowns, Nat.add_sub_of_le hev, eastCounts,
        ih size value htsorted htlower]
  have hlower : ∀ steps : List DyckStep, ∀ east : ℕ,
      ∀ value ∈ eastCounts east steps, east ≤ value := by
    intro steps
    induction steps with
    | nil => simp [eastCounts]
    | cons step rest ih =>
      intro east value hv
      cases step with
      | U =>
        simp only [eastCounts, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact le_rfl
        · exact ih east value hv
      | D => exact (Nat.le_succ east).trans (ih (east + 1) value hv)
  have hshift (word : List ℕ) (size east : ℕ)
      (hs : east < size) (hl : ∀ value ∈ word, east + 1 ≤ value) :
      dyckSteps size east word = D :: dyckSteps size (east + 1) word := by
    cases word with
    | nil =>
      have hh : size - east = (size - (east + 1)) + 1 := by omega
      simp [dyckSteps, hh, List.replicate_succ]
    | cons value rest =>
      have hv := hl value (by simp)
      have hh : value - east = (value - (east + 1)) + 1 := by omega
      simp [dyckSteps, hh, List.replicate_succ]
  have hright : ∀ steps : List DyckStep, ∀ east : ℕ,
      dyckSteps (east + steps.count D) east (eastCounts east steps) = steps := by
    intro steps
    induction steps with
    | nil => intro east; simp [eastCounts, dyckSteps]
    | cons step rest ih =>
      intro east
      cases step with
      | U => simpa [eastCounts, dyckSteps] using congrArg (U :: ·) (ih east)
      | D =>
        have hs : east < east + (D :: rest).count D := by simp
        rw [eastCounts, hshift _ _ _ hs (hlower rest (east + 1))]
        have he : east + (D :: rest).count D = east + 1 + rest.count D := by
          simp; omega
        rw [he, ih]
  have hstop : ∀ suffix preceding : List DyckStep,
      (suffix ++ U :: preceding).takeWhile (· == D) = suffix.takeWhile (· == D) := by
    intro suffix
    induction suffix with
    | nil => intro preceding; simp
    | cons step rest ih =>
      intro preceding
      cases step <;> simp [ih]
  have hfinal : ∀ word : List ℕ, ∀ total east : ℕ,
      ((dyckSteps total east word).reverse.takeWhile (· == D)).length =
        total - word.getLastD east := by
    intro word
    induction word with
    | nil => intro total east; simp [dyckSteps]
    | cons value rest ih =>
      intro total east
      simpa only [dyckSteps, List.reverse_append, List.reverse_cons,
        List.reverse_replicate, List.append_assoc, List.singleton_append, hstop,
        List.getLastD_cons] using ih total value
  have hmaximum : ∀ word : List ℕ, ∀ east : ℕ,
      word.Pairwise (· ≤ ·) → (∀ value ∈ word, east ≤ value) →
      word.getLastD east = max east (word.foldr max 0) := by
    intro word
    induction word with
    | nil => intro east hsorted hlower; simp
    | cons value rest ih =>
      intro east hsorted hlower
      obtain ⟨htlower, htsorted⟩ := List.pairwise_cons.mp hsorted
      have hev : east ≤ value := hlower value (by simp)
      rw [List.getLastD_cons, ih value htsorted htlower, List.foldr_cons]
      exact (max_eq_right (hev.trans (le_max_left _ _))).symm
  have hruns : ∀ word : List ℕ, ∀ total east : ℕ,
      ((dyckSteps total east word).splitOn U).map List.length =
        List.zipWith (· - ·) word (east :: word) ++ [total - word.getLastD east] := by
    intro word
    induction word with
    | nil =>
      intro total east
      rw [dyckSteps, List.splitOn_eq_singleton (by simp)]
      simp
    | cons value rest ih =>
      intro total east
      rw [dyckSteps, List.splitOn_append_cons_self_of_not_mem (by simp)]
      simpa only [List.map_cons, List.length_replicate, List.zipWith_cons_cons,
        List.getLastD_cons, List.cons_append] using
          congrArg (fun lengths => (value - east) :: lengths) (ih total value)
  have hmaxBound : ∀ word : List ℕ, ∀ total : ℕ,
      0 < total → (∀ value ∈ word, value < total) → word.foldr max 0 < total := by
    intro word
    induction word with
    | nil => intro total hpos hbound; exact hpos
    | cons value rest ih =>
      intro total hpos hbound
      exact max_lt (hbound value (by simp))
        (ih total hpos (fun other hmem => hbound other (by simp [hmem])))
  let forward (word :
      {word : List ℕ // word.length = size ∧ InversionSeqDefs.IsInversionSeq word ∧
        word.Pairwise (· ≤ ·)}) : {path : DyckWord // path.semilength = size} := by
    refine ⟨⟨dyckSteps size 0 word.val, ?_, ?_⟩, ?_⟩
    · have hh := hwrite word.val 0 0 (by omega) word.property.2.2
        (by simp) (by simpa [InversionSeqDefs.IsInversionSeq] using word.property.2.1)
      rw [Nat.zero_add, word.property.1] at hh
      omega
    · have hh := hwrite word.val 0 0 (by omega) word.property.2.2
        (by simp) (by simpa [InversionSeqDefs.IsInversionSeq] using word.property.2.1)
      rw [Nat.zero_add, word.property.1] at hh
      simpa using hh.2.2
    · have hh := hwrite word.val 0 0 (by omega) word.property.2.2
        (by simp) (by simpa [InversionSeqDefs.IsInversionSeq] using word.property.2.1)
      rw [Nat.zero_add, word.property.1] at hh
      exact hh.1
  let backward (path : {path : DyckWord // path.semilength = size}) :
      {word : List ℕ // word.length = size ∧ InversionSeqDefs.IsInversionSeq word ∧
        word.Pairwise (· ≤ ·)} := by
    refine ⟨eastCounts 0 path.val.toList, ?_, ?_, ?_⟩
    · have hh := hread path.val.toList 0 0
        (by simpa using path.val.count_D_le_count_U)
      exact hh.1.trans path.property
    · have hh := hread path.val.toList 0 0
        (by simpa using path.val.count_D_le_count_U)
      simpa [InversionSeqDefs.IsInversionSeq] using hh.2.2.2
    · have hh := hread path.val.toList 0 0
        (by simpa using path.val.count_D_le_count_U)
      exact hh.2.1
  refine ⟨{
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro word
    apply Subtype.ext
    exact hleft word.val size 0 word.property.2.2 (by simp)
  · intro path
    apply Subtype.ext
    apply DyckWord.ext
    change dyckSteps size 0 (eastCounts 0 path.val.toList) = path.val.toList
    have hs : size = 0 + path.val.toList.count D := by
      simpa [DyckWord.semilength_eq_count_D] using path.property.symm
    calc
      dyckSteps size 0 (eastCounts 0 path.val.toList) =
          dyckSteps (0 + path.val.toList.count D) 0 (eastCounts 0 path.val.toList) :=
        congrArg (fun total => dyckSteps total 0 (eastCounts 0 path.val.toList)) hs
      _ = path.val.toList := hright path.val.toList 0
  · intro word; rfl
  · intro path; rfl
  · intro word
    change ((dyckSteps size 0 word.val).reverse.takeWhile (· == D)).length =
      size - word.val.foldr max 0
    rw [hfinal, hmaximum word.val 0 word.property.2.2 (by simp)]
    simp
  · intro word
    change ((((dyckSteps size 0 word.val).splitOn U).map List.length).filter
        (· != 0)).dropLast =
      (List.zipWith (· - ·) word.val (0 :: word.val)).filter (· != 0)
    rw [hruns, hmaximum word.val 0 word.property.2.2 (by simp)]
    simp only [Nat.zero_max, List.filter_append]
    by_cases hs : size = 0
    · have hw : word.val = [] := List.eq_nil_of_length_eq_zero (word.property.1.trans hs)
      simp [hw, hs]
    · have hv : ∀ value ∈ word.val, value < size := by
        intro value hmem
        obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hmem
        have hb := word.property.2.1 index hindex
        rw [List.getD_eq_getElem _ _ hindex] at hb
        have hi : index < size := by simpa [word.property.1] using hindex
        omega
      have hm := hmaxBound word.val size (by omega) hv
      have hn : size - word.val.foldr max 0 ≠ 0 := by omega
      simp [hn]

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck
