/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding
   mirror-E: none(waiver:filtered-value-partition-and-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Indexed letters biject with sorted value partitions and reconstruct permutations. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWords
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWordEncoding

open FishburnTenSevenWords FishburnTenSevenWords.Letter

def blocks {size : ℕ} (word : Fin size → Letter) : List ℕ × List ℕ × List ℕ :=
  let select (letter : Letter) :=
    ((List.finRange size).filter (fun index => decide (word index = letter))).map
      (fun index => index.val + 2)
  ((select d).reverse, select i, (select j).reverse)

def encodeBlocks {size : ℕ} (parts : List ℕ × List ℕ × List ℕ) : Fin size → Letter :=
  fun index => if index.val + 2 ∈ parts.1 then d
    else if index.val + 2 ∈ parts.2.1 then i else j

def reconstruct {size : ℕ} (total : ℕ) (word : Fin size → Letter) : List ℕ :=
  let parts := blocks word
  (List.range' (size + 3) (total - (size + 2))).reverse ++ parts.1 ++
    1 :: (parts.2.1 ++ (size + 2) :: parts.2.2)

def encodePermutation {size : ℕ} (permutation : List ℕ) : Fin size → Letter :=
  fun index => if index.val + 2 ∈ permutation.takeWhile (fun value => value != 1) then d
    else if index.val + 2 ∈
      (permutation.dropWhile (fun value => value != 1)).tail.takeWhile
        (fun value => value != size + 2) then i else j

theorem block_bijection (size : ℕ) :
    ∃ correspondence : (Fin size → Letter) ≃
        {parts : List ℕ × List ℕ × List ℕ //
          parts.1.Pairwise (· > ·) ∧ parts.2.1.Pairwise (· < ·) ∧
          parts.2.2.Pairwise (· > ·) ∧
          (parts.1 ++ (parts.2.1 ++ parts.2.2)).Perm (List.range' 2 size)},
      (∀ word, (correspondence word).val = blocks word) ∧
      (∀ parts, correspondence.symm parts = encodeBlocks parts.val) := by
  let select (word : Fin size → Letter) (letter : Letter) :=
    ((List.finRange size).filter (fun index => decide (word index = letter))).map
      (fun index => index.val + 2)
  let component (parts : List ℕ × List ℕ × List ℕ) (letter : Letter) :=
    match letter with
    | d => parts.1
    | i => parts.2.1
    | j => parts.2.2
  have hmem (word : Fin size → Letter) (letter : Letter) (value : ℕ) :
      value ∈ component (blocks word) letter ↔
        ∃ index : Fin size, word index = letter ∧ index.val + 2 = value := by
    cases letter <;> simp [component, blocks]
  have hmem_index (word : Fin size → Letter) (letter : Letter) (index : Fin size) :
      index.val + 2 ∈ component (blocks word) letter ↔ word index = letter := by
    rw [hmem]
    constructor
    · rintro ⟨other, hletter, heq⟩
      have hsame : other = index := Fin.ext (by omega)
      simpa only [hsame] using hletter
    · intro hletter
      exact ⟨index, hletter, rfl⟩
  have hrange : List.ofFn (fun index : Fin size => index.val + 2) =
      List.range' 2 size := by
    apply List.ext_getElem (by simp)
    intro index hleft hright
    simp [Nat.add_comm]
  have hselect_sorted (word : Fin size → Letter) (letter : Letter) :
      (select word letter).Pairwise (· < ·) := by
    have hsorted : (List.ofFn (fun index : Fin size => index.val + 2)).Pairwise (· < ·) :=
      List.pairwise_ofFn.mpr (fun _ _ hlt => by omega)
    rw [List.ofFn_eq_map, List.pairwise_map] at hsorted
    exact (hsorted.filter _).map _ (fun _ _ hlt => hlt)
  have hpartition (word : Fin size → Letter) (indices : List (Fin size)) :
      ((indices.filter (fun index => decide (word index = d))) ++
        ((indices.filter (fun index => decide (word index = i))) ++
          (indices.filter (fun index => decide (word index = j))))).Perm indices := by
    induction indices with
    | nil => simp
    | cons index tail ih =>
      cases hletter : word index with
      | d => simpa [hletter] using ih.cons index
      | i =>
        simp only [List.filter_cons, hletter, reduceCtorEq, decide_true, decide_false,
          Bool.false_eq_true, if_false, if_true]
        simpa only [List.cons_append] using List.perm_middle.trans (ih.cons index)
      | j =>
        simp only [List.filter_cons, hletter, reduceCtorEq, decide_true, decide_false,
          Bool.false_eq_true, if_false, if_true]
        apply List.Perm.trans _ (ih.cons index)
        simpa only [List.append_assoc] using
          (List.perm_middle (a := index)
            (l₁ := tail.filter (fun index => decide (word index = d)) ++
              tail.filter (fun index => decide (word index = i)))
            (l₂ := tail.filter (fun index => decide (word index = j))))
  have hcorrect (word : Fin size → Letter) :
      (blocks word).1.Pairwise (· > ·) ∧ (blocks word).2.1.Pairwise (· < ·) ∧
      (blocks word).2.2.Pairwise (· > ·) ∧
      ((blocks word).1 ++ ((blocks word).2.1 ++ (blocks word).2.2)).Perm
        (List.range' 2 size) := by
    refine ⟨List.pairwise_reverse.mpr (hselect_sorted word d),
      hselect_sorted word i, List.pairwise_reverse.mpr (hselect_sorted word j), ?_⟩
    have hperm := (hpartition word (List.finRange size)).map
      (fun index => index.val + 2)
    simp only [List.map_append, ← List.ofFn_eq_map, hrange] at hperm
    exact ((List.reverse_perm (select word d)).append
      ((List.Perm.refl (select word i)).append (List.reverse_perm (select word j)))).trans hperm
  have hleft (word : Fin size → Letter) : encodeBlocks (blocks word) = word := by
    funext index
    have hd := hmem_index word d index
    have hi := hmem_index word i index
    cases hletter : word index <;> simp [encodeBlocks, component, hd, hi, hletter]
  have hright (parts : List ℕ × List ℕ × List ℕ)
      (hparts : parts.1.Pairwise (· > ·) ∧ parts.2.1.Pairwise (· < ·) ∧
        parts.2.2.Pairwise (· > ·) ∧
        (parts.1 ++ (parts.2.1 ++ parts.2.2)).Perm (List.range' 2 size)) :
      blocks (encodeBlocks (size := size) parts) = parts := by
    have hperm := hparts.2.2.2
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    obtain ⟨_, hrest, hdrest⟩ := List.nodup_append.mp hnodup
    obtain ⟨_, _, hij⟩ := List.nodup_append.mp hrest
    have hdecode (index : Fin size) (letter : Letter) :
        encodeBlocks parts index = letter ↔ index.val + 2 ∈ component parts letter := by
      have hvalue : index.val + 2 ∈ parts.1 ++ (parts.2.1 ++ parts.2.2) := by
        apply hperm.mem_iff.mpr
        exact List.mem_range'.mpr ⟨index.val, index.isLt, by simp [Nat.add_comm]⟩
      by_cases hd : index.val + 2 ∈ parts.1
      · have hi : index.val + 2 ∉ parts.2.1 :=
          fun hmem => hdrest _ hd _ (List.mem_append_left _ hmem) rfl
        have hj : index.val + 2 ∉ parts.2.2 :=
          fun hmem => hdrest _ hd _ (List.mem_append_right _ hmem) rfl
        cases letter <;> simp [encodeBlocks, component, hd, hi, hj]
      · by_cases hi : index.val + 2 ∈ parts.2.1
        · have hj : index.val + 2 ∉ parts.2.2 := fun hmem => hij _ hi _ hmem rfl
          cases letter <;> simp [encodeBlocks, component, hd, hi, hj]
        · have hj : index.val + 2 ∈ parts.2.2 := by
            simpa only [List.mem_append, hd, hi, false_or] using hvalue
          cases letter <;> simp [encodeBlocks, component, hd, hi, hj]
    have hmembers (letter : Letter) (value : ℕ) :
        value ∈ component (blocks (encodeBlocks (size := size) parts)) letter ↔
          value ∈ component parts letter := by
      rw [hmem]
      constructor
      · rintro ⟨index, hletter, rfl⟩
        exact (hdecode index letter).mp hletter
      · intro hmem_part
        have hmem_all : value ∈ parts.1 ++ (parts.2.1 ++ parts.2.2) := by
          cases letter <;> simp_all [component]
        obtain ⟨index, hbound, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hmem_all)
        refine ⟨⟨index, hbound⟩, (hdecode ⟨index, hbound⟩ letter).mpr ?_, ?_⟩
        · simpa [hvalue, Nat.add_comm] using hmem_part
        · simpa [Nat.add_comm] using hvalue.symm
    have hsorted := hcorrect (encodeBlocks parts)
    exact Prod.ext (hsorted.1.eq_of_mem_iff hparts.1 (hmembers d))
      (Prod.ext (hsorted.2.1.eq_of_mem_iff hparts.2.1 (hmembers i))
        (hsorted.2.2.1.eq_of_mem_iff hparts.2.2.1 (hmembers j)))
  exact ⟨{
    toFun := fun word => ⟨blocks word, hcorrect word⟩
    invFun := fun parts => encodeBlocks parts.val
    left_inv := hleft
    right_inv := fun parts => Subtype.ext (hright parts.val parts.property) },
    fun _ => rfl, fun _ => rfl⟩

theorem reconstruct_permutation (total size : ℕ) (htotal : size + 2 ≤ total) :
    Function.LeftInverse (encodePermutation (size := size)) (reconstruct total) ∧
    ∀ word : Fin size → Letter,
      let parts := blocks word
      let decreasing := (List.range' (size + 3) (total - (size + 2))).reverse ++ parts.1
      (reconstruct total word).Perm (List.range' 1 total) ∧
      decreasing.Pairwise (· > ·) ∧ parts.2.1.Pairwise (· < ·) ∧
      parts.2.2.Pairwise (· > ·) ∧
      ∀ value ∈ parts.2.1 ++ parts.2.2, 1 < value ∧ value < size + 2 := by
  obtain ⟨correspondence, hforward, hbackward⟩ := block_bijection size
  let upper := List.range' (size + 3) (total - (size + 2))
  have hparts (word : Fin size → Letter) :
      (blocks word).1.Pairwise (· > ·) ∧ (blocks word).2.1.Pairwise (· < ·) ∧
      (blocks word).2.2.Pairwise (· > ·) ∧
      ((blocks word).1 ++ ((blocks word).2.1 ++ (blocks word).2.2)).Perm
        (List.range' 2 size) := by
    simpa only [hforward] using (correspondence word).property
  have hleft (word : Fin size → Letter) : encodeBlocks (blocks word) = word := by
    simpa only [hbackward, hforward] using correspondence.symm_apply_apply word
  have hsmall (word : Fin size → Letter) (value : ℕ)
      (hvalue : value ∈ (blocks word).1 ++ ((blocks word).2.1 ++ (blocks word).2.2)) :
      1 < value ∧ value < size + 2 := by
    obtain ⟨index, hindex, heq⟩ :=
      List.mem_range'.mp ((hparts word).2.2.2.mem_iff.mp hvalue)
    omega
  have hupper (value : ℕ) (hvalue : value ∈ upper.reverse) : size + 3 ≤ value := by
    obtain ⟨index, _, heq⟩ := List.mem_range'.mp (List.mem_reverse.mp hvalue)
    omega
  constructor
  · intro word
    let parts := blocks word
    have hprefix (value : ℕ) (hvalue : value ∈ upper.reverse ++ parts.1) :
        (value != 1) = true := by
      rcases List.mem_append.mp hvalue with hlarge | hlow
      · have hbound := hupper value hlarge
        simp only [bne_iff_ne]
        omega
      · have hbound := hsmall word value (List.mem_append_left _ hlow)
        simp only [bne_iff_ne]
        omega
    have hincreasing (value : ℕ) (hvalue : value ∈ parts.2.1) :
        (value != size + 2) = true := by
      have hbound := hsmall word value
        (List.mem_append_right _ (List.mem_append_left _ hvalue))
      simp only [bne_iff_ne]
      omega
    have htake : (reconstruct total word).takeWhile (fun value => value != 1) =
        upper.reverse ++ parts.1 := by
      change ((upper.reverse ++ parts.1) ++
        1 :: (parts.2.1 ++ (size + 2) :: parts.2.2)).takeWhile _ = _
      rw [List.takeWhile_append_of_pos hprefix]
      simp
    have hdrop : (reconstruct total word).dropWhile (fun value => value != 1) =
        1 :: (parts.2.1 ++ (size + 2) :: parts.2.2) := by
      change ((upper.reverse ++ parts.1) ++
        1 :: (parts.2.1 ++ (size + 2) :: parts.2.2)).dropWhile _ = _
      rw [List.dropWhile_append_of_pos hprefix]
      simp
    have htake_increasing :
        (parts.2.1 ++ (size + 2) :: parts.2.2).takeWhile
          (fun value => value != size + 2) = parts.2.1 := by
      rw [List.takeWhile_append_of_pos hincreasing]
      simp
    funext index
    have hnot_upper : index.val + 2 ∉ upper.reverse := by
      intro hvalue
      have hbound := hupper _ hvalue
      omega
    simp only [encodePermutation, htake, hdrop, List.tail_cons, htake_increasing,
      List.mem_append, hnot_upper, false_or]
    exact congrFun (hleft word) index
  · intro word
    let parts := blocks word
    have hpeak :
        (parts.1 ++ (parts.2.1 ++ (size + 2) :: parts.2.2)).Perm
          ((parts.1 ++ (parts.2.1 ++ parts.2.2)) ++ [size + 2]) := by
      have hmove : (parts.1 ++ (parts.2.1 ++ (size + 2) :: parts.2.2)).Perm
          ((size + 2) :: (parts.1 ++ (parts.2.1 ++ parts.2.2))) := by
        simpa only [List.append_assoc] using
          (List.perm_middle (a := size + 2) (l₁ := parts.1 ++ parts.2.1) (l₂ := parts.2.2))
      exact hmove.trans (by simpa using
        (List.perm_append_comm (l₁ := [size + 2])
          (l₂ := parts.1 ++ (parts.2.1 ++ parts.2.2))))
    have hcore : (parts.1 ++ 1 :: (parts.2.1 ++ (size + 2) :: parts.2.2)).Perm
        (1 :: ((parts.1 ++ (parts.2.1 ++ parts.2.2)) ++ [size + 2])) :=
      List.perm_middle.trans (hpeak.cons 1)
    have hwhole : (reconstruct total word).Perm
        (1 :: ((parts.1 ++ (parts.2.1 ++ parts.2.2)) ++ (size + 2) :: upper)) := by
      have hperm := ((List.reverse_perm upper).append hcore).trans
        (List.perm_append_comm (l₁ := upper)
          (l₂ := 1 :: ((parts.1 ++ (parts.2.1 ++ parts.2.2)) ++ [size + 2])))
      simpa only [reconstruct, upper, parts, List.append_assoc, List.cons_append,
        List.singleton_append, List.nil_append] using hperm
    have hconcat : List.range' 2 size ++
        List.range' (size + 2) ((total - (size + 2)) + 1) =
          List.range' 2 (size + ((total - (size + 2)) + 1)) := by
      simpa [Nat.add_comm] using
        (List.range'_append (s := 2) (m := size) (n := (total - (size + 2)) + 1) (step := 1))
    have htail : List.range' (size + 2) ((total - (size + 2)) + 1) =
        (size + 2) :: upper := by
      rw [List.range'_succ]
    have hlength : total = (size + ((total - (size + 2)) + 1)) + 1 := by omega
    have hall : List.range' 1 total =
        1 :: List.range' 2 (size + ((total - (size + 2)) + 1)) := by
      conv_lhs => rw [hlength, List.range'_succ]
    have hrange : 1 :: (List.range' 2 size ++ (size + 2) :: upper) =
        List.range' 1 total := by
      rw [← htail, hconcat, ← hall]
    have hpermutation : (reconstruct total word).Perm (List.range' 1 total) := by
      apply hwhole.trans
      rw [← hrange]
      exact ((hparts word).2.2.2.append (List.Perm.refl ((size + 2) :: upper))).cons 1
    have hsorted_upper : upper.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro left right hleft hright hlt
      simp only [upper, List.getElem_range']
      omega
    refine ⟨hpermutation, ?_, (hparts word).2.1, (hparts word).2.2.1, ?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨List.pairwise_reverse.mpr hsorted_upper, (hparts word).1, ?_⟩
      intro larger hlarger smaller hsmaller
      have hlarge := hupper larger hlarger
      have hlow := hsmall word smaller (List.mem_append_left _ hsmaller)
      omega
    · intro value hvalue
      exact hsmall word value (List.mem_append_right _ hvalue)

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWordEncoding
