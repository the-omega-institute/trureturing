/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts
   mirror-E: none(waiver:minimum-rooted-circular-enumeration)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Deleting the least entry reduces circular avoidance to three linear classes. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import D5.S3.Combinatorics.ArcherCyclicPadovanPatterns
import D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCounts

open D5.S3.Combinatorics
open RotationAvoidanceDefs RotationAvoidanceCircular Nonnesting.NonnestingDefs

theorem minimum_rooted_reductions (n : ℕ) (tail : List ℕ)
    (hp : (1 :: tail).Perm (List.range' 1 (n + 1))) :
    ((1 :: tail) ∈ circularAvoiders (n + 1) [1, 2, 3, 4] ↔
      ¬ Occurs [1, 2, 3] tail ∧ ¬ Occurs [3, 4, 1, 2] tail) ∧
    ((1 :: tail) ∈ circularAvoiders (n + 1) [1, 3, 4, 2] ↔
      ¬ Occurs [2, 3, 1] tail ∧ ¬ Occurs [2, 1, 3, 4] tail ∧
        ¬ Occurs [4, 2, 1, 3] tail) ∧
    ((1 :: tail) ∈ circularAvoiders (n + 1) [1, 3, 2, 4] ↔
      ¬ Occurs [2, 1, 3] tail ∧ ¬ Occurs [4, 1, 3, 2] tail) := by
  have hleast : ∀ value ∈ tail, 1 < value := by
    have hnodup := hp.nodup_iff.mpr (List.nodup_range' (s := 1) (n := n + 1))
    intro value hvalue
    have hbound := hp.mem_iff.mp (List.mem_cons_of_mem 1 hvalue)
    have hne : value ≠ 1 := by
      intro heq
      exact (List.nodup_cons.mp hnodup).1 (heq ▸ hvalue)
    simp only [List.mem_range'] at hbound
    omega
  have letters_three (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3]) :
      letters pattern = 3 := by
    simpa [letters] using hpattern.foldr_eq (f := max) 0
  have letters_four (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3, 4]) :
      letters pattern = 4 := by
    simpa [letters] using hpattern.foldr_eq (f := max) 0
  have build (pattern word : List ℕ) (size : ℕ) (hletters : letters pattern = size)
      (hranks : ∀ rank, 1 ≤ rank → rank ≤ size → rank ∈ pattern)
      (witness : ℕ → ℕ)
      (hincreasing : ∀ rank, 1 ≤ rank → rank < size →
        witness rank < witness (rank + 1))
      (hsub : (pattern.map witness).Sublist word) : Occurs pattern word := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa [hletters] using hincreasing
    · intro rank hlow hhigh
      rw [hletters] at hhigh
      exact hsub.subset (List.mem_map_of_mem (hranks rank hlow hhigh))
  have ranks_three (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3])
      (rank : ℕ) (hlow : 1 ≤ rank) (hhigh : rank ≤ 3) : rank ∈ pattern := by
    apply hpattern.mem_iff.mpr
    have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  have ranks_four (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3, 4])
      (rank : ℕ) (hlow : 1 ≤ rank) (hhigh : rank ≤ 4) : rank ∈ pattern := by
    apply hpattern.mem_iff.mpr
    have : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp
  have tail_to_cons (pattern : List ℕ) :
      Occurs pattern tail → Occurs pattern (1 :: tail) := by
    rintro ⟨witness, hincreasing, hmem, hsub, _⟩
    exact ⟨witness, hincreasing, fun rank hlo hhi =>
      List.mem_cons_of_mem 1 (hmem rank hlo hhi), hsub.cons 1, by simp⟩
  have nonminimum_head (first : ℕ) (rest : List ℕ)
      (hpattern : (first :: rest).Perm [1, 2, 3, 4]) (hfirst : 1 < first) :
      Occurs (first :: rest) (1 :: tail) ↔ Occurs (first :: rest) tail := by
    constructor
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have hincreasing' : ∀ rank, 1 ≤ rank → rank < 4 →
          witness rank < witness (rank + 1) := by
        simpa [letters_four _ hpattern] using hincreasing
      have hfirstBound : first ≤ 4 := by
        have := hpattern.mem_iff.mp (List.mem_cons_self : first ∈ first :: rest)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega
      have hfirstNe : witness first ≠ 1 := by
        intro heq
        have hpositive : 1 ≤ witness 1 := by
          have hmemOne := hmem 1 (by omega) (by rw [letters_four _ hpattern]; omega)
          rcases List.mem_cons.mp hmemOne with heqOne | htail
          · omega
          · have := hleast _ htail
            omega
        have h12 := hincreasing' 1 (by omega) (by omega)
        have h23 := hincreasing' 2 (by omega) (by omega)
        have h34 := hincreasing' 3 (by omega) (by omega)
        norm_num only at h12 h23 h34
        have : first = 2 ∨ first = 3 ∨ first = 4 := by omega
        rcases this with rfl | rfl | rfl <;> omega
      have hsub' : ((first :: rest).map witness).Sublist tail :=
        List.Sublist.of_cons_of_ne hfirstNe hsub
      exact build _ tail 4 (letters_four _ hpattern) (ranks_four _ hpattern)
        witness hincreasing' hsub'
    · exact tail_to_cons _
  have rooted (triple : List ℕ) (htriple : triple.Perm [1, 2, 3]) :
      Occurs (1 :: triple.map Nat.succ) (1 :: tail) ↔ Occurs triple tail := by
    have hpattern : (1 :: triple.map Nat.succ).Perm [1, 2, 3, 4] := by
      simpa using (htriple.map Nat.succ).cons 1
    constructor
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have hincreasing' : ∀ rank, 1 ≤ rank → rank < 4 →
          witness rank < witness (rank + 1) := by
        simpa [letters_four _ hpattern] using hincreasing
      have hselected : (triple.map (fun rank => witness (rank + 1))).Sublist tail := by
        simpa [List.map_map, Function.comp_def] using hsub.of_cons_cons
      exact build triple tail 3 (letters_three _ htriple) (ranks_three _ htriple)
        (fun rank => witness (rank + 1)) (by
          intro rank hlow hhigh
          exact hincreasing' (rank + 1) (by omega) (by omega)) hselected
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      let enlarged : ℕ → ℕ := fun rank => if rank = 1 then 1 else witness (rank - 1)
      have hbound : 1 < witness 1 :=
        hleast _ (hmem 1 (by omega) (by rw [letters_three _ htriple]; omega))
      have hincreasing' : ∀ rank, 1 ≤ rank → rank < 3 →
          witness rank < witness (rank + 1) := by
        simpa [letters_three _ htriple] using hincreasing
      apply build _ _ 4 (letters_four _ hpattern) (ranks_four _ hpattern) enlarged
      · intro rank hlow hhigh
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl
        · simpa [enlarged] using hbound
        · simpa [enlarged] using hincreasing' 1 (by omega) (by omega)
        · simpa [enlarged] using hincreasing' 2 (by omega) (by omega)
      · have hmap : (triple.map Nat.succ).map enlarged = triple.map witness := by
          rw [List.map_map]
          apply List.map_congr_left
          intro rank hrank
          have : 1 ≤ rank := by
            have := htriple.mem_iff.mp hrank
            simp only [List.mem_cons, List.not_mem_nil, or_false] at this
            omega
          simp [enlarged, Nat.succ_eq_add_one]
          omega
        simpa [enlarged, hmap] using hsub.cons_cons 1
  have extract_low (pattern triple word : List ℕ)
      (hpattern : pattern.Perm [1, 2, 3, 4]) (htriple : triple.Perm [1, 2, 3])
      (hselected : triple.Sublist pattern) : Occurs pattern word → Occurs triple word := by
    rintro ⟨witness, hincreasing, _, hsub, _⟩
    apply build _ _ 3 (letters_three _ htriple) (ranks_three _ htriple) witness
    · intro rank hlow hhigh
      apply hincreasing rank hlow
      rw [letters_four _ hpattern]
      omega
    · exact (hselected.map witness).trans hsub
  have extract_high (pattern triple word : List ℕ)
      (hpattern : pattern.Perm [1, 2, 3, 4]) (htriple : triple.Perm [1, 2, 3])
      (hselected : (triple.map Nat.succ).Sublist pattern) :
      Occurs pattern word → Occurs triple word := by
    rintro ⟨witness, hincreasing, _, hsub, _⟩
    apply build _ _ 3 (letters_three _ htriple) (ranks_three _ htriple)
      (fun rank => witness (rank + 1))
    · intro rank hlow hhigh
      apply hincreasing (rank + 1) (by omega)
      rw [letters_four _ hpattern]
      omega
    · simpa [List.map_map, Function.comp_def] using (hselected.map witness).trans hsub
  have circular (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3, 4]) :
      (1 :: tail) ∈ circularAvoiders (n + 1) pattern ↔
        ∀ shift < 4, ¬ Occurs (pattern.rotate shift) (1 :: tail) := by
    simp only [circularAvoiders, Set.mem_ofPred_eq, List.head?_cons, and_true]
    exact all_cuts_iff_cycle_avoidance (n + 1) (by omega) pattern (1 :: tail) hpattern hp
  have root123 := rooted [1, 2, 3] (by rfl)
  have root231 := rooted [2, 3, 1] (by decide)
  have root213 := rooted [2, 1, 3] (by decide)
  simp only [List.map_cons, List.map_nil, Nat.succ_eq_add_one] at root123 root231 root213
  have tail3412 := nonminimum_head 3 [4, 1, 2] (by decide) (by omega)
  have tail2134 := nonminimum_head 2 [1, 3, 4] (by decide) (by omega)
  have tail4213 := nonminimum_head 4 [2, 1, 3] (by decide) (by omega)
  have tail4132 := nonminimum_head 4 [1, 3, 2] (by decide) (by omega)
  have excludes (triple pattern : List ℕ) (htriple : triple.Perm [1, 2, 3])
      (hpattern : pattern.Perm [1, 2, 3, 4]) (hfirst : 1 < pattern.headD 0)
      (hextract : Occurs pattern tail → Occurs triple tail)
      (havoid : ¬ Occurs triple tail) : ¬ Occurs pattern (1 :: tail) := by
    cases pattern with
    | nil => simp at hpattern
    | cons first rest =>
      exact fun hocc => havoid (hextract ((nonminimum_head first rest hpattern hfirst).mp
        hocc))
  refine ⟨?_, ?_, ?_⟩
  · rw [circular [1, 2, 3, 4] (by rfl)]
    constructor
    · intro havoid
      exact ⟨fun hocc => havoid 0 (by omega) (root123.mpr hocc),
        fun hocc => havoid 2 (by omega) (by simpa using tail3412.mpr hocc)⟩
    · rintro ⟨h123, h3412⟩ shift hshift
      have : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa using fun hocc => h123 (root123.mp hocc)
      · apply excludes [1, 2, 3] [2, 3, 4, 1] (by rfl) (by decide) (by decide) _ h123
        exact extract_high _ _ _ (by decide) (by rfl) (by decide)
      · simpa using fun hocc => h3412 (tail3412.mp hocc)
      · apply excludes [1, 2, 3] [4, 1, 2, 3] (by rfl) (by decide) (by decide) _ h123
        exact extract_low _ _ _ (by decide) (by rfl) (by decide)
  · rw [circular [1, 3, 4, 2] (by decide)]
    constructor
    · intro havoid
      exact ⟨fun hocc => havoid 0 (by omega) (root231.mpr hocc),
        fun hocc => havoid 3 (by omega) (by simpa using tail2134.mpr hocc),
        fun hocc => havoid 2 (by omega) (by simpa using tail4213.mpr hocc)⟩
    · rintro ⟨h231, h2134, h4213⟩ shift hshift
      have : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa using fun hocc => h231 (root231.mp hocc)
      · apply excludes [2, 3, 1] [3, 4, 2, 1] (by decide) (by decide) (by decide) _ h231
        exact extract_high _ _ _ (by decide) (by decide) (by decide)
      · simpa using fun hocc => h4213 (tail4213.mp hocc)
      · simpa using fun hocc => h2134 (tail2134.mp hocc)
  · rw [circular [1, 3, 2, 4] (by decide)]
    constructor
    · intro havoid
      exact ⟨fun hocc => havoid 0 (by omega) (root213.mpr hocc),
        fun hocc => havoid 3 (by omega) (by simpa using tail4132.mpr hocc)⟩
    · rintro ⟨h213, h4132⟩ shift hshift
      have : shift = 0 ∨ shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa using fun hocc => h213 (root213.mp hocc)
      · apply excludes [2, 1, 3] [3, 2, 4, 1] (by decide) (by decide) (by decide) _ h213
        exact extract_high _ _ _ (by decide) (by decide) (by decide)
      · apply excludes [2, 1, 3] [2, 4, 1, 3] (by decide) (by decide) (by decide) _ h213
        exact extract_low _ _ _ (by decide) (by decide) (by decide)
      · simpa using fun hocc => h4132 (tail4132.mp hocc)

theorem binary_extreme_count (n : ℕ) (hn : 1 ≤ n) :
    (Fishburn.FishburnClassicalDefs.classicalAvoiders n
      [[2, 1, 3], [2, 3, 1]]).ncard = 2 ^ (n - 1) := by
  classical
  let words := fun size => Fishburn.FishburnClassicalDefs.classicalAvoiders size
    [[2, 1, 3], [2, 3, 1]]
  have membership (size : ℕ) (word : List ℕ) : word ∈ words size ↔
      word.Perm (List.range' 1 size) ∧
        ¬ Occurs [2, 1, 3] word ∧ ¬ Occurs [2, 3, 1] word := by
    simp [words, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have inherited (pattern word : List ℕ) (first : ℕ) :
      Occurs pattern word → Occurs pattern (first :: word) := by
    rintro ⟨witness, hincreasing, hmem, hsub, _⟩
    exact ⟨witness, hincreasing, fun rank hlo hhi =>
      List.mem_cons_of_mem first (hmem rank hlo hhi), hsub.cons first, by simp⟩
  have ordered_pair (word : List ℕ) (low high : ℕ)
      (hlow : low ∈ word) (hhigh : high ∈ word) (hne : low ≠ high) :
      [low, high].Sublist word ∨ [high, low].Sublist word := by
    induction word with
    | nil => simp at hlow
    | cons first rest ih =>
      by_cases hfirstLow : first = low
      · subst first
        left
        apply List.Sublist.cons_cons
        apply List.singleton_sublist.mpr
        exact (List.mem_cons.mp hhigh).resolve_left (Ne.symm hne)
      · by_cases hfirstHigh : first = high
        · subst first
          right
          apply List.Sublist.cons_cons
          apply List.singleton_sublist.mpr
          exact (List.mem_cons.mp hlow).resolve_left hne
        · have hlowTail := (List.mem_cons.mp hlow).resolve_left (Ne.symm hfirstLow)
          have hhighTail := (List.mem_cons.mp hhigh).resolve_left (Ne.symm hfirstHigh)
          exact (ih hlowTail hhighTail).imp (fun h => h.cons first) (fun h => h.cons first)
  have make_pattern (pattern word : List ℕ) (hpattern : pattern.Perm [1, 2, 3])
      (low middle high : ℕ) (hlm : low < middle) (hmh : middle < high)
      (hsub : (pattern.map (fun rank =>
        if rank = 1 then low else if rank = 2 then middle else high)).Sublist word) :
      Occurs pattern word := by
    have hletters : letters pattern = 3 := by
      simpa [letters] using hpattern.foldr_eq (f := max) 0
    let witness := fun rank => if rank = 1 then low else if rank = 2 then middle else high
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · intro rank hlow hhigh
      rw [hletters] at hhigh
      have : rank = 1 ∨ rank = 2 := by omega
      rcases this with rfl | rfl <;> simp [witness] <;> omega
    · intro rank hlow hhigh
      rw [hletters] at hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hpattern.mem_iff.mpr
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl <;> simp
  have avoid_extreme (first : ℕ) (word : List ℕ)
      (hextreme : (∀ value ∈ word, first < value) ∨ (∀ value ∈ word, value < first))
      (h213 : ¬ Occurs [2, 1, 3] word) (h231 : ¬ Occurs [2, 3, 1] word) :
      ¬ Occurs [2, 1, 3] (first :: word) ∧ ¬ Occurs [2, 3, 1] (first :: word) := by
    have remove (rest : List ℕ) (hpattern : (2 :: rest).Perm [1, 2, 3]) :
        Occurs (2 :: rest) (first :: word) → Occurs (2 :: rest) word := by
      rintro ⟨witness, hincreasing, _, hsub, _⟩
      have hletters : letters (2 :: rest) = 3 := by
        simpa [letters] using hpattern.foldr_eq (f := max) 0
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by rw [hletters]; omega)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by rw [hletters]; omega)
      have hne : witness 2 ≠ first := by
        intro heq
        have htail := hsub.of_cons_cons
        have hlow : witness 1 ∈ word := by
          apply htail.subset
          apply List.mem_map_of_mem
          have hrank := hpattern.mem_iff.mpr (by simp : 1 ∈ [1, 2, 3])
          simpa using hrank
        have hhigh : witness 3 ∈ word := by
          apply htail.subset
          apply List.mem_map_of_mem
          have hrank := hpattern.mem_iff.mpr (by simp : 3 ∈ [1, 2, 3])
          simpa using hrank
        rcases hextreme with hleast | hgreatest
        · have := hleast _ hlow
          omega
        · have := hgreatest _ hhigh
          omega
      have hsub' : ((2 :: rest).map witness).Sublist word :=
        List.Sublist.of_cons_of_ne hne hsub
      refine ⟨witness, hincreasing, ?_, hsub', by simp⟩
      intro rank hlow hhigh
      rw [hletters] at hhigh
      apply hsub'.subset
      apply List.mem_map_of_mem
      apply hpattern.mem_iff.mpr
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl <;> simp
    exact ⟨fun hocc => h213 (remove [1, 3] (by decide) hocc),
      fun hocc => h231 (remove [3, 1] (by decide) hocc)⟩
  have shift (word pattern : List ℕ) (hpattern : pattern ∈ [[2, 1, 3], [2, 3, 1]]) :
      Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
    have hletters : letters pattern = pattern.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl
    unfold Occurs
    rw [hletters]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word Nat.succ
      (by intro left right hlt; omega)
  have finite_words (size : ℕ) : (words size).Finite := by
    apply (List.finite_toSet ((List.range' 1 size).permutations)).subset
    intro word hword
    exact List.mem_permutations.mpr ((membership size word).mp hword).1
  have recurrence (size : ℕ) (hsize : 1 ≤ size) :
      (words (size + 1)).ncard = 2 * (words size).ncard := by
    let lowInsert : List ℕ → List ℕ := fun word => 1 :: word.map Nat.succ
    let highInsert : List ℕ → List ℕ := List.cons (size + 1)
    have highPerm : ((size + 1) :: List.range' 1 size).Perm (List.range' 1 (size + 1)) := by
      have hsplit := List.range'_append_1 (s := 1) (m := size) (n := 1)
      have heq : List.range' 1 size ++ [size + 1] = List.range' 1 (size + 1) := by
        simpa [Nat.add_comm] using hsplit
      simpa using (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size)).trans
        (List.Perm.of_eq heq)
    have lowPerm : (1 :: (List.range' 1 size).map Nat.succ) =
        List.range' 1 (size + 1) := by
      have hsucc : Nat.succ = (fun value => 1 + value) := by funext value; omega
      rw [hsucc]
      rw [List.map_add_range']
      simp [List.range'_succ]
    have highMember (word : List ℕ) (hword : word ∈ words size) :
        highInsert word ∈ words (size + 1) := by
      obtain ⟨hperm, h213, h231⟩ := (membership size word).mp hword
      apply (membership _ _).mpr
      refine ⟨(hperm.cons (size + 1)).trans highPerm, ?_⟩
      apply avoid_extreme (size + 1) word (Or.inr ?_) h213 h231
      intro value hvalue
      have := hperm.mem_iff.mp hvalue
      simp only [List.mem_range'] at this
      omega
    have lowMember (word : List ℕ) (hword : word ∈ words size) :
        lowInsert word ∈ words (size + 1) := by
      obtain ⟨hperm, h213, h231⟩ := (membership size word).mp hword
      apply (membership _ _).mpr
      refine ⟨by simpa [lowPerm] using (hperm.map Nat.succ).cons 1, ?_⟩
      apply avoid_extreme 1 (word.map Nat.succ) (Or.inl ?_)
        (fun hocc => h213 ((shift word _ (by simp)).mp hocc))
        (fun hocc => h231 ((shift word _ (by simp)).mp hocc))
      intro value hvalue
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hvalue
      have := hperm.mem_iff.mp hold
      simp only [List.mem_range'] at this
      omega
    have split : words (size + 1) = lowInsert '' words size ∪ highInsert '' words size := by
      ext word
      constructor
      · intro hword
        obtain ⟨hperm, h213, h231⟩ := (membership _ _).mp hword
        cases word with
        | nil => have := hperm.length_eq; simp at this
        | cons first rest =>
          have hfirst : first = 1 ∨ first = size + 1 := by
            by_contra hnot
            have hfirstLow : first ≠ 1 := fun heq => hnot (Or.inl heq)
            have hfirstHigh : first ≠ size + 1 := fun heq => hnot (Or.inr heq)
            have hb := hperm.mem_iff.mp (List.mem_cons_self : first ∈ first :: rest)
            simp only [List.mem_range'] at hb
            have hlow : 1 ∈ rest := by
              have hm : 1 ∈ first :: rest := hperm.mem_iff.mpr (by simp)
              exact (List.mem_cons.mp hm).resolve_left (Ne.symm hfirstLow)
            have hhigh : size + 1 ∈ rest := by
              have hm : size + 1 ∈ first :: rest := hperm.mem_iff.mpr (by simp)
              exact (List.mem_cons.mp hm).resolve_left (Ne.symm hfirstHigh)
            rcases ordered_pair rest 1 (size + 1) hlow hhigh (by omega) with hpair | hpair
            · apply h213
              apply make_pattern [2, 1, 3] _ (by decide) 1 first (size + 1) (by omega)
                (by omega)
              simpa using hpair.cons_cons first
            · apply h231
              apply make_pattern [2, 3, 1] _ (by decide) 1 first (size + 1) (by omega)
                (by omega)
              simpa using hpair.cons_cons first
          have htail213 : ¬ Occurs [2, 1, 3] rest := fun hocc => h213 (inherited _ _ _ hocc)
          have htail231 : ¬ Occurs [2, 3, 1] rest := fun hocc => h231 (inherited _ _ _ hocc)
          rcases hfirst with rfl | rfl
          · left
            have htailPerm : rest.Perm (List.range' 2 size) := by
              simpa [List.range'_succ] using hperm
            let reduced := rest.map Nat.pred
            have hrecover : reduced.map Nat.succ = rest := by
              dsimp [reduced]
              rw [List.map_map]
              calc
                rest.map (Nat.succ ∘ Nat.pred) = rest.map id := by
                  apply List.map_congr_left
                  intro value hvalue
                  have := htailPerm.mem_iff.mp hvalue
                  simp only [List.mem_range'] at this
                  exact Nat.succ_pred_eq_of_pos (by omega)
                _ = rest := List.map_id rest
            have hreducePerm : reduced.Perm (List.range' 1 size) := by
              have hmap := htailPerm.map (fun value => value - 1)
              simpa [reduced, show Nat.pred = (fun value => value - 1) from rfl,
                List.map_sub_range' (by omega : 1 ≤ 2)] using hmap
            refine ⟨reduced, (membership _ _).mpr ⟨hreducePerm, ?_, ?_⟩, ?_⟩
            · intro hocc
              apply htail213
              rw [← hrecover]
              exact (shift reduced _ (by simp)).mpr hocc
            · intro hocc
              apply htail231
              rw [← hrecover]
              exact (shift reduced _ (by simp)).mpr hocc
            · simp [lowInsert, hrecover]
          · right
            refine ⟨rest, (membership _ _).mpr ⟨?_, htail213, htail231⟩, rfl⟩
            exact (hperm.trans highPerm.symm).cons_inv
      · rintro (⟨word, hword, rfl⟩ | ⟨word, hword, rfl⟩)
        · exact lowMember word hword
        · exact highMember word hword
    have hdisjoint : Disjoint (lowInsert '' words size) (highInsert '' words size) := by
      apply Set.disjoint_left.mpr
      rintro word ⟨left, _, hleft⟩ ⟨right, _, hright⟩
      have heq := congrArg List.head? (hleft.trans hright.symm)
      simp [lowInsert, highInsert] at heq
      omega
    have hlowInjective : Function.Injective lowInsert := by
      intro left right heq
      have hmaps := List.cons.inj heq |>.2
      exact (List.map_inj_right (by intro left right heq; omega)).mp hmaps
    have hhighInjective : Function.Injective highInsert := List.cons_injective
    rw [split, Set.ncard_union_eq hdisjoint ((finite_words size).image lowInsert)
      ((finite_words size).image highInsert),
      Set.ncard_image_of_injective _ hlowInjective,
      Set.ncard_image_of_injective _ hhighInjective]
    omega
  have hbase : words 1 = {[1]} := by
    ext word
    rw [membership]
    constructor
    · rintro ⟨hperm, _⟩
      have heq : word = [1] := by simpa using hperm
      simp [heq]
    · intro hword
      have heq : word = [1] := by simpa using hword
      subst word
      refine ⟨by rfl, ?_, ?_⟩
      all_goals
        rintro ⟨witness, _, _, hsub, _⟩
        have := hsub.length_le
        simp at this
  have all_sizes (offset : ℕ) : (words (offset + 1)).ncard = 2 ^ offset := by
    induction offset with
    | zero => simp [hbase]
    | succ offset ih =>
      rw [recurrence (offset + 1) (by omega), ih, pow_succ]
      omega
  simpa [words, Nat.sub_add_cancel hn] using all_sizes (n - 1)

theorem minimum_split_fibonacci (left right : List ℕ)
    (hnodup : (left ++ 1 :: right).Nodup)
    (hleast : ∀ value ∈ left ++ right, 1 < value) :
    (¬ Occurs [2, 1, 3] (left ++ 1 :: right) ∧
      ¬ Occurs [4, 1, 3, 2] (left ++ 1 :: right)) ↔
    (¬ Occurs [2, 1, 3] left ∧ ¬ Occurs [4, 1, 3, 2] left) ∧
      (∀ high ∈ left, ∀ low ∈ right, low < high) ∧
      ((left = [] ∧ ¬ Occurs [2, 1, 3] right ∧ ¬ Occurs [4, 1, 3, 2] right) ∨
        (left ≠ [] ∧ right.Pairwise (· < ·))) := by
  have build (pattern word : List ℕ) (size : ℕ)
      (hpattern : pattern.Perm (List.range' 1 size)) (hletters : letters pattern = size)
      (witness : ℕ → ℕ)
      (hincreasing : ∀ rank, 1 ≤ rank → rank < size →
        witness rank < witness (rank + 1))
      (hsub : (pattern.map witness).Sublist word) : Occurs pattern word := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa [hletters] using hincreasing
    · intro rank hlow hhigh
      rw [hletters] at hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hpattern.mem_iff.mpr
      simp only [List.mem_range'_1]
      omega
  have inherited (pattern smaller larger : List ℕ) (hsublist : smaller.Sublist larger) :
      Occurs pattern smaller → Occurs pattern larger := by
    rintro ⟨witness, hincreasing, hmem, hsub, _⟩
    exact ⟨witness, hincreasing, fun rank hlo hhi => hsublist.subset (hmem rank hlo hhi),
      hsub.trans hsublist, by simp⟩
  have leftSub : left.Sublist (left ++ 1 :: right) := List.sublist_append_left _ _
  have rightSub : right.Sublist (left ++ 1 :: right) :=
    (List.sublist_cons_self 1 right).trans (List.sublist_append_right _ _)
  have positive (value : ℕ) (hvalue : value ∈ left ++ 1 :: right) : 1 ≤ value := by
    rcases List.mem_append.mp hvalue with hleft | hright
    · exact (hleast value (List.mem_append_left _ hleft)).le
    · rcases List.mem_cons.mp hright with rfl | hright
      · omega
      · exact (hleast value (List.mem_append_right _ hright)).le
  have split_selected (selected : List ℕ)
      (hsub : selected.Sublist (left ++ 1 :: right)) :
      ∃ cut ≤ selected.length, (selected.take cut).Sublist left ∧
        (selected.drop cut).Sublist (1 :: right) := by
    obtain ⟨chosenLeft, chosenRight, heq, hprefix, hsuffix⟩ := List.sublist_append_iff.mp hsub
    refine ⟨chosenLeft.length, ?_, ?_, ?_⟩
    · simp [heq]
    · simpa [heq] using hprefix
    · simpa [heq] using hsuffix
  constructor
  · rintro ⟨h213, h4132⟩
    have hseparation : ∀ high ∈ left, ∀ low ∈ right, low < high := by
      intro high hhigh low hlow
      have hne : high ≠ low := by
        intro heq
        have hdisjoint := (List.nodup_append.mp hnodup).2.2
        exact hdisjoint high hhigh low (List.mem_cons_of_mem 1 hlow) heq
      by_contra hnot
      have hlt : high < low := by omega
      have hhighPositive := hleast high (List.mem_append_left _ hhigh)
      apply h213
      let witness := fun rank => if rank = 1 then 1 else if rank = 2 then high else low
      apply build [2, 1, 3] _ 3 (by decide) (by rfl) witness
      · intro rank hlowRank hhighRank
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp [witness] <;> omega
      · have hselected := (List.singleton_sublist.mpr hhigh).append
          ((List.singleton_sublist.mpr hlow).cons_cons 1)
        simpa [witness] using hselected
    refine ⟨⟨fun hocc => h213 (inherited _ _ _ leftSub hocc),
      fun hocc => h4132 (inherited _ _ _ leftSub hocc)⟩, hseparation, ?_⟩
    by_cases hleftEmpty : left = []
    · exact Or.inl ⟨hleftEmpty, fun hocc => h213 (inherited _ _ _ rightSub hocc),
        fun hocc => h4132 (inherited _ _ _ rightSub hocc)⟩
    · right
      refine ⟨hleftEmpty, List.pairwise_iff_forall_sublist.mpr ?_⟩
      intro high low hpair
      have hhigh : high ∈ right := hpair.subset (by simp)
      have hlow : low ∈ right := hpair.subset (by simp)
      have hrightNodup : right.Nodup := (List.nodup_append.mp hnodup).2.1.of_cons
      have hne : high ≠ low := by simpa using hrightNodup.sublist hpair
      by_contra hnot
      have hdescent : low < high := by omega
      obtain ⟨outer, houter⟩ := List.exists_mem_of_ne_nil left hleftEmpty
      have hupper := hseparation outer houter high hhigh
      have hlowerPositive := hleast low (List.mem_append_right _ hlow)
      apply h4132
      let witness := fun rank => if rank = 1 then 1 else if rank = 2 then low else
        if rank = 3 then high else outer
      apply build [4, 1, 3, 2] _ 4 (by decide) (by rfl) witness
      · intro rank hlowRank hhighRank
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp [witness] <;> omega
      · simpa [witness] using
          (List.singleton_sublist.mpr houter).append (hpair.cons_cons 1)
  · rintro ⟨⟨hleft213, hleft4132⟩, hseparation, hright⟩
    have increasing_right (hleft : left ≠ []) : right.Pairwise (· < ·) := by
      rcases hright with ⟨hleftEmpty, _⟩ | ⟨_, hincreasing⟩
      · exact (hleft hleftEmpty).elim
      · exact hincreasing
    have hright213 : ¬ Occurs [2, 1, 3] right := by
      rcases hright with ⟨_, havoid, _⟩ | ⟨hleft, hincreasing⟩
      · exact havoid
      · rintro ⟨witness, hincreasingWitness, _, hsub, _⟩
        have h12 : witness 1 < witness 2 := hincreasingWitness 1 (by omega) (by decide)
        have hpair : [witness 2, witness 1].Sublist right :=
          (by decide : [2, 1].Sublist [2, 1, 3]).map witness |>.trans hsub
        have := List.pairwise_iff_forall_sublist.mp hincreasing hpair
        omega
    have hright4132 : ¬ Occurs [4, 1, 3, 2] right := by
      rcases hright with ⟨_, _, havoid⟩ | ⟨hleft, hincreasing⟩
      · exact havoid
      · rintro ⟨witness, hincreasingWitness, _, hsub, _⟩
        have h12 : witness 1 < witness 2 := hincreasingWitness 1 (by omega) (by decide)
        have h23 : witness 2 < witness 3 := hincreasingWitness 2 (by omega) (by decide)
        have h34 : witness 3 < witness 4 := hincreasingWitness 3 (by omega) (by decide)
        have hpair : [witness 4, witness 1].Sublist right :=
          (by decide : [4, 1].Sublist [4, 1, 3, 2]).map witness |>.trans hsub
        have := List.pairwise_iff_forall_sublist.mp hincreasing hpair
        omega
    constructor
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have hpositive : 1 ≤ witness 1 := positive _ (hmem 1 (by omega) (by decide))
      change [witness 2, witness 1, witness 3].Sublist (left ++ 1 :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 := by simp at hcut; omega
      rcases this with rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        have hselected : [witness 2, witness 1, witness 3].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hsuffix
        exact hright213 (build _ _ 3 (by decide) (by rfl) witness (by
          intro rank hlo hhi
          exact hincreasing rank hlo hhi) (by simpa using hselected))
      · have hhigh : witness 2 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 1, witness 3].Sublist (1 :: right) := by
          simpa using hsuffix
        have hlow : witness 3 ∈ right := hselected.of_cons_cons.subset (by simp)
        have := hseparation _ hhigh _ hlow
        omega
      · have hhigh : witness 2 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 3].Sublist (1 :: right) := by simpa using hsuffix
        have hlow : witness 3 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := hseparation _ hhigh _ hlow
        omega
      · have hselected : [witness 2, witness 1, witness 3].Sublist left := by
          simpa using hprefix
        exact hleft213 (build _ _ 3 (by decide) (by rfl) witness (by
          intro rank hlo hhi
          exact hincreasing rank hlo hhi) (by simpa using hselected))
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have h34 : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have hpositive : 1 ≤ witness 1 := positive _ (hmem 1 (by omega) (by decide))
      change [witness 4, witness 1, witness 3, witness 2].Sublist
        (left ++ 1 :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 := by
        simp at hcut
        omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        have hselected : [witness 4, witness 1, witness 3, witness 2].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hsuffix
        exact hright4132 (build _ _ 4 (by decide) (by rfl) witness (by
          intro rank hlo hhi
          exact hincreasing rank hlo hhi) (by simpa using hselected))
      · have hhigh : witness 4 ∈ left := hprefix.subset (by simp)
        have hleft : left ≠ [] := List.ne_nil_of_mem hhigh
        have hselected : [witness 1, witness 3, witness 2].Sublist (1 :: right) := by
          simpa using hsuffix
        have hpair : [witness 3, witness 2].Sublist right := hselected.of_cons_cons
        have := List.pairwise_iff_forall_sublist.mp (increasing_right hleft) hpair
        omega
      · have hhigh : witness 4 ∈ left := hprefix.subset (by simp)
        have hleft : left ≠ [] := List.ne_nil_of_mem hhigh
        have hselected : [witness 3, witness 2].Sublist (1 :: right) := by
          simpa using hsuffix
        have hpair : [witness 3, witness 2].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hselected
        have := List.pairwise_iff_forall_sublist.mp (increasing_right hleft) hpair
        omega
      · have hhigh : witness 1 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 2].Sublist (1 :: right) := by simpa using hsuffix
        have hlow : witness 2 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := hseparation _ hhigh _ hlow
        omega
      · have hselected : [witness 4, witness 1, witness 3, witness 2].Sublist left := by
          simpa using hprefix
        exact hleft4132 (build _ _ 4 (by decide) (by rfl) witness (by
          intro rank hlo hhi
          exact hincreasing rank hlo hhi) (by simpa using hselected))

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCounts
