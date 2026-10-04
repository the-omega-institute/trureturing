/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFailureProduct
   mirror-E: none(waiver:separated-contraction-failures)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The separated marked circles are counted by two independent Fibonacci classes. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFailureProduct

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular

set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
theorem alternating_separated_circle_count (size pivot : ℕ)
    (hpivot : 2 ≤ pivot) (hsize : pivot < size) :
    ({p : List ℕ | p ∈ rotationAvoiders size size [2, 4, 1, 3] ∧
      p.head? = some pivot ∧ p.tail =
        p.tail.filter (fun value => decide (value < pivot)) ++
        p.tail.filter (fun value => decide (pivot < value))} : Set (List ℕ)).ncard =
      Nat.fib (2 * (pivot - 1) - 1) * Nat.fib (2 * (size - pivot) - 1) := by
  have build (pattern container : List ℕ) (width : ℕ) (chosen : ℕ → ℕ)
      (hp : pattern.Perm (List.range' 1 width)) (hl : letters pattern = width)
      (hi : ∀ rank, 1 ≤ rank → rank < width → chosen rank < chosen (rank + 1))
      (hs : (pattern.map chosen).Sublist container) : Occurs pattern container := by
    refine ⟨chosen, ?_, ?_, hs, by simp⟩
    · simpa only [hl] using hi
    · intro rank hlo hhi
      rw [hl] at hhi
      exact hs.subset (List.mem_map_of_mem
        (hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))))
  have mono (pattern small large : List ℕ) (hs : small.Sublist large) :
      Occurs pattern small → Occurs pattern large := by
    rintro ⟨chosen, hi, hm, ht, _⟩
    exact ⟨chosen, hi, fun rank hlo hhi => hs.subset (hm rank hlo hhi),
      ht.trans hs, by simp⟩
  have criterion (low high : List ℕ)
      (hlow : low.Perm (List.range' 1 (pivot - 1)))
      (hhigh : high.Perm (List.range' (pivot + 1) (size - pivot))) :
      (pivot :: low ++ high) ∈ rotationAvoiders size size [2, 4, 1, 3] ↔
        ¬ Occurs [1, 3, 2] low ∧ ¬ Occurs [3, 2, 4, 1] low ∧
        ¬ Occurs [2, 1, 3] high ∧ ¬ Occurs [4, 1, 3, 2] high := by
    let word := pivot :: low ++ high
    have lowBounds (value : ℕ) (hv : value ∈ low) : 1 ≤ value ∧ value < pivot := by
      have hh := List.mem_range'_1.mp (hlow.mem_iff.mp hv); omega
    have highBounds (value : ℕ) (hv : value ∈ high) : pivot < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hhigh.mem_iff.mp hv); omega
    have hn : word.Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨?_, List.nodup_append.mpr
        ⟨hlow.nodup_iff.mpr List.nodup_range', hhigh.nodup_iff.mpr List.nodup_range', ?_⟩⟩
      · intro hv
        rcases List.mem_append.mp hv with hv | hv
        · have := lowBounds pivot hv; omega
        · have := highBounds pivot hv; omega
      · intro a ha b hb he
        have := lowBounds a ha
        have := highBounds b hb; omega
    have perm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup hn List.nodup_range').mpr
      intro value
      simp only [word, List.cons_append, List.mem_cons, List.mem_append,
        hlow.mem_iff, hhigh.mem_iff, List.mem_range'_1]
      omega
    have cycleCriterion := all_cuts_iff_cycle_avoidance size (by omega)
      [2, 4, 1, 3] word (by decide) perm
    have lowSub : low.Sublist word :=
      (List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)
    have highSub : high.Sublist word :=
      (List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)
    constructor
    · intro hg
      have hc := cycleCriterion.mp hg
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro ⟨chosen, hi, hm, hs, _⟩
        let lifted := fun rank : ℕ => if rank = 4 then pivot else chosen rank
        have upper : chosen 3 < pivot := (lowBounds _ (hm 3 (by omega) (by decide))).2
        have triple : [chosen 1, chosen 3, chosen 2].Sublist low := hs
        apply hc 1 (by omega)
        apply build [4, 1, 3, 2] word 4 lifted (by decide) rfl
        · intro rank hlo hhi
          have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hh with rfl | rfl | rfl
          · simpa [lifted] using hi 1 (by omega) (by decide)
          · simpa [lifted] using hi 2 (by omega) (by decide)
          · simpa [lifted] using upper
        · simpa [lifted, word] using (triple.trans
            (List.sublist_append_left low high)).cons_cons pivot
      · exact fun ho => hc 3 (by omega) (mono _ _ _ lowSub ho)
      · rintro ⟨chosen, hi, hm, hs, _⟩
        let lifted := fun rank : ℕ => if rank = 1 then pivot else chosen (rank - 1)
        have lower : pivot < chosen 1 := (highBounds _ (hm 1 (by omega) (by decide))).1
        apply hc 2 (by omega)
        apply build [1, 3, 2, 4] word 4 lifted (by decide) rfl
        · intro rank hlo hhi
          have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hh with rfl | rfl | rfl
          · simpa [lifted] using lower
          · simpa [lifted] using hi 1 (by omega) (by decide)
          · simpa [lifted] using hi 2 (by omega) (by decide)
        · have ht := hs.trans (List.sublist_append_right low high)
          simpa [lifted, word] using ht.cons_cons pivot
      · exact fun ho => hc 1 (by omega) (mono _ _ _ highSub ho)
    · rintro ⟨hl132, hl3241, hh213, hh4132⟩
      apply cycleCriterion.mpr
      let bucket := fun value : ℕ => if value < pivot then 0 else if value = pivot then 1 else 2
      have bound (value : ℕ) : bucket value < 3 := by dsimp [bucket]; split_ifs <;> omega
      let color := fun value : ℕ => (⟨bucket value, bound value⟩ : Fin 3)
      let slot : Fin 3 → ℕ := fun shade => if shade = 0 then 1 else if shade = 1 then 0 else 2
      let position := fun value : ℕ => slot (color value)
      have lowColor (value : ℕ) (hv : value ∈ low) : color value = 0 := by
        simp [color, bucket, (lowBounds value hv).2]
      have highColor (value : ℕ) (hv : value ∈ high) : color value = 2 := by
        have hb := highBounds value hv
        simp [color, bucket, show ¬ value < pivot by omega, show value ≠ pivot by omega]
      have pivotColor : color pivot = 1 := by simp [color, bucket]
      have colorMono (a b : ℕ) (hh : a ≤ b) : color a ≤ color b := by
        change bucket a ≤ bucket b
        dsimp [bucket]; split_ifs <;> omega
      have singleton (value : ℕ) (hc : color value = 1) : value = pivot := by
        have he := congrArg Fin.val hc
        dsimp [color, bucket] at he
        split_ifs at he <;> omega
      have ordered : word.Pairwise (fun a b => position a ≤ position b) := by
        have lowOrdered : low.Pairwise (fun a b => position a ≤ position b) :=
          List.pairwise_of_forall_mem_list (by
            intro a ha b hb; simp [position, lowColor a ha, lowColor b hb])
        have highOrdered : high.Pairwise (fun a b => position a ≤ position b) :=
          List.pairwise_of_forall_mem_list (by
            intro a ha b hb; simp [position, highColor a ha, highColor b hb])
        simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
          List.mem_append, or_imp, forall_and]
        refine ⟨⟨?_, ?_⟩, lowOrdered, highOrdered, ?_⟩
        · intro a ha; simp [position, pivotColor, lowColor a ha, slot]
        · intro a ha; simp [position, pivotColor, highColor a ha, slot]
        · intro a ha b hb; simp [position, lowColor a ha, highColor b hb, slot]
      have filtered (shade : Fin 3) :
          word.filter (fun value => decide (color value = shade)) =
            if shade = 0 then low else if shade = 1 then [pivot] else high := by
        have block (values : List ℕ) (paint : Fin 3)
            (hc : ∀ value ∈ values, color value = paint) :
            values.filter (fun value => decide (color value = shade)) =
              if shade = paint then values else [] := by
          split_ifs with he
          · exact List.filter_eq_self.mpr (by intro value hv; simp [hc value hv, he])
          · exact List.filter_eq_nil_iff.mpr (by
              intro value hv; simp [hc value hv, Ne.symm he])
        simp only [word, List.cons_append, List.filter_cons, List.filter_append,
          block low 0 lowColor, block high 2 highColor, pivotColor]
        fin_cases shade <;> simp
      have profiles : ∀ a b c d : Fin 3,
          a ≤ b → b ≤ c → c ≤ d →
          (a = b → a ≠ 1) → (b = c → b ≠ 1) → (c = d → c ≠ 1) →
          ((slot b ≤ slot d ∧ slot d ≤ slot a ∧ slot a ≤ slot c) →
            (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 2)) ∧
          ((slot d ≤ slot a ∧ slot a ≤ slot c ∧ slot c ≤ slot b) →
            (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 2)) ∧
          ((slot a ≤ slot c ∧ slot c ≤ slot b ∧ slot b ≤ slot d) →
            (a = 0 ∧ b = 0 ∧ c = 0) ∨ (b = 2 ∧ c = 2 ∧ d = 2)) ∧
          ((slot c ≤ slot b ∧ slot b ≤ slot d ∧ slot d ≤ slot a) →
            (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (b = 2 ∧ c = 2 ∧ d = 2)) := by decide
      intro shift hshift ho
      obtain ⟨chosen, hi, _, selected, _⟩ := ho
      have hp := (List.rotate_perm ([2, 4, 1, 3] : List ℕ) shift).trans
        (by decide : ([2, 4, 1, 3] : List ℕ).Perm [1, 2, 3, 4])
      have hl : letters (([2, 4, 1, 3] : List ℕ).rotate shift) = 4 := by
        simpa [letters] using hp.foldr_eq (f := max) 0
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa only [hl] using hi
      have single (a b : ℕ) (hh : chosen a < chosen b) :
          color (chosen a) = color (chosen b) → color (chosen a) ≠ 1 := by
        intro he hc
        have := singleton _ hc
        have := singleton _ (he.symm.trans hc); omega
      have shapes := profiles (color (chosen 1)) (color (chosen 2))
        (color (chosen 3)) (color (chosen 4))
        (colorMono _ _ (hi' 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi' 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi' 3 (by omega) (by omega)).le)
        (single 1 2 (hi' 1 (by omega) (by omega)))
        (single 2 3 (hi' 2 (by omega) (by omega)))
        (single 3 4 (hi' 3 (by omega) (by omega)))
      have edge (a b : ℕ) (hs : [a, b].Sublist (([2, 4, 1, 3] : List ℕ).rotate shift)) :
          position (chosen a) ≤ position (chosen b) :=
        List.pairwise_iff_forall_sublist.mp ordered ((hs.map chosen).trans selected)
      have project (ranks : List ℕ) (shade : Fin 3) (block : List ℕ)
          (hs : ranks.Sublist (([2, 4, 1, 3] : List ℕ).rotate shift))
          (hc : ∀ rank ∈ ranks, color (chosen rank) = shade)
          (hf : word.filter (fun value => decide (color value = shade)) = block) :
          (ranks.map chosen).Sublist block := by
        have hh := ((hs.map chosen).trans selected).filter
          (fun value => decide (color value = shade))
        have he : (ranks.map chosen).filter (fun value => decide (color value = shade)) =
            ranks.map chosen := List.filter_eq_self.mpr (by
          intro value hv
          obtain ⟨rank, hr, rfl⟩ := List.mem_map.mp hv
          simp [hc rank hr])
        rwa [he, hf] at hh
      have lowTriple (ranks : List ℕ) (hc : ∀ rank ∈ ranks, color (chosen rank) = 0)
          (hs : ranks.Sublist (([2, 4, 1, 3] : List ℕ).rotate shift))
          (he : ranks = [1, 3, 2] ∨ ranks = [2, 4, 3]) : False := by
        apply hl132
        rcases he with rfl | rfl
        · apply build _ low 3 chosen (by decide) rfl
          · intro rank hlo hhi; interval_cases rank <;> exact hi' _ (by omega) (by omega)
          · exact project _ 0 low hs hc (by simpa using filtered 0)
        · apply build _ low 3 (fun rank => chosen (rank + 1)) (by decide) rfl
          · intro rank hlo hhi; interval_cases rank <;> exact hi' _ (by omega) (by omega)
          · simpa using project _ 0 low hs hc (by simpa using filtered 0)
      have highTriple (ranks : List ℕ) (hc : ∀ rank ∈ ranks, color (chosen rank) = 2)
          (hs : ranks.Sublist (([2, 4, 1, 3] : List ℕ).rotate shift))
          (he : ranks = [2, 1, 3] ∨ ranks = [3, 2, 4]) : False := by
        apply hh213
        rcases he with rfl | rfl
        · apply build _ high 3 chosen (by decide) rfl
          · intro rank hlo hhi; interval_cases rank <;> exact hi' _ (by omega) (by omega)
          · exact project _ 2 high hs hc (by simpa using filtered 2)
        · apply build _ high 3 (fun rank => chosen (rank + 1)) (by decide) rfl
          · intro rank hlo hhi; interval_cases rank <;> exact hi' _ (by omega) (by omega)
          · simpa using project _ 2 high hs hc (by simpa using filtered 2)
      interval_cases shift
      · have shape := shapes.1 ⟨edge 2 4 (by decide), edge 4 1 (by decide),
          edge 1 3 (by decide)⟩
        rcases shape with hh | hh
        · apply lowTriple [2, 4, 3] _ (by decide) (Or.inr rfl)
          intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> tauto
        · apply highTriple [2, 1, 3] _ (by decide) (Or.inl rfl)
          intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> tauto
      · have shape := shapes.2.1 ⟨edge 4 1 (by decide), edge 1 3 (by decide),
          edge 3 2 (by decide)⟩
        rcases shape with hh | hh
        · apply lowTriple [1, 3, 2] _ (by decide) (Or.inl rfl)
          intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> tauto
        · apply hh4132
          apply build _ high 4 chosen (by decide) rfl hi'
          exact project [4, 1, 3, 2] 2 high (by decide) (by
            intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl <;> tauto) (by simpa using filtered 2)
      · have shape := shapes.2.2.1 ⟨edge 1 3 (by decide), edge 3 2 (by decide),
          edge 2 4 (by decide)⟩
        rcases shape with hh | hh
        · apply lowTriple [1, 3, 2] _ (by decide) (Or.inl rfl)
          intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> tauto
        · apply highTriple [3, 2, 4] _ (by decide) (Or.inr rfl)
          intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> tauto
      · have shape := shapes.2.2.2 ⟨edge 3 2 (by decide), edge 2 4 (by decide),
          edge 4 1 (by decide)⟩
        rcases shape with hh | hh
        · apply hl3241
          apply build _ low 4 chosen (by decide) rfl hi'
          exact project [3, 2, 4, 1] 0 low (by decide) (by
            intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl <;> tauto) (by simpa using filtered 0)
        · apply highTriple [3, 2, 4] _ (by decide) (Or.inr rfl)
          intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> tauto
  classical
  let lowerParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (pivot - 1)
    [[1, 3, 2], [3, 2, 4, 1]]
  let upperParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (size - pivot)
    [[2, 1, 3], [4, 1, 3, 2]]
  let domain := lowerParents ×ˢ upperParents
  let target := {p : List ℕ | p ∈ rotationAvoiders size size [2, 4, 1, 3] ∧
    p.head? = some pivot ∧ p.tail =
      p.tail.filter (fun value => decide (value < pivot)) ++
      p.tail.filter (fun value => decide (pivot < value))}
  let emit := fun pair : List ℕ × List ℕ =>
    pivot :: pair.1 ++ pair.2.map (fun value => pivot + value)
  have lowerMembership (p : List ℕ) : p ∈ lowerParents ↔
      p.Perm (List.range' 1 (pivot - 1)) ∧
        ¬ Occurs [1, 3, 2] p ∧ ¬ Occurs [3, 2, 4, 1] p := by
    simp [lowerParents, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have upperMembership (p : List ℕ) : p ∈ upperParents ↔
      p.Perm (List.range' 1 (size - pivot)) ∧
        ¬ Occurs [2, 1, 3] p ∧ ¬ Occurs [4, 1, 3, 2] p := by
    simp [upperParents, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have shift (pattern p : List ℕ) (hl : letters pattern = pattern.length) :
      Occurs pattern (p.map (fun value => pivot + value)) ↔ Occurs pattern p := by
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern p (pivot + ·)
      (by intro a b hh; dsimp; omega)
  have filters (low high : List ℕ)
      (hl : ∀ value ∈ low, value < pivot) (hh : ∀ value ∈ high, pivot < value) :
      (low ++ high).filter (fun value => decide (value < pivot)) = low ∧
      (low ++ high).filter (fun value => decide (pivot < value)) = high := by
    have keepLow : low.filter (fun value => decide (value < pivot)) = low :=
      List.filter_eq_self.mpr (by intro value hv; simp [hl value hv])
    have dropLow : low.filter (fun value => decide (pivot < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by intro value hv; have := hl value hv; simp; omega)
    have keepHigh : high.filter (fun value => decide (pivot < value)) = high :=
      List.filter_eq_self.mpr (by intro value hv; simp [hh value hv])
    have dropHigh : high.filter (fun value => decide (value < pivot)) = [] :=
      List.filter_eq_nil_iff.mpr (by intro value hv; have := hh value hv; simp; omega)
    simp only [List.filter_append, keepLow, dropLow, keepHigh, dropHigh,
      List.append_nil, List.nil_append, and_self]
  have emitMember (pair : List ℕ × List ℕ) (hp : pair ∈ domain) : emit pair ∈ target := by
    obtain ⟨hl, hl132, hl3241⟩ := (lowerMembership pair.1).mp hp.1
    obtain ⟨hh, hh213, hh4132⟩ := (upperMembership pair.2).mp hp.2
    have highPerm : (pair.2.map (fun value => pivot + value)).Perm
        (List.range' (pivot + 1) (size - pivot)) := by
      simpa only [List.map_add_range'] using hh.map (fun value => pivot + value)
    have hc := (criterion pair.1 _ hl highPerm).mpr
      ⟨hl132, hl3241, fun ho => hh213 ((shift _ _ rfl).mp ho),
        fun ho => hh4132 ((shift _ _ rfl).mp ho)⟩
    have hf := filters pair.1 (pair.2.map (fun value => pivot + value)) (by
      intro value hv
      have := List.mem_range'_1.mp (hl.mem_iff.mp hv); omega) (by
      intro value hv
      have := List.mem_range'_1.mp (highPerm.mem_iff.mp hv); omega)
    exact ⟨hc, by simp [emit], by simpa only [emit, List.cons_append, List.tail_cons,
      hf.1, hf.2]⟩
  let decode := fun p : List ℕ =>
    (p.tail.filter (fun value => decide (value < pivot)),
      (p.tail.filter (fun value => decide (pivot < value))).map (fun value => value - pivot))
  have decodeEmit (pair : List ℕ × List ℕ) (hp : pair ∈ domain) : decode (emit pair) = pair := by
    have highPerm := hp.2.1.map (fun value => pivot + value)
    have hf := filters pair.1 (pair.2.map (fun value => pivot + value)) (by
      intro value hv
      have := List.mem_range'_1.mp (hp.1.1.mem_iff.mp hv); omega) (by
      intro value hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hv
      have := List.mem_range'_1.mp (hp.2.1.mem_iff.mp ho); omega)
    simp [decode, emit, hf.1, hf.2, List.map_map, Function.comp_def]
  have emitSurjective (p : List ℕ) (hp : p ∈ target) :
      ∃ pair ∈ domain, emit pair = p := by
    have split : p = pivot :: p.tail := by
      cases p with
      | nil => simp [target] at hp
      | cons head tail =>
        have he : head = pivot := by simpa using hp.2.1
        simp [he]
    let low := p.tail.filter (fun value => decide (value < pivot))
    let high := p.tail.filter (fun value => decide (pivot < value))
    have separated : p = pivot :: low ++ high := by
      rw [split]
      congr 1
      exact hp.2.2
    have tailNodup : p.tail.Nodup :=
      (List.nodup_cons.mp (split ▸ hp.1.1.nodup_iff.mpr List.nodup_range')).2
    have lowPerm : low.Perm (List.range' 1 (pivot - 1)) := by
      apply (List.perm_ext_iff_of_nodup (tailNodup.filter _) List.nodup_range').mpr
      intro value
      simp only [low, List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
      constructor
      · rintro ⟨hv, hb⟩
        have := List.mem_range'_1.mp (hp.1.1.mem_iff.mp (List.mem_of_mem_tail hv)); omega
      · intro hv
        have hm := hp.1.1.mem_iff.mpr
          (List.mem_range'_1.mpr (by omega : 1 ≤ value ∧ value < 1 + size))
        rw [split] at hm
        exact ⟨(List.mem_cons.mp hm).resolve_left (by omega), by omega⟩
    have highPerm : high.Perm (List.range' (pivot + 1) (size - pivot)) := by
      apply (List.perm_ext_iff_of_nodup (tailNodup.filter _) List.nodup_range').mpr
      intro value
      simp only [high, List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
      constructor
      · rintro ⟨hv, hb⟩
        have := List.mem_range'_1.mp (hp.1.1.mem_iff.mp (List.mem_of_mem_tail hv)); omega
      · intro hv
        have hm := hp.1.1.mem_iff.mpr
          (List.mem_range'_1.mpr (by omega : 1 ≤ value ∧ value < 1 + size))
        rw [split] at hm
        exact ⟨(List.mem_cons.mp hm).resolve_left (by omega), by omega⟩
    let parent := high.map (fun value => value - pivot)
    have parentPerm : parent.Perm (List.range' 1 (size - pivot)) := by
      simpa only [parent, List.map_sub_range' (by omega : pivot ≤ pivot + 1),
        Nat.add_sub_cancel_left] using highPerm.map (fun value => value - pivot)
    have restore : parent.map (fun value => pivot + value) = high := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id high]
      apply List.map_congr_left
      intro value hv
      have := List.mem_range'_1.mp (highPerm.mem_iff.mp hv)
      dsimp; omega
    have hc := (criterion low high lowPerm highPerm).mp (separated ▸ hp.1)
    refine ⟨(low, parent), ⟨(lowerMembership low).mpr ⟨lowPerm, hc.1, hc.2.1⟩,
      (upperMembership parent).mpr ⟨parentPerm, ?_, ?_⟩⟩, ?_⟩
    · intro ho; exact hc.2.2.1 (restore ▸ (shift _ _ rfl).mpr ho)
    · intro ho; exact hc.2.2.2 (restore ▸ (shift _ _ rfl).mpr ho)
    · simpa only [emit, restore] using separated.symm
  have sliceCard := Set.ncard_congr (s := domain) (t := target) (fun pair _ => emit pair)
    emitMember (by
      intro a b ha hb he
      have hh := congrArg decode he
      rwa [decodeEmit a ha, decodeEmit b hb] at hh) (by
      intro p hp
      obtain ⟨pair, hh, he⟩ := emitSurjective p hp
      exact ⟨pair, hh, he⟩)
  let reflectedParents := Fishburn.FishburnClassicalDefs.classicalAvoiders (pivot - 1)
    [[2, 1, 3], [4, 1, 3, 2]]
  let reflect := fun word : List ℕ => (word.map (fun value => pivot - value)).reverse
  have reflectPerm (word : List ℕ) (hp : word.Perm (List.range' 1 (pivot - 1))) :
      (reflect word).Perm (List.range' 1 (pivot - 1)) := by
    have hr : (List.range' 1 (pivot - 1)).map (fun value => pivot - value) =
        (List.range' 1 (pivot - 1)).reverse := by
      rw [List.reverse_range', List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro value hv
      dsimp; omega
    exact (List.reverse_perm _).trans
      (((hp.map (pivot - ·)).trans (List.Perm.of_eq hr)).trans (List.reverse_perm _))
  have reflectTwice (word : List ℕ) (hp : word.Perm (List.range' 1 (pivot - 1))) :
      reflect (reflect word) = word := by
    simp only [reflect, List.map_reverse, List.reverse_reverse, List.map_map]
    conv_rhs => rw [← List.map_id word]
    apply List.map_congr_left
    intro value hv
    have hh := List.mem_range'_1.mp (hp.mem_iff.mp hv)
    dsimp; omega
  have reflectOccurrence (width : ℕ) (pattern word : List ℕ)
      (hp : pattern.Perm (List.range' 1 width)) (hl : letters pattern = width)
      (hr : letters ((pattern.map (fun rank => width + 1 - rank)).reverse) = width)
      (hw : word.Perm (List.range' 1 (pivot - 1))) :
      Occurs pattern word →
        Occurs ((pattern.map (fun rank => width + 1 - rank)).reverse) (reflect word) := by
    rintro ⟨witness, hi, hm, hs, _⟩
    let chosen := fun rank : ℕ => pivot - witness (width + 1 - rank)
    have witnessBounds (rank : ℕ) (hlo : 1 ≤ rank) (hhi : rank ≤ width) :
        1 ≤ witness rank ∧ witness rank < pivot := by
      have hh := List.mem_range'_1.mp (hw.mem_iff.mp (hm rank hlo (by rwa [hl])))
      omega
    refine ⟨chosen, ?_, ?_, ?_, by simp⟩
    · intro rank hlo hhi
      rw [hr] at hhi
      have hh := hi (width - rank) (by omega) (by rw [hl]; omega)
      have hb := witnessBounds (width + 1 - rank) (by omega) (by omega)
      have he : width - rank + 1 = width + 1 - rank := by omega
      rw [he] at hh
      dsimp [chosen]
      have he' : width + 1 - (rank + 1) = width - rank := by omega
      rw [he']; omega
    · intro rank hlo hhi
      rw [hr] at hhi
      apply List.mem_reverse.mpr
      exact List.mem_map.mpr ⟨witness (width + 1 - rank),
        hm _ (by omega) (by rw [hl]; omega), rfl⟩
    · have ht := (hs.map (fun value => pivot - value)).reverse
      convert ht using 1
      simp only [List.map_reverse, List.map_map]
      congr 1
      apply List.map_congr_left
      intro rank hk
      have hb := List.mem_range'_1.mp (hp.mem_iff.mp hk)
      dsimp [chosen]
      congr 2
      omega
  have reflectMember (word : List ℕ) (hw : word ∈ lowerParents) :
      reflect word ∈ reflectedParents := by
    obtain ⟨hp, h132, h3241⟩ := (lowerMembership word).mp hw
    refine ⟨reflectPerm word hp, ?_⟩
    intro pattern ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · intro ho
      have hh := reflectOccurrence 3 [2, 1, 3] (reflect word) (by decide) rfl rfl
        (reflectPerm word hp) ho
      rw [reflectTwice word hp] at hh
      exact h132 hh
    · intro ho
      have hh := reflectOccurrence 4 [4, 1, 3, 2] (reflect word) (by decide) rfl rfl
        (reflectPerm word hp) ho
      rw [reflectTwice word hp] at hh
      exact h3241 hh
  have reflectBack (word : List ℕ) (hw : word ∈ reflectedParents) :
      reflect word ∈ lowerParents := by
    refine (lowerMembership _).mpr ⟨reflectPerm word hw.1, ?_, ?_⟩
    · intro ho
      have hh := reflectOccurrence 3 [1, 3, 2] (reflect word) (by decide) rfl rfl
        (reflectPerm word hw.1) ho
      rw [reflectTwice word hw.1] at hh
      exact hw.2 [2, 1, 3] (by simp) hh
    · intro ho
      have hh := reflectOccurrence 4 [3, 2, 4, 1] (reflect word) (by decide) rfl rfl
        (reflectPerm word hw.1) ho
      rw [reflectTwice word hw.1] at hh
      exact hw.2 [4, 1, 3, 2] (by simp) hh
  have lowerCard : lowerParents.ncard = Nat.fib (2 * (pivot - 1) - 1) := by
    have hc := Set.ncard_congr (s := lowerParents) (t := reflectedParents)
      (fun word _ => reflect word) reflectMember (by
        intro left right hl hr he
        have hh := congrArg reflect he
        rwa [reflectTwice left hl.1, reflectTwice right hr.1] at hh) (by
        intro word hw
        exact ⟨reflect word, reflectBack word hw, reflectTwice word hw.1⟩)
    exact hc.trans (RotationAvoidanceFibonacci.fibonacci_count (pivot - 1) (by omega))
  have upperCard : upperParents.ncard = Nat.fib (2 * (size - pivot) - 1) :=
    RotationAvoidanceFibonacci.fibonacci_count (size - pivot) (by omega)
  change target.ncard = _
  rw [← sliceCard, Set.ncard_prod, lowerCard, upperCard]

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFailureProduct
