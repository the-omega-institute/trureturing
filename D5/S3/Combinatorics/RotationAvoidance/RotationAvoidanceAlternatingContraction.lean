/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAlternatingContraction
   mirror-E: none(waiver:alternating-consecutive-endpoint-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Marked contraction removes the product family of separated Fibonacci parents. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceBinaryContraction
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFailureProduct
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAlternatingContraction

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular RotationAvoidanceBinaryContraction

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
theorem alternating_consecutive_endpoint_count (width pivot : ℕ) (hwidth : 3 ≤ width)
    (hpivot : 2 ≤ pivot) (hupper : pivot < width + 1) :
    ({word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
      word.head? = some pivot ∧ word.getLast? = some (pivot + 1) ∧
      ∀ cut < width + 2, Occurs [2, 4, 1, 3] (word.rotate cut) ↔ cut = 0} :
        Set (List ℕ)).ncard = Nat.fib (2 * width - 1) -
          Nat.fib (2 * (pivot - 1) - 1) * Nat.fib (2 * (width + 1 - pivot) - 1) := by
  classical
  let q : List ℕ := [2, 4, 1, 3]
  let parents := {p : List ℕ | p ∈ rotationAvoiders (width + 1) (width + 1) q ∧
    p.head? = some pivot}
  let ordered := fun p : List ℕ => p.tail.Pairwise (fun a b => a < pivot ∨ pivot < b)
  let failures := {p : List ℕ | p ∈ parents ∧ ordered p}
  let accepted := parents \ failures
  let target := {word : List ℕ | word.Perm (List.range' 1 (width + 2)) ∧
    word.head? = some pivot ∧ word.getLast? = some (pivot + 1) ∧
    ∀ cut < width + 2, Occurs q (word.rotate cut) ↔ cut = 0}
  have rotatedGood (p : List ℕ)
      (hp : p ∈ rotationAvoiders (width + 1) (width + 1) q) (cut : ℕ) :
      p.rotate cut ∈ rotationAvoiders (width + 1) (width + 1) q := by
    refine ⟨(List.rotate_perm _ _).trans hp.1, ?_⟩
    intro start hs ho
    rw [List.rotate_rotate, ← List.rotate_mod,
      show p.length = width + 1 by simpa using hp.1.length_eq] at ho
    exact hp.2 _ (Nat.mod_lt _ (by omega)) ho
  let root := fun value (p : List ℕ) => p.rotate (p.idxOf value)
  have rootHead (value : ℕ) (p : List ℕ) (hm : value ∈ p) :
      (root value p).head? = some value := by
    change (p.rotate (p.idxOf value)).head? = some value
    rw [List.head?_rotate (List.idxOf_lt_length_iff.mpr hm)]
    exact List.getElem?_idxOf hm
  have rootedUnique (u v : List ℕ) (hu : u.Nodup) (value : ℕ)
      (hh : u.head? = some value) (hv : v.head? = some value)
      (hr : List.IsRotated u v) : u = v := by
    obtain ⟨cut, he⟩ := hr
    have hn : u ≠ [] := by intro he; simp [he] at hh
    have hz : 0 < u.length := List.length_pos_of_ne_nil hn
    have hb : cut % u.length < u.length := Nat.mod_lt _ hz
    have hg : u[cut % u.length]? = u[0]? := by
      rw [← List.head?_rotate hb, List.rotate_mod, he, ← List.head?_eq_getElem?, hh, hv]
    rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hz,
      Option.some.injEq] at hg
    have hzero : cut % u.length = 0 := hu.getElem_inj_iff.mp hg
    rw [← List.rotate_mod u cut, hzero, List.rotate_zero] at he
    exact he
  have rootMember (value : ℕ) (hv : 1 ≤ value ∧ value ≤ width + 1) (p : List ℕ)
      (hp : p ∈ rotationAvoiders (width + 1) (width + 1) q) :
      root value p ∈ rotationAvoiders (width + 1) (width + 1) q ∧
        (root value p).head? = some value := by
    exact ⟨rotatedGood p hp _, rootHead value p
      (hp.1.mem_iff.mpr (List.mem_range'_1.mpr (by omega)))⟩
  have rootTwice (a b : ℕ) (hb : 1 ≤ b ∧ b ≤ width + 1) (p : List ℕ)
      (hp : p ∈ rotationAvoiders (width + 1) (width + 1) q)
      (hhead : p.head? = some a) : root a (root b p) = p := by
    have hm := rootMember b hb p hp
    have hmem : a ∈ root b p :=
      (List.rotate_perm p _).mem_iff.mpr (List.mem_of_head? hhead)
    apply rootedUnique (root a (root b p)) p
      (List.nodup_rotate.mpr (hm.1.1.nodup_iff.mpr List.nodup_range')) a
      (rootHead a _ hmem) hhead
    exact (List.IsRotated.forall _ _).trans (List.IsRotated.forall _ _)
  have parentsCount : parents.ncard = (circularAvoiders (width + 1) q).ncard := by
    have hc := Set.ncard_congr (s := circularAvoiders (width + 1) q) (t := parents)
      (fun p _ => root pivot p) (fun p hp => rootMember pivot (by omega) p hp.1) (by
        intro u v hu hv he
        have hh := congrArg (root 1) he
        rwa [rootTwice 1 pivot (by omega) u hu.1 hu.2,
          rootTwice 1 pivot (by omega) v hv.1 hv.2] at hh) (by
        intro p hp
        refine ⟨root 1 p, rootMember 1 (by omega) p hp.1, ?_⟩
        exact rootTwice pivot 1 (by omega) p hp.1 hp.2)
    exact hc.symm
  have parentSplit (p : List ℕ) (hp : p ∈ parents) : p = pivot :: p.tail := by
    cases p with
    | nil => simp [parents] at hp
    | cons head tail =>
      have hh : head = pivot := by simpa using hp.2
      simp [hh]
  have orderedIff (tail : List ℕ) (hne : pivot ∉ tail) :
      tail.Pairwise (fun a b => a < pivot ∨ pivot < b) ↔
        tail = tail.filter (fun value => decide (value < pivot)) ++
          tail.filter (fun value => decide (pivot < value)) := by
    constructor
    · intro hh
      induction tail with
      | nil => simp
      | cons head rest ih =>
        obtain ⟨headPairs, restPairs⟩ := List.pairwise_cons.mp hh
        have headNe : head ≠ pivot := by intro he; exact hne (by simp [he])
        have restNe : pivot ∉ rest := fun hv => hne (List.mem_cons_of_mem _ hv)
        by_cases hlo : head < pivot
        · have hhi : ¬ pivot < head := by omega
          simp only [List.filter_cons, show decide (head < pivot) = true by simp [hlo],
            show decide (pivot < head) = false by simp [hhi], if_true, if_false,
            List.cons_append]
          exact congrArg (head :: ·) (ih restNe restPairs)
        · have hhi : pivot < head := by omega
          have allHigh (value : ℕ) (hv : value ∈ rest) : pivot < value :=
            (headPairs value hv).resolve_left hlo
          have lowEmpty : rest.filter (fun value => decide (value < pivot)) = [] :=
            List.filter_eq_nil_iff.mpr (by
              intro value hv; have := allHigh value hv; simp; omega)
          have highAll : rest.filter (fun value => decide (pivot < value)) = rest :=
            List.filter_eq_self.mpr (by intro value hv; simp [allHigh value hv])
          simp [hlo, hhi, lowEmpty, highAll]
    · intro he
      have lowPairs : (tail.filter (fun value => decide (value < pivot))).Pairwise
          (fun a b => a < pivot ∨ pivot < b) := List.pairwise_of_forall_mem_list (by
        intro a ha b hb; exact Or.inl (of_decide_eq_true (List.mem_filter.mp ha).2))
      have highPairs : (tail.filter (fun value => decide (pivot < value))).Pairwise
          (fun a b => a < pivot ∨ pivot < b) := List.pairwise_of_forall_mem_list (by
        intro a ha b hb; exact Or.inr (of_decide_eq_true (List.mem_filter.mp hb).2))
      rw [he]
      exact List.pairwise_append.mpr ⟨lowPairs, highPairs, by
        intro a ha b hb; exact Or.inl (of_decide_eq_true (List.mem_filter.mp ha).2)⟩
  have failuresCount : failures.ncard = Nat.fib (2 * (pivot - 1) - 1) *
      Nat.fib (2 * (width + 1 - pivot) - 1) := by
    have he : failures = {p : List ℕ | p ∈ rotationAvoiders (width + 1) (width + 1) q ∧
        p.head? = some pivot ∧ p.tail =
          p.tail.filter (fun value => decide (value < pivot)) ++
          p.tail.filter (fun value => decide (pivot < value))} := by
      ext p
      constructor
      · rintro ⟨hp, hh⟩
        have hn := hp.1.1.nodup_iff.mpr List.nodup_range'
        have hne : pivot ∉ p.tail := (List.nodup_cons.mp (parentSplit p hp ▸ hn)).1
        exact ⟨hp.1, hp.2, (orderedIff p.tail hne).mp hh⟩
      · rintro ⟨hg, head, he⟩
        have hp : p ∈ parents := ⟨hg, head⟩
        have hn := hg.1.nodup_iff.mpr List.nodup_range'
        have hne : pivot ∉ p.tail := (List.nodup_cons.mp (parentSplit p hp ▸ hn)).1
        exact ⟨hp, (orderedIff p.tail hne).mpr he⟩
    rw [he]
    exact RotationAvoidanceFailureProduct.alternating_separated_circle_count
      (width + 1) pivot hpivot hupper
  let lift := fun value : ℕ => if value < pivot then value else value + 1
  let lower := fun value : ℕ => if value < pivot then value else value - 1
  have liftStrict : StrictMono lift := by
    intro a b hh; dsimp [lift]; split_ifs <;> omega
  have lowerLift (value : ℕ) : lower (lift value) = value := by
    dsimp [lower, lift]; split_ifs <;> omega
  let emit := fun p : List ℕ => pivot :: p.tail.map lift ++ [pivot + 1]
  have rangeInsertion : (pivot :: (List.range' 1 (width + 1)).map lift).Perm
      (List.range' 1 (width + 2)) := by
    have splitOld : List.range' 1 (width + 1) =
        List.range' 1 (pivot - 1) ++ List.range' pivot (width + 2 - pivot) := by
      have he := List.range'_append (s := 1) (m := pivot - 1)
        (n := width + 2 - pivot) (step := 1)
      simpa only [Nat.one_mul, show 1 + (pivot - 1) = pivot by omega,
        show pivot - 1 + (width + 2 - pivot) = width + 1 by omega] using he.symm
    have splitNew : List.range' 1 (width + 2) =
        List.range' 1 (pivot - 1) ++ pivot :: List.range' (pivot + 1) (width + 2 - pivot) := by
      rw [show pivot :: List.range' (pivot + 1) (width + 2 - pivot) =
        List.range' pivot ((width + 2 - pivot) + 1) by rw [List.range'_succ]]
      have he := List.range'_append (s := 1) (m := pivot - 1)
        (n := (width + 2 - pivot) + 1) (step := 1)
      simpa only [Nat.one_mul, show 1 + (pivot - 1) = pivot by omega,
        show pivot - 1 + ((width + 2 - pivot) + 1) = width + 2 by omega] using he.symm
    have lows : (List.range' 1 (pivot - 1)).map lift = List.range' 1 (pivot - 1) := by
      conv_rhs => rw [← List.map_id (List.range' 1 (pivot - 1))]
      apply List.map_congr_left
      intro value hv
      have hb := List.mem_range'_1.mp hv
      dsimp [lift]; split_ifs <;> omega
    have highs : (List.range' pivot (width + 2 - pivot)).map lift =
        List.range' (pivot + 1) (width + 2 - pivot) := by
      have he : (List.range' pivot (width + 2 - pivot)).map lift =
          (List.range' pivot (width + 2 - pivot)).map (1 + ·) := by
        apply List.map_congr_left
        intro value hv
        have hb := List.mem_range'_1.mp hv
        dsimp [lift]; split_ifs <;> omega
      rw [he, List.map_add_range']; congr 1; omega
    rw [splitOld, List.map_append, lows, highs, splitNew]
    exact (List.perm_middle (a := pivot) (l₁ := List.range' 1 (pivot - 1))
      (l₂ := List.range' (pivot + 1) (width + 2 - pivot))).symm
  have emitPerm (p : List ℕ) (hp : p ∈ parents) :
      (emit p).Perm (List.range' 1 (width + 2)) := by
    have hm := hp.1.1.map lift
    rw [parentSplit p hp, List.map_cons, show lift pivot = pivot + 1 by simp [lift]] at hm
    have moved : (p.tail.map lift ++ [pivot + 1]).Perm ((pivot + 1) :: p.tail.map lift) := by
      simpa using List.perm_middle (a := pivot + 1) (l₁ := p.tail.map lift) (l₂ := [])
    exact ((moved.trans hm).cons pivot).trans rangeInsertion
  have emitCycles (p : List ℕ) (hp : p ∈ parents) :
      ∀ shift < 4, ¬ Occurs (q.rotate shift) (p.tail.map lift ++ [pivot + 1]) := by
    have hg := rotatedGood p hp.1 1
    have ha := (all_cuts_iff_cycle_avoidance (width + 1) (by omega) q (p.rotate 1)
      (by decide) hg.1).mp hg
    have mapped : (p.rotate 1).map lift = p.tail.map lift ++ [pivot + 1] := by
      rw [parentSplit p hp]
      simp [List.rotate_cons_succ, lift]
    intro shift hs ho
    rw [← mapped] at ho
    have hr := (List.rotate_perm q shift).trans (by decide : q.Perm [1, 2, 3, 4])
    have hl : letters (q.rotate shift) = (q.rotate shift).length := by
      have hh : letters (q.rotate shift) = 4 := by simpa [letters] using hr.foldr_eq (f := max) 0
      simpa [q] using hh
    apply ha shift hs
    unfold Occurs at ho ⊢
    rw [hl] at ho ⊢
    exact (ArcherCyclicPadovanPatterns.contains_map_iff _ _ lift liftStrict).mp ho
  have targetIff (p : List ℕ) (hp : p ∈ parents) : Occurs q (emit p) ↔ ¬ ordered p := by
    constructor
    · intro ho hd
      have hc := (consecutive_endpoint_contraction (width + 2) pivot (p.tail.map lift) q
        (by omega) (Or.inl rfl) (emitPerm p hp)).mpr ⟨emitCycles p hp, ho⟩
      have test := (unique_bad_cut_iff (width + 2) (by omega) q (emit p)
        (by decide) (emitPerm p hp)).mp hc
      obtain ⟨chosen, hi, _, selected, _⟩ := ho
      change [chosen 2, chosen 4, chosen 1, chosen 3].Sublist
        (pivot :: (p.tail.map lift ++ [pivot + 1])) at selected
      have h12 : chosen 1 < chosen 2 := by simpa [q] using hi 1 (by omega) (by decide)
      have h23 : chosen 2 < chosen 3 := by simpa [q] using hi 2 (by omega) (by decide)
      have h34 : chosen 3 < chosen 4 := by simpa [q] using hi 3 (by omega) (by decide)
      have firstUsed : chosen 2 = pivot := by
        by_contra hn
        apply test.2.2.1
        refine ⟨chosen, hi, ?_, List.Sublist.of_cons_of_ne hn selected, by simp⟩
        intro rank hlo hhi
        apply (List.Sublist.of_cons_of_ne hn selected).subset
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [q]
      have pair : [chosen 4, chosen 1].Sublist (p.tail.map lift) := by
        have ht : [chosen 4, chosen 1, chosen 3].Sublist (p.tail.map lift ++ [pivot + 1]) :=
          selected.of_cons_cons
        have ht : [chosen 3, chosen 1, chosen 4].Sublist
            ((pivot + 1) :: (p.tail.map lift).reverse) := by simpa using ht.reverse
        simpa using ht.of_cons_cons.reverse
      have ht := pair.map lower
      have restored : (p.tail.map lift).map lower = p.tail := by
        simp [List.map_map, Function.comp_def, lowerLift]
      rw [restored] at ht
      have hh := List.pairwise_iff_forall_sublist.mp hd ht
      dsimp [lower] at hh
      split_ifs at hh <;> omega
    · intro hd
      obtain ⟨high, low, pair, hh⟩ : ∃ high low,
          [high, low].Sublist p.tail ∧ ¬ (high < pivot ∨ pivot < low) := by
        simpa only [ordered, List.pairwise_iff_forall_sublist, not_forall,
          Classical.not_imp, exists_prop] using hd
      have hn : pivot ∉ p.tail :=
        (List.nodup_cons.mp (parentSplit p hp ▸ hp.1.1.nodup_iff.mpr List.nodup_range')).1
      have highNe : high ≠ pivot := fun he => hn (he ▸ pair.subset (by simp))
      have lowNe : low ≠ pivot := fun he => hn (he ▸ pair.subset (by simp))
      have highBound : pivot < high := by omega
      have lowBound : low < pivot := by omega
      let chosen := fun rank : ℕ => if rank = 1 then lift low else if rank = 2 then pivot
        else if rank = 3 then pivot + 1 else lift high
      have liftLow : lift low = low := by simp [lift, lowBound]
      have liftHigh : lift high = high + 1 := by simp [lift, show ¬ high < pivot by omega]
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank < 4 at hhi; omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen, liftLow, liftHigh] <;> omega
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by change rank ≤ 4 at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl
        · change lift low ∈ pivot :: p.tail.map lift ++ [pivot + 1]
          exact List.mem_cons_of_mem _ (List.mem_append_left _
            (List.mem_map_of_mem (pair.subset (by simp : low ∈ _))))
        · simp [chosen, emit]
        · simp [chosen, emit]
        · change lift high ∈ pivot :: p.tail.map lift ++ [pivot + 1]
          exact List.mem_cons_of_mem _ (List.mem_append_left _
            (List.mem_map_of_mem (pair.subset (by simp : high ∈ _))))
      · simpa [q, chosen, emit] using
          ((pair.map lift).append (List.Sublist.refl [pivot + 1])).cons_cons pivot
  have emitMember (p : List ℕ) (hp : p ∈ accepted) : emit p ∈ target := by
    have hd : ¬ ordered p := fun hh => hp.2 ⟨hp.1, hh⟩
    refine ⟨emitPerm p hp.1, by simp [emit], ?_, ?_⟩
    · change ((pivot :: p.tail.map lift) ++ [pivot + 1]).getLast? = some (pivot + 1)
      rw [List.getLast?_append_cons]; rfl
    · exact (consecutive_endpoint_contraction (width + 2) pivot (p.tail.map lift) q
        (by omega) (Or.inl rfl) (emitPerm p hp.1)).mpr
          ⟨emitCycles p hp.1, (targetIff p hp.1).mpr hd⟩
  have decode (p : List ℕ) (hp : p ∈ parents) :
      pivot :: (emit p).tail.dropLast.map lower = p := by
    simp only [emit, List.cons_append, List.tail_cons, List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil, List.map_map, Function.comp_def,
      lowerLift]
    simpa using (parentSplit p hp).symm
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ p ∈ accepted, emit p = word := by
    obtain ⟨front, lastEq⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, wordEq⟩ : ∃ interior, word = pivot :: interior ++ [pivot + 1] := by
      cases front with
      | nil => have hh := hw.1.length_eq; simp [lastEq] at hh
      | cons head interior =>
        have hh : head = pivot := by simpa [lastEq] using hw.2.1
        exact ⟨interior, by simpa [hh] using lastEq⟩
    let p := pivot :: interior.map lower
    have notPivot : pivot ∉ interior := fun hv =>
      (List.nodup_cons.mp ((wordEq ▸ hw.1).nodup_iff.mpr List.nodup_range')).1
        (List.mem_append_left _ hv)
    have notNext : pivot + 1 ∉ interior := by
      have hn := List.nodup_append.mp
        (List.nodup_cons.mp ((wordEq ▸ hw.1).nodup_iff.mpr List.nodup_range')).2
      exact fun hv => hn.2.2 (pivot + 1) hv (pivot + 1) (by simp) rfl
    have restore : (interior.map lower).map lift = interior := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id interior]
      apply List.map_congr_left
      intro value hv
      have hn : value ≠ pivot := fun he => notPivot (he ▸ hv)
      have hn' : value ≠ pivot + 1 := fun he => notNext (he ▸ hv)
      dsimp [lift, lower]; split_ifs <;> omega
    have pPerm : p.Perm (List.range' 1 (width + 1)) := by
      have hh := (wordEq ▸ hw.1).trans rangeInsertion.symm
      have hh := List.Perm.cons_inv hh
      have move : ((pivot + 1) :: interior).Perm (interior ++ [pivot + 1]) := by
        simpa using (List.perm_middle (a := pivot + 1) (l₁ := interior) (l₂ := [])).symm
      have hh := (move.trans hh).map lower
      rw [List.map_map] at hh
      simpa [List.map_cons, show lower (pivot + 1) = pivot by simp [lower],
        Function.comp_def, lowerLift, p] using hh
    have hc := (consecutive_endpoint_contraction (width + 2) pivot interior q
      (by omega) (Or.inl rfl) (wordEq ▸ hw.1)).mp (wordEq ▸ hw.2.2.2)
    have hg : p ∈ rotationAvoiders (width + 1) (width + 1) q := by
      have mapped : (p.rotate 1).map lift = interior ++ [pivot + 1] := by
        simp only [p, List.rotate_cons_succ, List.rotate_zero, List.map_append,
          List.map_singleton, show lift pivot = pivot + 1 by simp [lift], restore]
      have hrot := (List.rotate_perm p 1).trans pPerm
      have hrotGood := (all_cuts_iff_cycle_avoidance (width + 1) (by omega) q (p.rotate 1)
        (by decide) hrot).mpr (by
          intro shift hs ho
          apply hc.1 shift hs
          rw [← mapped]
          have hr := (List.rotate_perm q shift).trans (by decide : q.Perm [1, 2, 3, 4])
          have hl : letters (q.rotate shift) = (q.rotate shift).length := by
            have hh : letters (q.rotate shift) = 4 := by
              simpa [letters] using hr.foldr_eq (f := max) 0
            simpa [q] using hh
          unfold Occurs at ho ⊢
          rw [hl] at ho ⊢
          exact (ArcherCyclicPadovanPatterns.contains_map_iff _ _ lift liftStrict).mpr ho)
      have back := rotatedGood (p.rotate 1) hrotGood width
      have lengthP : p.length = width + 1 := by simpa using pPerm.length_eq
      have he : (p.rotate 1).rotate width = p := by
        rw [List.rotate_rotate, show 1 + width = p.length by omega, List.rotate_length]
      exact he ▸ back
    have hp : p ∈ parents := ⟨hg, by simp [p]⟩
    have he : emit p = word := by simp only [emit, p, List.tail_cons, restore, ← wordEq]
    have notFail : p ∉ failures := by
      rintro ⟨_, hd⟩
      exact (targetIff p hp).mp (he.symm ▸ (wordEq.symm ▸ hc.2)) hd
    exact ⟨p, ⟨hp, notFail⟩, he⟩
  have cardTarget := Set.ncard_congr (s := accepted) (t := target) (fun p _ => emit p)
    emitMember (by
      intro p r hp hr he
      have hh := congrArg (fun word : List ℕ => pivot :: word.tail.dropLast.map lower) he
      rwa [decode p hp.1, decode r hr.1] at hh) (by
      intro word hw
      obtain ⟨p, hp, he⟩ := emitSurjective word hw
      exact ⟨p, hp, he⟩)
  have finiteParents : parents.Finite := by
    apply (List.finite_toSet (List.range' 1 (width + 1)).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1.1
  have subsetFailures : failures ⊆ parents := fun _ hp => hp.1
  have rejected := Set.ncard_sdiff_add_ncard_of_subset subsetFailures finiteParents
  have rooted_count (q : List ℕ) (patterns : List (List ℕ))
      (hletters : ∀ pattern ∈ patterns, letters pattern = pattern.length)
      (hreduction : ∀ tail, (1 :: tail).Perm (List.range' 1 (width + 1)) →
        ((1 :: tail) ∈ circularAvoiders (width + 1) q ↔
          ∀ pattern ∈ patterns, ¬ Occurs pattern tail)) :
      (circularAvoiders (width + 1) q).ncard =
        (Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns).ncard := by
    let emit := fun word : List ℕ => 1 :: word.map Nat.succ
    have shift (pattern word : List ℕ) (hpattern : pattern ∈ patterns) :
        Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
      unfold Occurs
      rw [hletters pattern hpattern]
      exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word Nat.succ
        (by intro low high hlt; omega)
    have emitPerm (word : List ℕ) (hword : word.Perm (List.range' 1 width)) :
        (emit word).Perm (List.range' 1 (width + 1)) := by
      have hrange : (List.range' 1 width).map Nat.succ = List.range' 2 width := by
        simpa only [show (fun value : ℕ => 1 + value) = Nat.succ by
          funext value; omega, Nat.reduceAdd] using
          List.map_add_range' (a := 1) 1 width 1
      simpa only [emit, hrange, List.range'_succ, Nat.reduceAdd, Nat.mul_one] using
        (hword.map Nat.succ).cons 1
    have emitMember (word : List ℕ)
        (hword : word ∈ Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns) :
        emit word ∈ circularAvoiders (width + 1) q := by
      apply (hreduction _ (emitPerm word hword.1)).mpr
      intro pattern hpattern
      exact fun hocc => hword.2 pattern hpattern ((shift pattern word hpattern).mp hocc)
    have emitInjective : Function.Injective emit := by
      intro first second heq
      exact List.map_injective_iff.mpr Nat.succ_injective (List.cons.inj heq).2
    have emitSurjective (circle : List ℕ)
        (hcircle : circle ∈ circularAvoiders (width + 1) q) :
        ∃ word ∈ Fishburn.FishburnClassicalDefs.classicalAvoiders width patterns,
          emit word = circle := by
      obtain ⟨tail, rfl⟩ : ∃ tail, circle = 1 :: tail := by
        cases circle with
        | nil => simp [circularAvoiders] at hcircle
        | cons head tail =>
          have hhead : head = 1 := by simpa using hcircle.2
          exact ⟨tail, by simp [hhead]⟩
      have htailPerm : tail.Perm (List.range' 2 width) := by
        have hp := hcircle.1.1
        rw [List.range'_succ] at hp
        exact List.Perm.cons_inv hp
      let word := tail.map (· - 1)
      have restore : word.map Nat.succ = tail := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id tail]
        apply List.map_congr_left
        intro value hvalue
        have := List.mem_range'.mp (htailPerm.mem_iff.mp hvalue)
        dsimp
        omega
      have wordPerm : word.Perm (List.range' 1 width) := by
        have hp := htailPerm.map (fun value => value - 1)
        simpa only [word, List.map_sub_range' (by omega : 1 ≤ 2), Nat.reduceSub] using hp
      have tailAvoid := (hreduction tail hcircle.1.1).mp hcircle
      refine ⟨word, ⟨wordPerm, ?_⟩, by simp only [emit, restore]⟩
      intro pattern hpattern hocc
      exact tailAvoid pattern hpattern
        (restore ▸ (shift pattern word hpattern).mpr hocc)
    exact (Set.ncard_congr (fun word _ => emit word) emitMember
      (fun first second _ _ heq => emitInjective heq) (by
        intro circle hcircle
        obtain ⟨word, hword, heq⟩ := emitSurjective circle hcircle
        exact ⟨word, hword, heq⟩)).symm
  have fibonacci : (circularAvoiders (width + 1) [1, 3, 2, 4]).ncard =
      Nat.fib (2 * width - 1) := by
    rw [rooted_count [1, 3, 2, 4] [[2, 1, 3], [4, 1, 3, 2]] (by
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl) (by
        intro tail hp
        simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] using (RotationAvoidanceCounts.minimum_rooted_reductions width tail hp).2.2)]
    exact RotationAvoidanceFibonacci.fibonacci_count width (by omega)
  have cycle (q : List ℕ) (hq : q.Perm [1, 2, 3, 4]) (shift : ℕ)
      (hshift : shift < 4) :
      (circularAvoiders (width + 1) (q.rotate shift)).ncard =
        (circularAvoiders (width + 1) q).ncard := by
    have qlength : q.length = 4 := by simpa using hq.length_eq
    have forward (pattern : List ℕ) (hlen : pattern.length = 4) (offset : ℕ)
        (word : List ℕ) (havoid : ∀ cut < 4, ¬ Occurs (pattern.rotate cut) word) :
        ∀ cut < 4, ¬ Occurs ((pattern.rotate offset).rotate cut) word := by
      intro cut hcut
      rw [List.rotate_rotate, ← List.rotate_mod, hlen]
      exact havoid _ (Nat.mod_lt _ (by omega))
    have restore : (q.rotate shift).rotate (4 - shift) = q := by
      rw [List.rotate_rotate, show shift + (4 - shift) = 4 by omega,
        ← qlength, List.rotate_length]
    have setEq : circularAvoiders (width + 1) (q.rotate shift) =
        circularAvoiders (width + 1) q := by
      ext word
      constructor <;> intro hword
      · have havoid := (all_cuts_iff_cycle_avoidance (width + 1) (by omega)
          (q.rotate shift) word ((List.rotate_perm q shift).trans hq) hword.1.1).mp hword.1
        refine ⟨(all_cuts_iff_cycle_avoidance (width + 1) (by omega) q word hq
          hword.1.1).mpr ?_, hword.2⟩
        simpa only [restore] using forward (q.rotate shift)
          (by simpa using qlength) (4 - shift) word havoid
      · have havoid := (all_cuts_iff_cycle_avoidance (width + 1) (by omega) q word hq
          hword.1.1).mp hword.1
        exact ⟨(all_cuts_iff_cycle_avoidance (width + 1) (by omega) (q.rotate shift)
          word ((List.rotate_perm q shift).trans hq) hword.1.1).mpr
            (forward q qlength shift word havoid), hword.2⟩
    rw [setEq]
  have count : (circularAvoiders (width + 1) q).ncard =
      (circularAvoiders (width + 1) [1, 3, 2, 4]).ncard := by
    simpa only [q, show ([1, 3, 2, 4] : List ℕ).rotate 2 = [2, 4, 1, 3] by decide]
      using cycle [1, 3, 2, 4] (by decide) 2 (by omega)
  change accepted.ncard + failures.ncard = parents.ncard at rejected
  rw [failuresCount, parentsCount, count, fibonacci] at rejected
  change target.ncard = _
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAlternatingContraction
