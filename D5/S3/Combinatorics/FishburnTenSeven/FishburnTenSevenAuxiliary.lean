/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenAuxiliary
   mirror-E: none(waiver:auxiliary-maximum-decomposition)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Maximum decomposition of Fishburn permutations avoiding 213. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicAscents
import D5.S3.Combinatorics.Fishburn.FishburnBasicThreePatterns
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliary

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open Fishburn.FishburnBasicAscents Fishburn.FishburnBasicThreePatterns
open Fishburn.FishburnBasicInsertion

theorem H_head_decomposition (size : ℕ) (p : List ℕ) :
    p ∈ avoiders (size + 1) [[2, 1, 3]] ↔
    ∃ q : ↥(avoiders size [[2, 1, 3]]),
      p = (size + 1) :: q.val ∨ p = 1 :: q.val.map (· + 1) := by
  conv_lhs => simp only [avoiders, Set.mem_ofPred_eq, List.mem_singleton, forall_eq]
  have hmaximumPerm (q : List ℕ) :
      ((size + 1) :: q).Perm (List.range' 1 (size + 1)) ↔
        q.Perm (List.range' 1 size) := by
    have hmove : ((size + 1) :: List.range' 1 size).Perm
        (List.range' 1 (size + 1)) := by
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    exact ⟨fun hp => (hp.trans hmove.symm).cons_inv,
      fun hp => (hp.cons _).trans hmove⟩
  have hmaximum (q : List ℕ) (hq : q.Perm (List.range' 1 size)) :
      (IsFishburn ((size + 1) :: q) ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] ((size + 1) :: q)) ↔
      (IsFishburn q ∧ ¬ NonnestingDefs.Occurs [2, 1, 3] q) := by
    have hbound : ∀ value ∈ q, value < size + 1 := by
      intro value hv
      have := hq.mem_iff.mp hv
      simp only [List.mem_range'_1] at this
      omega
    have hf := isFishburn_insertIdx_max_iff q (size + 1) 0 (by omega) hbound
    have ho := maximum_213_test size q hq 0 (by omega)
    have heligible : ∀ before later, before + 1 = 0 → 0 ≤ later → later < q.length →
        q.getD before 0 ≠ q.getD later 0 + 1 := by
      intro before later he
      omega
    simpa [heligible] using
      (and_congr hf (not_congr ho))
  have hshift (q : List ℕ) (hq : ∀ value ∈ q, 1 ≤ value) :
      NonnestingDefs.Occurs [2, 1, 3] (q.map (· + 1)) ↔
        NonnestingDefs.Occurs [2, 1, 3] q := by
    change ArrowWilfDefs.Contains [2, 1, 3] [] 3 _ ↔
      ArrowWilfDefs.Contains [2, 1, 3] [] 3 _
    constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      have hpositive (rank : ℕ) (hl : 1 ≤ rank) (hh : rank ≤ 3) :
          2 ≤ values rank := by
        obtain ⟨value, hv, he⟩ := List.mem_map.mp (hmem rank hl hh)
        have := hq value hv
        omega
      refine ⟨fun rank => values rank - 1, ?_, ?_, ?_, by simp⟩
      · intro rank hl hh
        have := hpositive rank hl (by omega)
        have := hpositive (rank + 1) (by omega) (by omega)
        have := hstep rank hl hh
        dsimp only
        omega
      · intro rank hl hh
        obtain ⟨value, hv, he⟩ := List.mem_map.mp (hmem rank hl hh)
        simpa [← he] using hv
      · have hcancel : (q.map (· + 1)).map (· - 1) = q := by
          rw [List.map_map]
          conv_rhs => rw [← List.map_id q]
          apply List.map_congr_left
          intro value _
          exact Nat.add_sub_cancel value 1
        have hmapped := hsub.map (· - 1)
        rw [hcancel] at hmapped
        simpa [List.map_map, Function.comp_def] using hmapped
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      refine ⟨fun rank => values rank + 1, ?_, ?_, ?_, by simp⟩
      · intro rank hl hh
        exact Nat.add_lt_add_right (hstep rank hl hh) 1
      · intro rank hl hh
        exact List.mem_map_of_mem (hmem rank hl hh)
      · simpa [List.map_map, Function.comp_def] using hsub.map (· + 1)
  have hminimum (q : List ℕ) (hq : q.Perm (List.range' 1 size)) :
      (IsFishburn (1 :: q.map (· + 1)) ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] (1 :: q.map (· + 1))) ↔
      (IsFishburn q ∧ ¬ NonnestingDefs.Occurs [2, 1, 3] q) := by
    have hpositive : ∀ value ∈ q, 1 ≤ value := by
      intro value hv
      have := hq.mem_iff.mp hv
      simp only [List.mem_range'_1] at this
      omega
    have hfish : IsFishburn (1 :: q.map (· + 1)) ↔ IsFishburn q := by
      let child := 1 :: q.map (· + 1)
      have hlength : child.length = q.length + 1 := by simp [child]
      have hentry (index : ℕ) (hi : index < q.length) :
          child.getD (index + 1) 0 = q.getD index 0 + 1 := by
        rw [List.getD_cons_succ, List.getD_eq_getElem _ 0 (by simpa using hi),
          List.getD_eq_getElem q 0 hi]
        simp
      have hafter (index : ℕ) (hp : 0 < index) (hh : index < child.length) :
          child.getD index 0 = q.getD (index - 1) 0 + 1 := by
        have he : index - 1 + 1 = index := by omega
        have hb : index - 1 < q.length := by omega
        simpa only [he] using hentry (index - 1) hb
      change IsFishburn child ↔ IsFishburn q
      constructor
      · intro hchild before later hgap hlater hbad
        apply hchild (before + 1) (later + 1) (by omega) (by omega)
        rw [hentry before (by omega), hentry later hlater,
          hentry (before + 1) (by omega)]
        constructor <;> omega
      · intro hparent before later hgap hlater hbad
        by_cases hz : before = 0
        · subst before
          have he := hbad.1
          rw [show child.getD 0 0 = 1 from rfl, hafter later (by omega) hlater] at he
          omega
        · apply hparent (before - 1) (later - 1) (by omega) (by omega)
          rw [hafter before (by omega) (by omega), hafter later (by omega) hlater,
            hafter (before + 1) (by omega) (by omega)] at hbad
          have he : before + 1 - 1 = before - 1 + 1 := by omega
          rw [he] at hbad
          constructor <;> omega
    have ho : NonnestingDefs.Occurs [2, 1, 3] (1 :: q.map (· + 1)) ↔
        NonnestingDefs.Occurs [2, 1, 3] (q.map (· + 1)) := by
      change ArrowWilfDefs.Contains [2, 1, 3] [] 3 _ ↔
        ArrowWilfDefs.Contains [2, 1, 3] [] 3 _
      constructor
      · rintro ⟨values, hstep, _, hsub, _⟩
        have h12 := hstep 1 (by omega) (by omega)
        change values 1 < values 2 at h12
        have hsubtail : ([2, 1, 3].map values).Sublist (q.map (· + 1)) := by
          rcases List.sublist_cons_iff.mp hsub with htail | ⟨rest, he, hr⟩
          · exact htail
          · have hehead : values 2 = 1 := by simpa using congrArg List.head? he
            have hm : values 1 ∈ q.map (· + 1) := hr.subset (by
              have herest : rest = [values 1, values 3] := by
                simpa using (List.cons.inj he).2.symm
              simp [herest])
            obtain ⟨value, hv, hevalue⟩ := List.mem_map.mp hm
            have := hpositive value hv
            omega
        refine ⟨values, hstep, ?_, hsubtail, by simp⟩
        intro rank hl hh
        apply hsubtail.subset
        apply List.mem_map_of_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega
      · rintro ⟨values, hstep, hmem, hsub, _⟩
        refine ⟨values, hstep, ?_, hsub.cons 1, by simp⟩
        intro rank hl hh
        exact List.mem_cons_of_mem 1 (hmem rank hl hh)
    exact and_congr hfish (not_congr (ho.trans (hshift q hpositive)))
  have hminimumPerm (q : List ℕ) (hq : q.Perm (List.range' 1 size)) :
      (1 :: q.map (· + 1)).Perm (List.range' 1 (size + 1)) := by
    have hm := (hq.map (· + 1)).cons 1
    simpa [List.range'_succ, ← List.range'_succ_left] using hm
  constructor
  · rintro ⟨hperm, hfish, havoid⟩
    have hnonempty : p ≠ [] := by
      have := hperm.length_eq
      simp only [List.length_range'] at this
      intro he
      simp [he] at this
    obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hnonempty
    have hhead : head = size + 1 ∨ head = 1 := by
      by_cases he : head = size + 1
      · exact Or.inl he
      right
      have hmem : size + 1 ∈ head :: tail := by
        apply hperm.mem_iff.mpr
        simp only [List.mem_range'_1]
        omega
      obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hmem
      have hbase : (left ++ right).Perm (List.range' 1 size) := by
        apply (hmaximumPerm (left ++ right)).mp
        exact (List.perm_middle.symm.trans (hsplit ▸ hperm))
      have hinsert : (left ++ right).insertIdx left.length (size + 1) =
          head :: tail := by
        rw [hsplit]
        have hins : ∀ first second : List ℕ,
            (first ++ second).insertIdx first.length (size + 1) =
              first ++ (size + 1) :: second := by
          intro first second
          induction first with
          | nil => simp
          | cons value rest ih => simpa [List.insertIdx_succ_cons] using ih
        exact hins left right
      have hnodec : ∀ first second, first < second → second < left.length →
          ¬ (left ++ right).getD second 0 < (left ++ right).getD first 0 := by
        intro first second hfs hs hdesc
        apply havoid
        rw [← hinsert]
        exact (maximum_213_test size (left ++ right) hbase left.length
          (by simp)).mpr (Or.inr ⟨first, second, hfs, hs, hdesc⟩)
      have hleftpos : 0 < left.length := by
        cases left with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            exact False.elim (he hsplit.1)
        | cons value rest => simp
      have hascent : (head :: tail).getD 0 0 < (head :: tail).getD 1 0 := by
        by_cases hlen : left.length = 1
        · have hat : (head :: tail).getD 1 0 = size + 1 := by
            rw [← hinsert, ← hlen]
            have hcut : left.length ≤ (left ++ right).length := by simp
            rw [List.getD_eq_getElem _ 0 (by
              rw [List.length_insertIdx_of_le_length hcut]; omega)]
            exact List.getElem_insertIdx_self _
          have hb := hperm.mem_iff.mp List.mem_cons_self
          simp only [List.mem_range'_1] at hb
          simpa only [List.getD_cons_zero, hat] using (by omega : head < size + 1)
        · have hnodup := hbase.nodup_iff.mpr (List.nodup_range' 1)
          have hneq : (left ++ right).getD 0 0 ≠ (left ++ right).getD 1 0 := by
            intro heq
            have := (List.getD_inj (by simp; omega) (by simp; omega) hnodup).mp heq
            omega
          have hn := hnodec 0 1 (by omega) (by omega)
          have hbefore (index : ℕ) (hi : index < left.length) :
              (head :: tail).getD index 0 = (left ++ right).getD index 0 := by
            rw [← hinsert, List.getD_eq_getElem _ 0 (by
              rw [List.length_insertIdx_of_le_length (by simp)]; simp; omega),
              List.getElem_insertIdx_of_lt hi,
              List.getD_eq_getElem _ 0 (by simp; omega)]
          rw [hbefore 0 hleftpos, hbefore 1 (by omega)]
          omega
      have hlength : 1 < (head :: tail).length := by
        rw [hsplit, List.length_append, List.length_cons]
        omega
      rcases (isFishburn_iff_ascent_predecessor (size + 1) (head :: tail) hperm).mp
        hfish 0 hlength hascent with hone | ⟨earlier, hearlier, _⟩
      · simpa using hone
      · omega
    rcases hhead with rfl | rfl
    · have hqperm := (hmaximumPerm tail).mp hperm
      refine ⟨⟨tail, hqperm, ?_⟩, Or.inl rfl⟩
      simpa only [List.mem_singleton, forall_eq] using
        (hmaximum tail hqperm).mp ⟨hfish, havoid⟩
    · have htailperm : tail.Perm (List.range' 2 size) := by
        have hp := hperm
        rw [List.range'_succ] at hp
        exact hp.cons_inv
      let q := tail.map (· - 1)
      have hqperm : q.Perm (List.range' 1 size) := by
        have hp := htailperm.map (· - 1)
        simpa [q, List.range'_succ_left, List.map_map, Function.comp_def] using hp
      have he : q.map (· + 1) = tail := by
        simp only [q, List.map_map]
        conv_rhs => rw [← List.map_id tail]
        apply List.map_congr_left
        intro value hv
        have := htailperm.mem_iff.mp hv
        simp only [List.mem_range'_1] at this
        simp only [Function.comp_apply, id_eq]
        omega
      refine ⟨⟨q, hqperm, ?_⟩, Or.inr ?_⟩
      · simpa only [List.mem_singleton, forall_eq] using
          (hminimum q hqperm).mp (by simpa [he] using And.intro hfish havoid)
      · simp [he]
  · rintro ⟨q, rfl | rfl⟩
    · exact ⟨(hmaximumPerm q.val).mpr q.property.1,
        (hmaximum q.val q.property.1).mpr
          (by simpa only [List.mem_singleton, forall_eq] using q.property.2)⟩
    · exact ⟨hminimumPerm q.val q.property.1,
        (hminimum q.val q.property.1).mpr
          (by simpa only [List.mem_singleton, forall_eq] using q.property.2)⟩

noncomputable def H_maximum_equiv (size : ℕ) (hsize : 1 ≤ size) :
    ↥(avoiders size [[2, 1, 3]]) ≃
      Σ cut : Fin size, ↥(avoiders (size - cut.val - 1) [[2, 1, 3]]) := by
  classical
  have hconstruct : ∀ cut rest : ℕ, ∀ q : ↥(avoiders rest [[2, 1, 3]]),
      (List.range' 1 cut ++ (cut + rest + 1) :: q.val.map (· + cut)).Perm
          (List.range' 1 (cut + rest + 1)) ∧
        IsFishburn (List.range' 1 cut ++ (cut + rest + 1) :: q.val.map (· + cut)) ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3]
          (List.range' 1 cut ++ (cut + rest + 1) :: q.val.map (· + cut)) := by
    intro cut
    induction cut with
    | zero =>
        intro rest q
        simpa [avoiders] using (H_head_decomposition rest ((rest + 1) :: q.val)).mpr
          ⟨q, Or.inl rfl⟩
    | succ cut ih =>
        intro rest q
        let word := List.range' 1 cut ++ (cut + rest + 1) :: q.val.map (· + cut)
        let parent : ↥(avoiders (cut + rest + 1) [[2, 1, 3]]) :=
          ⟨word, by simpa [avoiders, word] using ih rest q⟩
        have hword : List.range' 1 (cut + 1) ++
            (cut + 1 + rest + 1) :: q.val.map (· + (cut + 1)) =
            1 :: word.map (· + 1) := by
          simp only [word, List.range'_succ, List.cons_append, List.map_append,
            List.map_cons, List.map_map]
          rw [← List.range'_succ_left]
          simp [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        have hnext := (H_head_decomposition (cut + rest + 1)
          (1 :: word.map (· + 1))).mpr ⟨parent, Or.inr rfl⟩
        rw [hword]
        simpa only [show cut + 1 + rest + 1 = cut + rest + 1 + 1 by omega,
          avoiders, Set.mem_ofPred_eq, List.mem_singleton, forall_eq] using hnext
  have hexists : ∀ total : ℕ, 1 ≤ total → ∀ p : ↥(avoiders total [[2, 1, 3]]),
      ∃ code : Σ cut : Fin total, ↥(avoiders (total - cut.val - 1) [[2, 1, 3]]),
        p.val = List.range' 1 code.1.val ++ total :: code.2.val.map (· + code.1.val) := by
    intro total
    induction total using Nat.strong_induction_on with
    | h total ih =>
        intro ht p
        obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : total ≠ 0)
        obtain ⟨q, hq | hq⟩ := (H_head_decomposition previous p.val).mp p.property
        · have hs : previous + 1 - 0 - 1 = previous := by omega
          refine ⟨⟨⟨0, by omega⟩, hs.symm ▸ q⟩, ?_⟩
          simpa using hq
        · by_cases hz : previous = 0
          · subst previous
            have hnil : q.val = [] := by
              have hl := q.property.1.length_eq
              simpa using List.length_eq_zero_iff.mp hl
            refine ⟨⟨⟨0, by omega⟩, q⟩, ?_⟩
            simpa [hnil] using hq
          · obtain ⟨⟨cut, suffix⟩, hparent⟩ := ih previous (by omega) (by omega) q
            have hs : previous + 1 - (cut.val + 1) - 1 =
                previous - cut.val - 1 := by omega
            refine ⟨⟨⟨cut.val + 1, by omega⟩,
              ⟨suffix.val, by simpa only [hs] using suffix.property⟩⟩, ?_⟩
            rw [hq, hparent]
            simp only [List.map_append, List.map_cons, List.map_map,
              List.range'_succ, List.cons_append]
            rw [← List.range'_succ_left]
            simp [Function.comp_def, Nat.add_assoc]
  let word (code : Σ cut : Fin size, ↥(avoiders (size - cut.val - 1) [[2, 1, 3]])) : List ℕ :=
    List.range' 1 code.1.val ++ size :: code.2.val.map (· + code.1.val)
  have hwordmem (code : Σ cut : Fin size, ↥(avoiders (size - cut.val - 1) [[2, 1, 3]])) :
      (word code).Perm (List.range' 1 size) ∧ IsFishburn (word code) ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] (word code) := by
    have he : code.1.val + (size - code.1.val - 1) + 1 = size := by
      have := code.1.is_lt
      omega
    simpa only [he] using hconstruct code.1.val (size - code.1.val - 1) code.2
  have hposition (code : Σ cut : Fin size, ↥(avoiders (size - cut.val - 1) [[2, 1, 3]])) :
      (word code).getD code.1.val 0 = size := by
    dsimp only [word]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hinjective : Function.Injective word := by
    intro first second he
    have hperm := (hwordmem first).1
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hlength : (word first).length = size := by
      simpa using hperm.length_eq
    have hpositions : first.1.val = second.1.val := by
      apply (List.getD_inj (by rw [hlength]; exact first.1.is_lt)
        (by rw [hlength]; exact second.1.is_lt) hnodup).mp
      rw [hposition first, he, hposition second]
    rcases first with ⟨firstCut, firstSuffix⟩
    rcases second with ⟨secondCut, secondSuffix⟩
    have hcuts : firstCut = secondCut := Fin.ext hpositions
    subst secondCut
    have hmaps : firstSuffix.val.map (· + firstCut.val) =
        secondSuffix.val.map (· + firstCut.val) := by
      exact (List.cons.inj (List.append_cancel_left he)).2
    have hsuffix : firstSuffix = secondSuffix := by
      apply Subtype.ext
      exact (List.map_inj_right (fun first second he => Nat.add_right_cancel he)).mp hmaps
    subst secondSuffix
    rfl
  let encode (p : ↥(avoiders size [[2, 1, 3]])) :
      Σ cut : Fin size, ↥(avoiders (size - cut.val - 1) [[2, 1, 3]]) :=
    Classical.choose (hexists size hsize p)
  have hencode (p : ↥(avoiders size [[2, 1, 3]])) : p.val = word (encode p) :=
    Classical.choose_spec (hexists size hsize p)
  refine
    { toFun := encode
      invFun := fun code => ⟨word code, by simpa [avoiders] using hwordmem code⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    exact Subtype.ext (hencode p).symm
  · intro code
    apply hinjective
    exact (hencode ⟨word code, by simpa [avoiders] using hwordmem code⟩).symm

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliary
