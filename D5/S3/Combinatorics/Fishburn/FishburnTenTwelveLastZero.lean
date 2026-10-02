/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTwelveLastZero
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTwelveLastZero
   mirror-E: none(waiver:last-zero-history-decomposition)
   anchors: []
   utility: none
   digest: The first entry uniquely recovers the last zero insertion and its positive suffix. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTwelveCodes
import D5.S3.Combinatorics.Fishburn.FishburnBasicInitialValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTwelveLastZero

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic1243 FishburnBasicPatterns FishburnBasicParents
open FishburnBasicInitialValues
open FishburnTenTwelvePaths

def endpoint : (n : ℕ) → (p : List ℕ) → (steps : ℕ) → PositiveHistory n p steps → List ℕ
  | _, p, 0, _ => p
  | n, p, steps + 1, ⟨site, tail⟩ =>
    endpoint (n + 1) (p.insertIdx site.val (n + 1)) steps tail

theorem last_zero_bijection (n : ℕ) :
    Nonempty ((Σ cut : Fin (n + 1),
      (base : avoiders cut.val [[1, 2, 4, 3], [3, 1, 2, 4]]) ×
        PositiveHistory (cut.val + 1) ((cut.val + 1) :: base.val) (n - cut.val)) ≃
          avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]) := by
  classical
  have hbounded (size : ℕ) (word : List ℕ)
      (hp : word.Perm (List.range' 1 size)) :
      word.filter (fun value => value ≤ size) = word := by
    apply List.filter_eq_self.mpr
    intro value hm
    have hr := hp.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hb, heq⟩ := hr
    simpa only [decide_eq_true_eq] using (show value ≤ size by omega)
  have hfilter_insert (bound : ℕ) (word : List ℕ) (site value : ℕ)
      (hsite : site ≤ word.length) (hvalue : bound < value) :
      (word.insertIdx site value).filter (fun entry => entry ≤ bound) =
        word.filter (fun entry => entry ≤ bound) := by
    induction word generalizing site with
    | nil =>
      have hs : site = 0 := by simpa using hsite
      subst site
      simp [show ¬ value ≤ bound by omega]
    | cons head tail ih =>
      cases site with
      | zero => simp [show ¬ value ≤ bound by omega]
      | succ site =>
        simp only [List.insertIdx_succ_cons, List.filter_cons]
        rw [ih site (by simp only [List.length_cons] at hsite; omega)]
  have hprepend (size : ℕ) (word : List ℕ)
      (hp : word ∈ avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]]) :
      (size + 1) :: word ∈ avoiders (size + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] := by
    have hmax : ∀ value ∈ word, value < size + 1 := by
      intro value hm
      have hr := hp.1.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hr
      obtain ⟨offset, hb, heq⟩ := hr
      omega
    refine ⟨?_, ?_, ?_⟩
    · apply (hp.1.cons (size + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    · apply (isFishburn_insertIdx_max_iff word (size + 1) 0 (by omega) hmax).mpr
      exact ⟨hp.2.1, by intro before later heq; omega⟩
    · intro pattern hpattern hocc
      have hc : pattern = [1, 2, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · have ht := (maximum_1243_test size word hp.1 0 (by omega)).mp hocc
        rcases ht with hold | ⟨_, second, _, _, hb, _⟩
        · exact hp.2.2 _ (by simp) hold
        · omega
      · have ht := ((maximum_pattern_tests size word hp.1 0 (by omega)).2.1).mp hocc
        rcases ht with hold | ⟨_, _, third, _, _, hb, _⟩
        · exact hp.2.2 _ (by simp) hold
        · omega
  have hvalid : ∀ steps size word,
      word ∈ avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]] →
      ∀ history : PositiveHistory size word steps,
        endpoint size word steps history ∈
          avoiders (size + steps) [[1, 2, 4, 3], [3, 1, 2, 4]] := by
    intro steps
    induction steps with
    | zero => intro size word hp history; simpa only [endpoint, Nat.add_zero] using hp
    | succ steps ih =>
      rintro size word hp ⟨site, tail⟩
      simpa only [endpoint, Nat.add_assoc, Nat.add_comm 1] using
        ih (size + 1) (word.insertIdx site.val (size + 1)) site.property.2.2 tail
  have hhead : ∀ steps size word, ∀ history : PositiveHistory size word steps,
      (endpoint size word steps history).getD 0 0 = word.getD 0 0 := by
    intro steps
    induction steps with
    | zero => intro size word history; rfl
    | succ steps ih =>
      rintro size word ⟨site, tail⟩
      rw [endpoint, ih]
      have hlen := List.length_insertIdx_of_le_length site.property.2.1 (size + 1)
      rw [List.getD_eq_getElem _ 0 (by omega),
        List.getElem_insertIdx_of_lt site.property.1,
        List.getD_eq_getElem word 0 (by omega)]
  have htrim : ∀ steps size word, ∀ history : PositiveHistory size word steps,
      ∀ bound, bound ≤ size →
        (endpoint size word steps history).filter (fun value => value ≤ bound) =
          word.filter (fun value => value ≤ bound) := by
    intro steps
    induction steps with
    | zero => intro size word history bound hb; rfl
    | succ steps ih =>
      rintro size word ⟨site, tail⟩ bound hb
      rw [endpoint, ih (size + 1)]
      · exact hfilter_insert bound word site.val (size + 1) site.property.2.1 (by omega)
      · omega
  have hinjective : ∀ steps size word,
      word ∈ avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]] →
      Function.Injective (endpoint size word steps) := by
    intro steps
    induction steps with
    | zero =>
      intro size word hp first second heq
      exact @Subsingleton.elim PUnit.{1} _ first second
    | succ steps ih =>
      intro size word hp
      rintro ⟨⟨first, hfirst⟩, firstTail⟩ ⟨⟨second, hsecond⟩, secondTail⟩ heq
      have hf := htrim steps (size + 1) (word.insertIdx first (size + 1))
        firstTail (size + 1) (by omega)
      have hs := htrim steps (size + 1) (word.insertIdx second (size + 1))
        secondTail (size + 1) (by omega)
      rw [hbounded _ _ hfirst.2.2.1] at hf
      rw [hbounded _ _ hsecond.2.2.1] at hs
      have hchildren : word.insertIdx first (size + 1) =
          word.insertIdx second (size + 1) := by
        rw [← hf, ← hs]
        exact congrArg (fun p : List ℕ => p.filter (fun value => value ≤ size + 1)) heq
      have hentries :
          (⟨(word, first), hp, hfirst.2.1, hfirst.2.2⟩ : {entry : List ℕ × ℕ //
            entry.1 ∈ avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]] ∧
              entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (size + 1) ∈
                avoiders (size + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]}) =
          ⟨(word, second), hp, hsecond.2.1, hsecond.2.2⟩ :=
        (maximum_insertion_bijection size [[1, 2, 4, 3], [3, 1, 2, 4]]).1
          (Subtype.ext hchildren)
      have hsites : first = second := congrArg (fun entry => entry.val.2) hentries
      subst second
      have htails := ih (size + 1) _ hfirst.2.2 heq
      cases htails
      rfl
  have hrealize : ∀ steps size word target,
      1 ≤ size → word ∈ avoiders size [[1, 2, 4, 3], [3, 1, 2, 4]] →
      target ∈ avoiders (size + steps) [[1, 2, 4, 3], [3, 1, 2, 4]] →
      target.filter (fun value => value ≤ size) = word →
      target.getD 0 0 = word.getD 0 0 →
      ∃ history : PositiveHistory size word steps, endpoint size word steps history = target := by
    intro steps
    induction steps with
    | zero =>
      intro size word target hsize hword htarget hfilter hh
      have heq : target = word := by
        simp only [Nat.add_zero] at htarget
        rwa [hbounded _ _ htarget.1] at hfilter
      exact ⟨PUnit.unit, heq.symm⟩
    | succ steps ih =>
      intro size word target hsize hword htarget hfilter hh
      let child := target.filter (fun value => value ≤ size + 1)
      have hchild : child ∈ avoiders (size + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] :=
        initial_values_avoider _ (size + (steps + 1)) target htarget (size + 1) (by omega)
      have hchildfilter : child.filter (fun value => value ≤ size) = word := by
        dsimp [child]
        rw [List.filter_filter]
        convert hfilter using 1
        apply List.filter_congr
        intro value hm
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      have hwordbound : word.getD 0 0 ≤ size := by
        have hl : word.length = size := by simpa using hword.1.length_eq
        have hm : word.getD 0 0 ∈ word := by
          rw [List.getD_eq_getElem word 0 (by omega)]
          exact List.getElem_mem (by omega)
        have hr := hword.1.mem_iff.mp hm
        simp only [List.mem_range', Nat.one_mul] at hr
        obtain ⟨offset, hb, heq⟩ := hr
        omega
      have hchildhead : child.getD 0 0 = target.getD 0 0 := by
        cases target with
        | nil => simp [child]
        | cons head tail =>
          have hb : head ≤ size + 1 := by simpa only [List.getD_cons_zero] using
            (show ((head :: tail).getD 0 0 ≤ size + 1) by omega)
          simp [child, hb]
      obtain ⟨entry, hentry⟩ :=
        (maximum_insertion_bijection size [[1, 2, 4, 3], [3, 1, 2, 4]]).2 ⟨child, hchild⟩
      have hinsert : entry.val.1.insertIdx entry.val.2 (size + 1) = child :=
        congrArg Subtype.val hentry
      have hparentEq : entry.val.1 = word := by
        rw [← hinsert, hfilter_insert size entry.val.1 entry.val.2 (size + 1)
          entry.property.2.1 (by omega), hbounded _ _ entry.property.1.1] at hchildfilter
        exact hchildfilter
      rcases entry with ⟨⟨parent, site⟩, hp, hs, ha⟩
      dsimp only at hparentEq hinsert hs ha
      subst parent
      have hsitepositive : 0 < site := by
        by_contra hnot
        have hz : site = 0 := by omega
        subst site
        have hhchild : child.getD 0 0 = size + 1 := by rw [← hinsert]; simp
        have hhmax : size + 1 = word.getD 0 0 := hhchild.symm.trans (hchildhead.trans hh)
        omega
      have htarget' : target ∈ avoiders ((size + 1) + steps)
          [[1, 2, 4, 3], [3, 1, 2, 4]] := by
        have hindex : size + 1 + steps = size + (steps + 1) := by omega
        simpa only [hindex] using htarget
      have hfilter' : target.filter (fun value => value ≤ size + 1) =
          word.insertIdx site (size + 1) := hinsert.symm
      have hhead' : target.getD 0 0 = (word.insertIdx site (size + 1)).getD 0 0 := by
        rw [hinsert]
        exact hchildhead.symm
      obtain ⟨tail, htail⟩ := ih (size + 1) (word.insertIdx site (size + 1)) target
        (by omega) ha htarget' hfilter' hhead'
      exact ⟨⟨⟨site, hsitepositive, hs, ha⟩, tail⟩, htail⟩
  let Pieces := Σ cut : Fin (n + 1),
    (base : avoiders cut.val [[1, 2, 4, 3], [3, 1, 2, 4]]) ×
      PositiveHistory (cut.val + 1) ((cut.val + 1) :: base.val) (n - cut.val)
  let assemble : Pieces → List ℕ := fun entry =>
    endpoint (entry.1.val + 1) ((entry.1.val + 1) :: entry.2.1.val)
      (n - entry.1.val) entry.2.2
  have hmember (entry : Pieces) : assemble entry ∈
      avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] := by
    have hv := hvalid (n - entry.1.val) (entry.1.val + 1)
      ((entry.1.val + 1) :: entry.2.1.val) (hprepend _ _ entry.2.1.property) entry.2.2
    have hb := entry.1.isLt
    have hindex : entry.1.val + 1 + (n - entry.1.val) = n + 1 := by omega
    simpa only [hindex] using hv
  have hassembleHead (entry : Pieces) : (assemble entry).getD 0 0 = entry.1.val + 1 := by
    exact hhead _ _ _ entry.2.2
  have hassembleFilter (entry : Pieces) :
      (assemble entry).filter (fun value => value ≤ entry.1.val) = entry.2.1.val := by
    have ht := htrim (n - entry.1.val) (entry.1.val + 1)
      ((entry.1.val + 1) :: entry.2.1.val) entry.2.2 entry.1.val (by omega)
    simpa [hbounded _ _ entry.2.1.property.1] using ht
  have hassembleInj : Function.Injective assemble := by
    rintro ⟨firstCut, firstPrefix, firstPath⟩ ⟨secondCut, secondPrefix, secondPath⟩ heq
    have hf := hassembleHead ⟨firstCut, firstPrefix, firstPath⟩
    have hs := hassembleHead ⟨secondCut, secondPrefix, secondPath⟩
    have hcuts : firstCut = secondCut := by
      apply Fin.ext
      have hh := congrArg (fun word : List ℕ => word.getD 0 0) heq
      rw [hf, hs] at hh
      change firstCut.val + 1 = secondCut.val + 1 at hh
      omega
    subst secondCut
    have hprefs : firstPrefix = secondPrefix := by
      apply Subtype.ext
      rw [← hassembleFilter ⟨firstCut, firstPrefix, firstPath⟩,
        ← hassembleFilter ⟨firstCut, secondPrefix, secondPath⟩]
      exact congrArg (fun word : List ℕ => word.filter (fun value => value ≤ firstCut.val)) heq
    subst secondPrefix
    have hpaths := hinjective _ _ _ (hprepend _ _ firstPrefix.property) heq
    cases hpaths
    rfl
  have hassembleSurj (target : List ℕ)
      (htarget : target ∈ avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]) :
      ∃ entry : Pieces, assemble entry = target := by
    have hlen : target.length = n + 1 := by simpa using htarget.1.length_eq
    have hnodup : target.Nodup := htarget.1.nodup_iff.mpr (List.nodup_range' 1)
    have hheadmem : target.getD 0 0 ∈ target := by
      rw [List.getD_eq_getElem target 0 (by omega)]
      exact List.getElem_mem (by omega)
    have hr := htarget.1.mem_iff.mp hheadmem
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hb, heq⟩ := hr
    let cut := target.getD 0 0 - 1
    have hcut : cut ≤ n := by dsimp [cut]; omega
    have hheadvalue : target.getD 0 0 = cut + 1 := by dsimp [cut]; omega
    let base := target.filter (fun value => value ≤ cut)
    have hprefix : base ∈ avoiders cut [[1, 2, 4, 3], [3, 1, 2, 4]] :=
      initial_values_avoider _ (n + 1) target htarget cut (by omega)
    have hstart : target.filter (fun value => value ≤ cut + 1) = (cut + 1) :: base := by
      cases target with
      | nil => simp at hlen
      | cons head tail =>
        have hh : head = cut + 1 := hheadvalue
        have hnot : cut + 1 ∉ tail := by
          rw [← hh]
          exact (List.nodup_cons.mp hnodup).1
        have hf : tail.filter (fun value => value ≤ cut + 1) =
            tail.filter (fun value => value ≤ cut) := by
          apply List.filter_congr
          intro value hm
          have hne : value ≠ cut + 1 := by intro he; exact hnot (he ▸ hm)
          simp only [decide_eq_decide]
          omega
        dsimp [base]
        rw [hh]
        simp [hf]
    have htarget' : target ∈ avoiders ((cut + 1) + (n - cut))
        [[1, 2, 4, 3], [3, 1, 2, 4]] := by
      have hindex : cut + 1 + (n - cut) = n + 1 := by omega
      simpa only [hindex] using htarget
    obtain ⟨history, hhistory⟩ := hrealize (n - cut) (cut + 1) ((cut + 1) :: base)
      target (by omega) (hprepend cut base hprefix) htarget' hstart hheadvalue
    exact ⟨⟨⟨cut, by omega⟩, ⟨base, hprefix⟩, history⟩, hhistory⟩
  let correspondence : Pieces → avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] :=
    fun entry => ⟨assemble entry, hmember entry⟩
  refine ⟨Equiv.ofBijective correspondence ⟨?_, ?_⟩⟩
  · intro first second heq
    exact hassembleInj (congrArg Subtype.val heq)
  · intro target
    obtain ⟨entry, heq⟩ := hassembleSurj target.val target.property
    exact ⟨entry, Subtype.ext heq⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTwelveLastZero
