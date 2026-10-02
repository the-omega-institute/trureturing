/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum
   mirror-E: none(waiver:minimum-pattern-witnesses)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Splitting at one identifies suffix triples and both crossing pattern witnesses. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicDecreasingPrefixes
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenMinimum

open D5.S3.Combinatorics Nonnesting
open Fishburn.FishburnDefs Fishburn.FishburnBasicPrefixes

theorem minimum_pattern_tests (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
    (one : ℕ) (honebound : one < p.length) (hone : p.getD one 0 = 1) :
    (NonnestingDefs.Occurs [1, 3, 2, 4] p ↔
      ∃ first second third, one < first ∧ first < second ∧ second < third ∧
        third < p.length ∧ p.getD second 0 < p.getD first 0 ∧
        p.getD first 0 < p.getD third 0) ∧
    (NonnestingDefs.Occurs [1, 4, 2, 3] p ↔
      ∃ first second third, one < first ∧ first < second ∧ second < third ∧
        third < p.length ∧ p.getD second 0 < p.getD third 0 ∧
        p.getD third 0 < p.getD first 0) ∧
    (¬ NonnestingDefs.Occurs [1, 3, 2, 4] p →
      (NonnestingDefs.Occurs [2, 1, 4, 3] p ↔
        ∃ first second third, first < one ∧ one < second ∧ second < third ∧
          third < p.length ∧ p.getD first 0 < p.getD third 0 ∧
          p.getD third 0 < p.getD second 0) ∧
      (NonnestingDefs.Occurs [3, 1, 2, 4] p ↔
        ∃ first second third, first < one ∧ one < second ∧ second < third ∧
          third < p.length ∧ p.getD second 0 < p.getD first 0 ∧
          p.getD first 0 < p.getD third 0)) := by
  have hdecreasing := prefix_through_one_decreasing n p hperm hfish one honebound hone
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hpositive (index : ℕ) (hindex : index < p.length) : 1 ≤ p.getD index 0 := by
    have hmem : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hindex]
      exact List.getElem_mem hindex
    have hrange := hperm.mem_iff.mp hmem
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, _, hvalue⟩ := hrange
    omega
  have hafter (index : ℕ) (hindex : index < p.length) (hne : index ≠ one) :
      1 < p.getD index 0 := by
    have hpos := hpositive index hindex
    have hvalue : p.getD index 0 ≠ 1 := by
      intro heq
      exact hne ((List.getD_inj hindex honebound hnodup).mp (heq.trans hone.symm))
    omega
  have hindices (low middle high top : ℕ)
      (hsub : [low, middle, high, top].Sublist p) :
      ∃ first second third fourth, first < second ∧ second < third ∧ third < fourth ∧
        fourth < p.length ∧ p.getD first 0 = low ∧ p.getD second 0 = middle ∧
        p.getD third 0 = high ∧ p.getD fourth 0 = top := by
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let first := positions ⟨0, by simp⟩
    let second := positions ⟨1, by simp⟩
    let third := positions ⟨2, by simp⟩
    let fourth := positions ⟨3, by simp⟩
    refine ⟨first.val, second.val, third.val, fourth.val, ?_, ?_, ?_, fourth.is_lt,
      ?_, ?_, ?_, ?_⟩
    · exact positions.strictMono (by change (0 : ℕ) < 1; omega)
    · exact positions.strictMono (by change (1 : ℕ) < 2; omega)
    · exact positions.strictMono (by change (2 : ℕ) < 3; omega)
    · rw [List.getD_eq_get]
      simpa [first] using (hpositions ⟨0, by simp⟩).symm
    · rw [List.getD_eq_get]
      simpa [second] using (hpositions ⟨1, by simp⟩).symm
    · rw [List.getD_eq_get]
      simpa [third] using (hpositions ⟨2, by simp⟩).symm
    · rw [List.getD_eq_get]
      simpa [fourth] using (hpositions ⟨3, by simp⟩).symm
  have hselected (positions : List ℕ) (horder : positions.Pairwise (· < ·))
      (hbound : ∀ index ∈ positions, index < p.length) :
      (positions.map (fun index => p.getD index 0)).Sublist p := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => p.getD index 0)).length →
        Fin p.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        hbound _ (List.getElem_mem (by simpa using index.is_lt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp horder first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem p 0 _
  have hmake (pattern : List ℕ) (hpattern : pattern.Perm [1, 2, 3, 4])
      (values : ℕ → ℕ)
      (hstep : ∀ rank, 1 ≤ rank → rank < 4 → values rank < values (rank + 1))
      (hsub : (pattern.map values).Sublist p) :
      ArrowWilfDefs.Contains pattern [] 4 p := by
    refine ⟨values, hstep, ?_, hsub, by simp⟩
    intro rank hlower hupper
    apply hsub.subset
    apply List.mem_map.mpr
    refine ⟨rank, hpattern.mem_iff.mpr ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hbuild132 (first second third : ℕ)
      (hfirst : one < first) (hsecond : first < second) (hthird : second < third)
      (hbound : third < p.length) (hlower : p.getD second 0 < p.getD first 0)
      (hupper : p.getD first 0 < p.getD third 0) :
      NonnestingDefs.Occurs [1, 3, 2, 4] p := by
    have hmin := hafter second (by omega) (by omega)
    have hsub := hselected [one, first, second, third]
      (by simp [List.pairwise_cons]; omega) (by
        intro index hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl <;> omega)
    let values : ℕ → ℕ := fun rank => if rank = 1 then 1
      else if rank = 2 then p.getD second 0
      else if rank = 3 then p.getD first 0 else p.getD third 0
    change ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 p
    apply hmake _ (by decide) values
    · intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hc with rfl | rfl | rfl <;> simpa [values]
    · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
        Nat.reduceEqDiff, hone] using hsub
  have h132 : NonnestingDefs.Occurs [1, 3, 2, 4] p ↔
      ∃ first second third, one < first ∧ first < second ∧ second < third ∧
        third < p.length ∧ p.getD second 0 < p.getD first 0 ∧
        p.getD first 0 < p.getD third 0 := by
    constructor
    · rintro ⟨values, hstep, _, hsub, _⟩
      have h12 := hstep 1 (by omega) (by change 1 < 4; omega)
      have h23 := hstep 2 (by omega) (by change 2 < 4; omega)
      have h34 := hstep 3 (by omega) (by change 3 < 4; omega)
      norm_num only [Nat.reduceAdd] at h12 h23 h34
      simp only [List.map_cons, List.map_nil] at hsub
      obtain ⟨first, second, third, fourth, hfs, hst, htf, hb, hvf, hvs, hvt, hvlast⟩ :=
        hindices _ _ _ _ hsub
      have honeleft : one < second := by
        by_contra hnot
        have := hdecreasing first second hfs (by omega)
        omega
      exact ⟨second, third, fourth, honeleft, hst, htf, hb, by omega, by omega⟩
    · rintro ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩
      exact hbuild132 first second third hf hs ht hb hl hu
  refine ⟨h132, ?_, ?_⟩
  · constructor
    · rintro ⟨values, hstep, _, hsub, _⟩
      have h12 := hstep 1 (by omega) (by change 1 < 4; omega)
      have h23 := hstep 2 (by omega) (by change 2 < 4; omega)
      have h34 := hstep 3 (by omega) (by change 3 < 4; omega)
      norm_num only [Nat.reduceAdd] at h12 h23 h34
      simp only [List.map_cons, List.map_nil] at hsub
      obtain ⟨first, second, third, fourth, hfs, hst, htf, hb, hvf, hvs, hvt, hvlast⟩ :=
        hindices _ _ _ _ hsub
      have honeleft : one < second := by
        by_contra hnot
        have := hdecreasing first second hfs (by omega)
        omega
      exact ⟨second, third, fourth, honeleft, hst, htf, hb, by omega, by omega⟩
    · rintro ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩
      have hmin := hafter second (by omega) (by omega)
      have hsub := hselected [one, first, second, third]
        (by simp [List.pairwise_cons]; omega) (by
          intro index hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl <;> omega)
      let values : ℕ → ℕ := fun rank => if rank = 1 then 1
        else if rank = 2 then p.getD second 0
        else if rank = 3 then p.getD third 0 else p.getD first 0
      change ArrowWilfDefs.Contains [1, 4, 2, 3] [] 4 p
      apply hmake _ (by decide) values
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hc with rfl | rfl | rfl <;> simpa [values]
      · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
          Nat.reduceEqDiff, hone] using hsub
  · intro havoid
    constructor
    · constructor
      · rintro ⟨values, hstep, _, hsub, _⟩
        have h12 := hstep 1 (by omega) (by change 1 < 4; omega)
        have h23 := hstep 2 (by omega) (by change 2 < 4; omega)
        have h34 := hstep 3 (by omega) (by change 3 < 4; omega)
        norm_num only [Nat.reduceAdd] at h12 h23 h34
        simp only [List.map_cons, List.map_nil] at hsub
        obtain ⟨first, second, third, fourth, hfs, hst, htf, hb, hvf, hvs, hvt, hvlast⟩ :=
          hindices _ _ _ _ hsub
        have hfirst : first < one := by
          by_contra hnot
          have hne : first ≠ one := by
            intro heq
            subst first
            have := hpositive second (by omega)
            omega
          exact havoid (hbuild132 first second third (by omega) hfs hst
            (by omega) (by omega) (by omega))
        have hthird : one < third := by
          by_contra hnot
          have := hdecreasing second third hst (by omega)
          omega
        exact ⟨first, third, fourth, hfirst, hthird, htf, hb, by omega, by omega⟩
      · rintro ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩
        have hmin := hafter first (by omega) (by omega)
        have hsub := hselected [first, one, second, third]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> omega)
        let values : ℕ → ℕ := fun rank => if rank = 1 then 1
          else if rank = 2 then p.getD first 0
          else if rank = 3 then p.getD third 0 else p.getD second 0
        change ArrowWilfDefs.Contains [2, 1, 4, 3] [] 4 p
        apply hmake _ (by decide) values
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> simpa [values]
        · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
            Nat.reduceEqDiff, hone] using hsub
    · constructor
      · rintro ⟨values, hstep, _, hsub, _⟩
        have h12 := hstep 1 (by omega) (by change 1 < 4; omega)
        have h23 := hstep 2 (by omega) (by change 2 < 4; omega)
        have h34 := hstep 3 (by omega) (by change 3 < 4; omega)
        norm_num only [Nat.reduceAdd] at h12 h23 h34
        simp only [List.map_cons, List.map_nil] at hsub
        obtain ⟨first, second, third, fourth, hfs, hst, htf, hb, hvf, hvs, hvt, hvlast⟩ :=
          hindices _ _ _ _ hsub
        have hfirst : first < one := by
          by_contra hnot
          have hne : first ≠ one := by
            intro heq
            subst first
            have := hpositive second (by omega)
            omega
          exact havoid (hbuild132 first second fourth (by omega) hfs
            (by omega) hb (by omega) (by omega))
        have hthird : one < third := by
          by_contra hnot
          have := hdecreasing second third hst (by omega)
          omega
        exact ⟨first, third, fourth, hfirst, hthird, htf, hb, by omega, by omega⟩
      · rintro ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩
        have hmin := hafter second (by omega) (by omega)
        have hsub := hselected [first, one, second, third]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> omega)
        let values : ℕ → ℕ := fun rank => if rank = 1 then 1
          else if rank = 2 then p.getD second 0
          else if rank = 3 then p.getD first 0 else p.getD third 0
        change ArrowWilfDefs.Contains [3, 1, 2, 4] [] 4 p
        apply hmake _ (by decide) values
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> simpa [values]
        · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
            Nat.reduceEqDiff, hone] using hsub

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenMinimum
