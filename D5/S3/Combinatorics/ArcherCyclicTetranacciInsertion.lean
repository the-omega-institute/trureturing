/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciInsertion
   mirror-E: none(waiver:preservation-under-low-arc-insertion)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Inserting a circularly increasing low arc preserves circular 1324 avoidance. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import D5.S3.Combinatorics.ArcherCyclicTetranacciPatterns
import D5.S3.Combinatorics.ArcherCyclicPadovanRotation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciInsertion

open ArcherCyclicDefs ArcherCyclicTetranacciPatterns

/-- The four insertion branches share this formula, including the empty low
tail in the branch `k = 1`. -/
def insertWord (k : ℕ) (v : List ℕ) : List ℕ :=
  1 :: (v.map (fun z => k + z) ++ List.range' 2 (k - 1))

/-- A new circular occurrence is either wholly in the high arc or would
require a forbidden 213 in that arc. -/
theorem circular_1324_insert_iff (k : ℕ) (s : List ℕ) (hk : 1 ≤ k)
    (hv : (1 :: s).Perm (List.range' 1 (s.length + 1))) :
    (∃ r < (insertWord k (1 :: s)).length,
      ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((insertWord k (1 :: s)).rotate r)) ↔
    (∃ r < (1 :: s).length,
      ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: s).rotate r)) := by
  let cut (w : List ℕ) : Prop :=
    ∃ pre post : List ℕ, ∃ a b c d : ℕ,
      w = pre ++ a :: post ∧ a < c ∧ c < b ∧ b < d ∧
        [b, c, d].Sublist (post ++ pre)
  have cut_iff (w : List ℕ) :
      (∃ r < w.length, ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)) ↔
        cut w := by
    constructor
    · intro hh
      obtain ⟨j, hj, a, c, b, d, t, hroot, hac, hcb, hbd, hs⟩ :=
        (ArcherCyclicPadovanMinimumRooted.circular_1324_iff_minimum_rooted w).mp hh
      have hdrop : w.drop j ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp only [List.length_drop, List.length_nil] at hlen
        omega
      obtain ⟨z, post, hz⟩ := List.exists_cons_of_ne_nil hdrop
      have hrot := List.rotate_eq_drop_append_take (le_of_lt hj)
      rw [hz] at hrot
      rw [hrot] at hroot
      have hza : z = a := by simpa using (congrArg List.head? hroot)
      subst z
      have ht : t = post ++ w.take j := by
        simpa using (congrArg List.tail hroot).symm
      refine ⟨w.take j, post, a, b, c, d, ?_, hac, hcb, hbd, ?_⟩
      · simpa [hz] using (List.take_append_drop j w).symm
      · exact ht ▸ hs
    · rintro ⟨pre, post, a, b, c, d, hcut, hac, hcb, hbd, hs⟩
      apply (ArcherCyclicPadovanMinimumRooted.circular_1324_iff_minimum_rooted w).mpr
      have hr : pre.length < w.length := by
        rw [hcut]
        simp only [List.length_append, List.length_cons]
        omega
      refine ⟨pre.length, hr, a, c, b, d, post ++ pre, ?_, hac, hcb, hbd, hs⟩
      rw [hcut, List.rotate_append_length_eq]
      simp
  have hcutInsert : cut (insertWord k (1 :: s)) ↔ cut (1 :: s) := by
    let v := 1 :: s
    let p := v.map (fun z => k + z)
    let l := List.range' 2 (k - 1)
    let w := insertWord k v
    have hvnd : v.Nodup := hv.nodup_iff.mpr List.nodup_range'
    have hvpos (z : ℕ) (hz : z ∈ v) : 1 ≤ z :=
      List.left_le_of_mem_range' (hv.mem_iff.mp hz)
    have hppos (z : ℕ) (hz : z ∈ p) : k < z := by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      have ha1 := hvpos a ha
      omega
    have hlbound (z : ℕ) (hz : z ∈ l) : 2 ≤ z ∧ z ≤ k := by
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hz
      omega
    have hnd : w.Nodup := by
      rw [show w = 1 :: (p ++ l) by rfl, List.nodup_cons, List.nodup_append']
      refine ⟨?_, hvnd.map (by intro a b heq; dsimp at heq; omega),
        List.nodup_range', ?_⟩
      · simp only [List.mem_append]
        rintro (h | h)
        · have := hppos 1 h; omega
        · have := hlbound 1 h; omega
      · intro a ha hb
        have := hppos a ha
        have := hlbound a hb
        omega
    have hkeep (t : ℕ) (x : List ℕ) (hx : ∀ a ∈ x, t < a) :
        x.filter (fun a => decide (t < a)) = x := by
      apply List.filter_eq_self.mpr
      intro a ha
      simp [hx a ha]
    have hdrop (t : ℕ) (x : List ℕ) (hx : ∀ a ∈ x, a ≤ t) :
        x.filter (fun a => decide (t < a)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      simp [show ¬ t < a by have := hx a ha; omega]
    have hlowfilter := hdrop k l (fun a ha => (hlbound a ha).2)
    have hhighfilter := hkeep k p hppos
    have hsplit3 (b c d : ℕ) (x y : List ℕ)
        (hs : [b, c, d].Sublist (x ++ y)) :
        [b, c, d].Sublist x ∨ ([b, c].Sublist x ∧ d ∈ y) ∨
          (b ∈ x ∧ [c, d].Sublist y) ∨ [b, c, d].Sublist y := by
      obtain ⟨a, z, heq, hax, hzy⟩ := List.sublist_append_iff.mp hs
      rcases a with (_ | ⟨e, _ | ⟨f, _ | ⟨g, a⟩⟩⟩)
      · simp only [List.nil_append] at heq
        subst z
        exact Or.inr (Or.inr (Or.inr hzy))
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨List.singleton_sublist.mp hax, hzy⟩))
      · simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        exact Or.inr (Or.inl ⟨hax, List.singleton_sublist.mp hzy⟩)
      · have heq' : a ++ z = [] := by
          have hh := congrArg (List.drop 3) heq
          simpa only [List.cons_append, List.drop_succ_cons,
            List.drop_zero, List.drop_nil] using hh.symm
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp heq'
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl, _⟩
        exact Or.inl hax
    constructor
    · intro hbad
      by_contra hgood
      have havoid : ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 v := by
        intro hb
        apply hgood
        obtain ⟨r, hr, a, c, b, d, t, hroot, hac, hcb, hbd, hs⟩ :=
          (ArcherCyclicPadovanMinimumRooted.circular_1324_iff_minimum_rooted v).mp
            ⟨0, by simp [v], by simpa using hb⟩
        have hsplitRoot : ∃ pre post, v = pre ++ a :: post ∧
            t = post ++ pre := by
          have hdrop : v.drop r ≠ [] := by
            intro hnil
            have hlen := congrArg List.length hnil
            simp only [List.length_drop, List.length_nil] at hlen
            omega
          obtain ⟨z, post, hz⟩ := List.exists_cons_of_ne_nil hdrop
          have hrot := List.rotate_eq_drop_append_take (le_of_lt hr)
          rw [hz] at hrot
          rw [hrot] at hroot
          have hza : z = a := by simpa using (congrArg List.head? hroot)
          subst z
          have ht : t = post ++ v.take r := by
            simpa using (congrArg List.tail hroot).symm
          refine ⟨v.take r, post, ?_, ht⟩
          simpa [hz] using (List.take_append_drop r v).symm
        obtain ⟨pre, post, hcut, ht⟩ := hsplitRoot
        exact ⟨pre, post, a, b, c, d, hcut, hac, hcb, hbd, ht ▸ hs⟩
      have hsmall (z : ℕ) (hz : z ∈ s) : 1 < z := by
        have hlo := hvpos z (by simp [v, hz])
        have hne : z ≠ 1 := by
          intro heq
          exact hvnd.notMem (heq ▸ hz)
        omega
      have hno213 (b c d : ℕ) (hcb : c < b) (hbd : b < d)
          (hs : [b, c, d].Sublist p) : False := by
        have hb : k < b := hppos b (hs.subset (by simp))
        have hc : k < c := hppos c (hs.subset (by simp))
        have hd : k < d := hppos d (hs.subset (by simp))
        have hs' : [b - k, c - k, d - k].Sublist v := by
          simpa [p, List.map_map, Function.comp_def] using hs.map (fun z => z - k)
        rcases List.cons_sublist_cons'.mp hs' with hs' | ⟨heq, _⟩
        · exact rooted_suffix_avoids_213 s hsmall havoid
            (b - k) (c - k) (d - k) (by omega) (by omega) hs'
        · omega
      obtain ⟨pre, post, a, b, c, d, hcut, hac, hcb, hbd, hs⟩ := hbad
      change w = pre ++ a :: post at hcut
      have hamem : a ∈ w := by rw [hcut]; simp
      have hapos : 1 ≤ a := by
        change a ∈ 1 :: (p ++ l) at hamem
        rcases List.mem_cons.mp hamem with rfl | ha
        · omega
        · rcases List.mem_append.mp ha with ha | ha
          · have := hppos a ha; omega
          · have := hlbound a ha; omega
      have hmatch (pre' post' : List ℕ) (hcut' : w = pre' ++ a :: post') :
          pre = pre' ∧ post = post' := by
        have hd := hnd
        rw [hcut] at hd
        have haPre : a ∉ pre := by
          intro ha
          exact (List.nodup_append'.mp hd).2.2 ha (by simp)
        have haPost : a ∉ post := hd.of_append_right.notMem
        obtain ⟨h₁, _, h₂⟩ := List.append_cons_inj_of_notMem haPre haPost |>.mp
          (hcut.symm.trans hcut')
        exact ⟨h₁, h₂⟩
      have extract (x y : List ℕ) (hx : ∀ z ∈ x, z ≤ k)
          (hy : ∀ z ∈ y, z ≤ k) (hc : k < c)
          (hs : [b, c, d].Sublist (x ++ p ++ y)) : False := by
        have hb : k < b := by omega
        have hd : k < d := by omega
        have hs' := hs.filter (fun z => decide (k < z))
        have hsel := hkeep k [b, c, d] (by
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl <;> assumption)
        rw [hsel, List.filter_append, List.filter_append,
          hdrop k x hx, hdrop k y hy, hhighfilter] at hs'
        simp only [List.nil_append, List.append_nil] at hs'
        exact hno213 b c d hcb hbd hs'
      by_cases ha1 : a = 1
      · subst a
        obtain ⟨rfl, hpost⟩ := hmatch [] (p ++ l) (by rfl)
        rw [hpost, List.append_nil] at hs
        by_cases hc : k < c
        · exact extract [] l (by simp) (fun z hz => (hlbound z hz).2) hc
            (by simpa using hs)
        · rcases hsplit3 b c d p l hs with hh | ⟨hh, _⟩ | ⟨hb, hh⟩ | hh
          · have := hppos c (hh.subset (by simp)); omega
          · have := hppos c (hh.subset (by simp)); omega
          · have := hppos b hb
            have := hlbound d (hh.subset (by simp))
            omega
          · have hbc : [b, c].Sublist l :=
              (List.sublist_append_left [b, c] [d]).trans hh
            have := (List.pairwise_lt_range' (s := 2) 1 (by decide : 0 < 1)
              (n := k - 1)).forall_sublist hbc
            omega
      · by_cases haHigh : k < a
        · have haP : a ∈ p := by
            change a ∈ 1 :: (p ++ l) at hamem
            rcases List.mem_cons.mp hamem with heq | hmem
            · exact False.elim (ha1 heq)
            · rcases List.mem_append.mp hmem with hm | hm
              · exact hm
              · have := hlbound a hm; omega
          obtain ⟨a₀, ha₀, hea⟩ := List.mem_map.mp haP
          obtain ⟨x, y, hvcut, _⟩ := List.eq_append_cons_of_mem ha₀
          have hcut' : w = (1 :: x.map (fun z => k + z)) ++ a ::
              (y.map (fun z => k + z) ++ l) := by
            simp [w, insertWord, hvcut, hea, List.map_append, List.append_assoc, l]
          obtain ⟨hpre, hpost⟩ := hmatch _ _ hcut'
          rw [hpre, hpost] at hs
          have hxpos (z : ℕ) (hz : z ∈ x.map (fun z => k + z)) : k < z := by
            apply hppos z
            dsimp [p]
            rw [hvcut, List.map_append]
            simp [hz]
          have hypos (z : ℕ) (hz : z ∈ y.map (fun z => k + z)) : k < z := by
            apply hppos z
            dsimp [p]
            rw [hvcut, List.map_append]
            simp [hz]
          have hs' := hs.filter (fun z => decide (k < z))
          have hsel := hkeep k [b, c, d] (by
            intro z hz
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl | rfl <;> omega)
          have h1drop : ([1] : List ℕ).filter (fun z => decide (k < z)) = [] :=
            hdrop k [1] (by simpa using hk)
          rw [hsel] at hs'
          simp only [List.filter_append, List.filter_cons] at hs'
          simp only [hlowfilter, hkeep k _ hxpos, hkeep k _ hypos,
            show decide (k < 1) = false by simp [show ¬ k < 1 by omega],
            Bool.false_eq_true, ↓reduceIte, List.append_nil] at hs'
          have hsOld : [b - k, c - k, d - k].Sublist (y ++ x) := by
            simpa [List.map_append, List.map_map, Function.comp_def] using
              hs'.map (fun z => z - k)
          apply hgood
          refine ⟨x, y, a₀, b - k, c - k, d - k, hvcut, ?_, ?_, ?_, hsOld⟩
          all_goals omega
        · have habound : 2 ≤ a ∧ a ≤ k := by omega
          let x := List.range' 2 (a - 2)
          let y := List.range' (a + 1) (k - a)
          have hlsplit : l = x ++ a :: y := by
            dsimp [l, x, y]
            calc
              _ = List.range' 2 ((a - 2) + (k - a + 1)) := by congr 1; omega
              _ = List.range' 2 (a - 2) ++
                  List.range' (2 + (a - 2)) (k - a + 1) := List.range'_append_1.symm
              _ = _ := by
                rw [List.range'_succ]
                rw [show 2 + (a - 2) = a by omega]
          obtain ⟨hpre, hpost⟩ := hmatch (1 :: (p ++ x)) y (by
            change 1 :: (p ++ l) = _
            rw [hlsplit]
            simp [List.append_assoc])
          rw [hpre, hpost] at hs
          have hxbound (z : ℕ) (hz : z ∈ x) : z < a := by
            obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hz
            omega
          have hybound (z : ℕ) (hz : z ∈ y) : a < z ∧ z ≤ k := by
            obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hz
            omega
          by_cases hc : k < c
          · exact extract (y ++ [1]) x
              (by intro z hz; simp only [List.mem_append, List.mem_singleton] at hz
                  rcases hz with hz | rfl
                  · exact (hybound z hz).2
                  · exact hk)
              (by intro z hz; have := hxbound z hz; omega) hc
              (by simpa [List.append_assoc] using hs)
          · have hs' := hs.filter (fun z => decide (a < z))
            have hsel := hkeep a [b, c, d] (by
              intro z hz
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with rfl | rfl | rfl <;> omega)
            have hpx := hkeep a p (by
              intro z hz; have := hppos z hz; omega)
            have hxx := hdrop a x (by
              intro z hz; have := hxbound z hz; omega)
            have hyx := hkeep a y (fun z hz => (hybound z hz).1)
            rw [hsel] at hs'
            simp only [List.filter_append, List.filter_cons] at hs'
            simp only [hpx, hxx, hyx,
              show decide (a < 1) = false by simp [show ¬ a < 1 by omega],
              Bool.false_eq_true, ↓reduceIte, List.append_nil] at hs'
            rcases hsplit3 b c d y p hs' with hh | ⟨hh, _⟩ | ⟨_, hh⟩ | hh
            · have hbc : [b, c].Sublist y :=
                (List.sublist_append_left [b, c] [d]).trans hh
              have := (List.pairwise_lt_range' (s := a + 1) 1 (by decide : 0 < 1)
                (n := k - a)).forall_sublist hbc
              omega
            · have := (List.pairwise_lt_range' (s := a + 1) 1 (by decide : 0 < 1)
                (n := k - a)).forall_sublist hh
              omega
            · have := hppos c (hh.subset (by simp)); omega
            · have := hppos c (hh.subset (by simp)); omega
    · rintro ⟨pre, post, a, b, c, d, hcut, hac, hcb, hbd, hs⟩
      refine ⟨1 :: pre.map (fun z => k + z),
        post.map (fun z => k + z) ++ l,
        k + a, k + b, k + c, k + d, ?_, by omega, by omega, by omega, ?_⟩
      · simp [insertWord, hcut, List.map_append, List.append_assoc, l]
      · have hs' := hs.map (fun z => k + z)
        have hemb : ((post ++ pre).map (fun z => k + z)).Sublist
            ((post.map (fun z => k + z) ++ l) ++
              1 :: pre.map (fun z => k + z)) := by
          simp only [List.map_append]
          have hh := (List.Sublist.refl (post.map (fun z => k + z))).append
            (List.sublist_append_right (l ++ [1]) (pre.map (fun z => k + z)))
          simp [List.append_assoc] at hh ⊢
        exact hs'.trans hemb
  exact (cut_iff _).trans (hcutInsert.trans (cut_iff _).symm)

end D5.S3.Combinatorics.ArcherCyclicTetranacciInsertion
