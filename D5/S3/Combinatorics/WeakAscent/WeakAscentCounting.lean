/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentCounting
   mirror-E: none(waiver:weak-ascent-descendant-counts)
   anchors: [mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: The common rule recursively counts all finite-depth weak-ascent extensions. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentChildren
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentCounting

open WeakAscentDefs WeakAscentGrowth WeakAscentStates WeakAscentChildren

def treeCount : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | depth + 1, height, slack =>
    ∑ index : Fin height ⊕ Fin slack,
      treeCount depth (childLabel height slack index).1 (childLabel height slack index).2

def weakExtensions (e : List ℕ) (depth : ℕ) : Set (List ℕ) :=
  {f | f ∈ weakAvoiders (e.length + depth) ∧ f.take e.length = e}

theorem weak_extensions_count (depth : ℕ) (e : List ℕ) (hempty : e ≠ [])
    (he : IsWeakAscent e) (havoid : ¬ Contains210 e) :
    (weakExtensions e depth).ncard = treeCount depth (weakLabel e).1 (weakLabel e).2 := by
  classical
  have weak_avoiders_finite (n : ℕ) : (weakAvoiders n).Finite := by
    have coordinate_bound (sequence : List ℕ) (hweak : IsWeakAscent sequence) (index : ℕ)
        (hindex : index < sequence.length) : sequence.getD index 0 ≤ index := by
      have hbound := hweak index hindex
      by_cases hzero : index = 0
      · simpa [hzero] using hbound
      · have hfilter := List.length_filter_le
          (fun pair : ℕ × ℕ => decide (pair.1 ≤ pair.2))
          ((sequence.take index).zip (sequence.take index).tail)
        simp only [List.length_zip, List.length_tail, List.length_take] at hfilter
        simp only [if_neg hzero] at hbound
        unfold wasc at hbound
        omega
    let decode (coordinates : Fin n → Fin (n + 1)) : List ℕ :=
      List.ofFn fun index => (coordinates index).val
    apply (Set.finite_univ.image decode).subset
    intro sequence hmember
    have hlength : sequence.length = n := hmember.1
    let coordinates : Fin n → Fin (n + 1) := fun index =>
      ⟨sequence.getD index.val 0, by
        have hindex : index.val < sequence.length := by simp [hlength]
        have hbound := coordinate_bound sequence hmember.2.1 index.val hindex
        omega⟩
    refine ⟨coordinates, Set.mem_univ _, ?_⟩
    apply List.ext_getElem
    · simp [decode, hlength]
    · intro index hleft hright
      simp only [decode, List.getElem_ofFn, coordinates]
      exact List.getD_eq_getElem sequence 0 hright
  have finite_extensions (base : List ℕ) (depth : ℕ) : (weakExtensions base depth).Finite :=
    (weak_avoiders_finite (base.length + depth)).subset fun _ hmember => hmember.1
  let (base : List ℕ) (depth : ℕ) : Fintype (weakExtensions base depth) :=
    (finite_extensions base depth).fintype
  have prefix_member (f : List ℕ) (length : ℕ) (hweak : IsWeakAscent f)
      (hno : ¬ Contains210 f) (hlength : length ≤ f.length) :
      f.take length ∈ weakAvoiders length := by
    have prefix_read (index : ℕ) (hindex : index < length) :
        (f.take length).getD index 0 = f.getD index 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hindex]
    refine ⟨by simp [List.length_take, min_eq_left hlength], ?_, ?_⟩
    · intro index hindex
      have hindex' : index < length := by simpa [List.length_take, min_eq_left hlength]
        using hindex
      rw [prefix_read index hindex', List.take_take, min_eq_left (by omega)]
      exact hweak index (by omega)
    · rintro ⟨top, bottom, last, htop, hbottom, hlast, hvalues, hdescent⟩
      have hlast' : last < length := by simpa [List.length_take, min_eq_left hlength]
        using hlast
      rw [prefix_read last hlast', prefix_read bottom (by omega)] at hvalues
      rw [prefix_read bottom (by omega), prefix_read top (by omega)] at hdescent
      exact hno ⟨top, bottom, last, htop, hbottom, by omega, hvalues, hdescent⟩
  induction depth generalizing e with
  | zero =>
    have hsingleton : weakExtensions e 0 = {e} := by
      ext f
      constructor
      · rintro ⟨hf, hprefix⟩
        have hlength : f.length = e.length := by simpa using hf.1
        rw [← hlength, List.take_length] at hprefix
        exact hprefix
      · intro hf
        have heq : f = e := hf
        subst f
        exact ⟨⟨by simp, he, havoid⟩, List.take_length⟩
    rw [hsingleton, Set.ncard_singleton]
    rfl
  | succ depth ih =>
    let Letters := {letter : ℕ // inversionBottom e ≤ letter ∧ letter ≤ 1 + wasc e}
    obtain ⟨hheight, hslack, correspondence, hlabels⟩ := weak_children_rule e hempty he havoid
    let : Finite Letters := Finite.of_injective correspondence correspondence.injective
    let : Fintype Letters := Fintype.ofFinite Letters
    have child_valid (letter : Letters) :
        IsWeakAscent (e ++ [letter.val]) ∧ ¬ Contains210 (e ++ [letter.val]) :=
      (append_interval e hempty he havoid letter.val).mpr letter.property
    have first_child (f : weakExtensions e (depth + 1)) :
        f.val.take (e.length + 1) = e ++ [f.val.getD e.length 0] := by
      have hlength : f.val.length = e.length + (depth + 1) := f.property.1.1
      rw [List.take_succ_eq_append_getElem (by omega), f.property.2,
        List.getD_eq_getElem _ _ (by omega)]
    have first_admitted (f : weakExtensions e (depth + 1)) :
        inversionBottom e ≤ f.val.getD e.length 0 ∧
        f.val.getD e.length 0 ≤ 1 + wasc e := by
      have hlength : f.val.length = e.length + (depth + 1) := f.property.1.1
      have hmember := prefix_member f.val (e.length + 1) f.property.1.2.1
        f.property.1.2.2 (by omega)
      rw [first_child f] at hmember
      exact (append_interval e hempty he havoid _).mp hmember.2
    let splitExtension : weakExtensions e (depth + 1) →
        Σ letter : Letters, weakExtensions (e ++ [letter.val]) depth := fun f =>
      ⟨⟨f.val.getD e.length 0, first_admitted f⟩,
        ⟨f.val, ⟨by
          refine ⟨?_, f.property.1.2⟩
          have hlength := f.property.1.1
          simp only [List.length_append, List.length_singleton]
          omega,
        by simpa only [List.length_append, List.length_singleton] using first_child f⟩⟩⟩
    let joinExtension : (Σ letter : Letters, weakExtensions (e ++ [letter.val]) depth) →
        weakExtensions e (depth + 1) := fun child =>
      ⟨child.2.val, ⟨by
        refine ⟨?_, child.2.property.1.2⟩
        have hlength := child.2.property.1.1
        simp only [List.length_append, List.length_singleton] at hlength
        omega,
      by
        have hprefix := congrArg (List.take e.length) child.2.property.2
        simp only [List.length_append, List.length_singleton, List.take_take,
          min_eq_left (show e.length ≤ e.length + 1 by omega)] at hprefix
        rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hprefix
        exact hprefix⟩⟩
    have recover_letter (child : Σ letter : Letters,
        weakExtensions (e ++ [letter.val]) depth) :
        child.2.val.getD e.length 0 = child.1.val := by
      have hread := congrArg (fun f : List ℕ => f.getD e.length 0) child.2.property.2
      have htaken : (child.2.val.take (e ++ [child.1.val]).length).getD e.length 0 =
          child.2.val.getD e.length 0 := by
        simp only [List.length_append, List.length_singleton,
          List.getD_eq_getElem?_getD, List.getElem?_take,
          if_pos (show e.length < e.length + 1 by omega)]
      rw [htaken, List.getD_append_right _ _ _ _ (Nat.le_refl _)] at hread
      simpa using hread
    let splitEquiv : weakExtensions e (depth + 1) ≃
        (Σ letter : Letters, weakExtensions (e ++ [letter.val]) depth) :=
      ⟨splitExtension, joinExtension, by
        intro f
        apply Subtype.ext
        rfl,
      by
        intro child
        have hletter : (splitExtension (joinExtension child)).1 = child.1 := by
          apply Subtype.ext
          exact recover_letter child
        apply Sigma.ext hletter
        have hpredicate := congrArg (fun letter : Letters => fun f : List ℕ =>
          f ∈ weakExtensions (e ++ [letter.val]) depth) hletter
        exact (Subtype.heq_iff_coe_heq rfl (heq_of_eq hpredicate)).mpr HEq.rfl⟩
    rw [← Nat.card_coe_set_eq, Nat.card_congr splitEquiv, Nat.card_sigma]
    simp only [Nat.card_coe_set_eq]
    calc
      (∑ letter : Letters, (weakExtensions (e ++ [letter.val]) depth).ncard) =
          ∑ letter : Letters, treeCount depth (weakLabel (e ++ [letter.val])).1
            (weakLabel (e ++ [letter.val])).2 := by
        apply Finset.sum_congr rfl
        intro letter _
        exact ih (e ++ [letter.val]) (by simp) (child_valid letter).1 (child_valid letter).2
      _ = ∑ index : Fin (weakLabel e).1 ⊕ Fin (weakLabel e).2,
          treeCount depth (childLabel (weakLabel e).1 (weakLabel e).2 index).1
            (childLabel (weakLabel e).1 (weakLabel e).2 index).2 := by
        apply Fintype.sum_equiv correspondence
        intro letter
        rw [hlabels letter]
      _ = treeCount (depth + 1) (weakLabel e).1 (weakLabel e).2 := rfl

end D5.S3.Combinatorics.WeakAscent.WeakAscentCounting
