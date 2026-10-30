/- GID: D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonincreasing Lyndon factorizations are unique over every linearly ordered alphabet. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
import Mathlib.Data.List.Induction

/-! # Uniqueness of nonincreasing Lyndon factorization -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

variable {A : Type*} [LinearOrder A]

/-- The last factor is the least nonempty suffix of the concatenated word. -/
theorem last_factor_is_min_nonempty_suffix (fs : List (List A)) (m : List A) :
    (∀ u ∈ fs ++ [m], IsLyndon u) →
    (fs ++ [m]).Pairwise (fun u v => v ≤ u) →
    IsLeast {s : List A | s ≠ [] ∧ s <:+ (fs ++ [m]).flatten} m := by
  induction fs with
  | nil =>
      intro hL _
      have hm : IsLyndon m := hL m (by simp)
      refine ⟨⟨hm.1, by simp⟩, ?_⟩
      rintro s ⟨hs, hsuf⟩
      simp only [List.nil_append, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hsuf
      rcases eq_or_ne s m with rfl | hsm
      · exact le_rfl
      · exact (((isLyndon_iff_lt_suffix m).mp hm).2 s hs hsuf hsm).le
  | cons u fs ih =>
      intro hL hO
      have hLtail : ∀ v ∈ fs ++ [m], IsLyndon v := by
        intro v hv
        exact hL v (by simp only [List.cons_append, List.mem_cons]; exact Or.inr hv)
      have hOtail : (fs ++ [m]).Pairwise (fun u v => v ≤ u) :=
        (List.pairwise_cons.mp hO).2
      have hmin := ih hLtail hOtail
      have hmu : m ≤ u := (List.pairwise_cons.mp hO).1 m (by simp)
      have hu : IsLyndon u := hL u (by simp)
      refine ⟨⟨hmin.1.1, ?_⟩, ?_⟩
      · simpa only [List.cons_append, List.flatten_cons] using
          hmin.1.2.trans (List.suffix_append u (fs ++ [m]).flatten)
      · rintro s ⟨hs, hsuf⟩
        change s <:+ u ++ (fs ++ [m]).flatten at hsuf
        rcases List.suffix_or_suffix_of_suffix hsuf
            (List.suffix_append u (fs ++ [m]).flatten) with hshort | hlong
        · exact hmin.2 ⟨hs, hshort⟩
        · rcases hlong with ⟨t, rfl⟩
          by_cases ht : t = []
          · subst t
            simpa only [List.nil_append] using
              hmin.2 ⟨by simpa only [List.nil_append] using hs, List.suffix_refl _⟩
          · have htu : t <:+ u := List.suffix_append_self_iff.mp hsuf
            have hut : u ≤ t := by
              rcases eq_or_ne t u with rfl | htu_ne
              · exact le_rfl
              · exact (((isLyndon_iff_lt_suffix u).mp hu).2 t ht htu htu_ne).le
            exact (hmu.trans hut).trans (le_of_not_gt
              (List.le_append_left (l₁ := t) (l₂ := (fs ++ [m]).flatten)))

/-- Equality of words determines every factor in a nonincreasing Lyndon factorization. -/
theorem nonincreasing_lyndon_factorization_unique (fs gs : List (List A))
    (hfs : ∀ w ∈ fs, IsLyndon w)
    (hfsO : fs.Pairwise (fun u v => v ≤ u))
    (hgs : ∀ w ∈ gs, IsLyndon w)
    (hgsO : gs.Pairwise (fun u v => v ≤ u))
    (heq : fs.flatten = gs.flatten) : fs = gs := by
  induction fs using List.reverseRecOn generalizing gs with
  | nil =>
      have hgnil : gs = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro w hw
        have hflat : gs.flatten = [] := heq.symm
        have hwnil : w = [] := by
          exact (List.flatten_eq_nil_iff.mp hflat) w hw
        exact (hgs w hw).1 hwnil
      exact hgnil.symm
  | append_singleton fs f ih =>
      cases gs using List.reverseRecOn with
      | nil =>
          have hf : IsLyndon f := hfs f (by simp)
          have hnil : f = [] := by
            have hflat : (fs ++ [f]).flatten = [] := heq
            exact (List.flatten_eq_nil_iff.mp hflat) f (by simp)
          exact (hf.1 hnil).elim
      | append_singleton gs g =>
          have hfmin := last_factor_is_min_nonempty_suffix fs f hfs hfsO
          have hgmin := last_factor_is_min_nonempty_suffix gs g hgs hgsO
          have hfg : f = g := le_antisymm
            (hfmin.2 ⟨hgmin.1.1, heq.symm ▸ hgmin.1.2⟩)
            (hgmin.2 ⟨hfmin.1.1, heq ▸ hfmin.1.2⟩)
          subst g
          have hprefix : fs.flatten = gs.flatten := by
            simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
              List.append_nil, List.append_left_inj] using heq
          have hfs' : ∀ w ∈ fs, IsLyndon w := fun w hw => hfs w (by simp [hw])
          have hgs' : ∀ w ∈ gs, IsLyndon w := fun w hw => hgs w (by simp [hw])
          have hfsO' : fs.Pairwise (fun u v => v ≤ u) :=
            (List.pairwise_append.mp hfsO).1
          have hgsO' : gs.Pairwise (fun u v => v ≤ u) :=
            (List.pairwise_append.mp hgsO).1
          exact congrArg (fun xs => xs ++ [f]) (ih gs hfs' hfsO' hgs' hgsO' hprefix)

end D5.S1.Words.Complexity.LyndonBrackets.LyndonFactorizationUnique
