/- GID: D5/S1/Words/TraceMultiCut
   generality: G
   mirror-B: D5/B/S1/Words/TraceMultiCut
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Simultaneous strict-independent two-row refinement of finite trace products. -/

import D5.S1.Words.TraceLevi
import Mathlib.Data.List.OfFn

/-! # Simultaneous two-row refinement of native traces -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TraceMultiCut

open D5.S1.Words.TraceProjection D5.S1.Words.TraceLevi

universe u
variable {α : Type u}

/-- A two-factor trace equality with a finite ordered product admits common row
families whose every earlier lower factor is strictly independent of every later
upper factor, letter by letter. -/
theorem connected_append_flatten_iff (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    (x y : List α) (zs : List (List α)) :
    Connected I (x ++ y) zs.flatten ↔
      ∃ p r : Fin zs.length → List α,
        Connected I x (List.ofFn p).flatten ∧
        Connected I y (List.ofFn r).flatten ∧
        (∀ j : Fin zs.length, Connected I zs[j] (p j ++ r j)) ∧
        (∀ j k : Fin zs.length, j < k →
          ∀ a ∈ p k, ∀ b ∈ r j, I a b) := by
  induction zs generalizing x y with
  | nil =>
      constructor
      · intro h
        have hn : x ++ y = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro a ha
          exact List.not_mem_nil (mem_of_connected I hs hi (connected_symm I hs hi h) ha)
        obtain ⟨hx, hy⟩ := List.append_eq_nil_iff.mp hn
        subst x
        subst y
        exact ⟨Fin.elim0, Fin.elim0, .refl, .refl,
          fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
      · rintro ⟨p, r, hx, hy, _, _⟩
        simpa using connected_append I hs hi hx hy
  | cons z zs ih =>
      constructor
      · intro h
        obtain ⟨p₀, q, r₀, s, hx, hy, hz, ht, hc⟩ :=
          (connected_append_iff I hs hi x y z zs.flatten).mp h
        obtain ⟨p, r, hq, hs', hcol, hcross⟩ := (ih q s).mp (connected_symm I hs hi ht)
        refine ⟨Fin.cons p₀ p, Fin.cons r₀ r, ?_, ?_, ?_, ?_⟩
        · simpa only [Connected, List.ofFn_cons, List.flatten_cons] using
            Relation.ReflTransGen.trans hx
              (connected_append I hs hi (Relation.ReflTransGen.refl (a := p₀)) hq)
        · simpa only [Connected, List.ofFn_cons, List.flatten_cons] using
            Relation.ReflTransGen.trans hy
              (connected_append I hs hi (Relation.ReflTransGen.refl (a := r₀)) hs')
        · intro j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using hz
          · simpa using hcol k
        · intro j k hjk
          revert hjk
          refine Fin.cases ?_ (fun j' => ?_) j
          · refine Fin.cases ?_ (fun k' _ a ha b hb => ?_) k
            · simp
            · have ham : a ∈ (List.ofFn p).flatten :=
                List.mem_flatten.mpr ⟨p k', List.mem_ofFn.mpr ⟨k', rfl⟩, ha⟩
              exact hc a (mem_of_connected I hs hi hq ham) b hb
          · refine Fin.cases ?_ (fun k' hjk a ha b hb => ?_) k
            · simp
            · exact hcross j' k' (by simpa using hjk) a ha b hb
      · rintro ⟨p, r, hx, hy, hcol, hcross⟩
        let pt : Fin zs.length → List α := fun j => p j.succ
        let rt : Fin zs.length → List α := fun j => r j.succ
        have htail : Connected I ((List.ofFn pt).flatten ++ (List.ofFn rt).flatten)
            zs.flatten := (ih _ _).mpr ⟨pt, rt, .refl, .refl,
              (fun j => by simpa [pt, rt] using hcol j.succ),
              (fun j k hjk => hcross j.succ k.succ (by simpa using hjk))⟩
        apply (connected_append_iff I hs hi x y z zs.flatten).mpr
        refine ⟨p 0, (List.ofFn pt).flatten, r 0, (List.ofFn rt).flatten,
          ?_, ?_, ?_, connected_symm I hs hi htail, ?_⟩
        · simpa only [List.ofFn_succ, List.flatten_cons] using hx
        · simpa only [List.ofFn_succ, List.flatten_cons] using hy
        · simpa using hcol 0
        · intro a ha b hb
          obtain ⟨w, hw, haw⟩ := List.mem_flatten.mp ha
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
          exact hcross 0 k.succ (Fin.succ_pos k) a haw b hb

end D5.S1.Words.TraceMultiCut
