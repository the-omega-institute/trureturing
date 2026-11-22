/- GID: D5/S1/Words/TraceMatrix
   generality: G
   mirror-B: D5/B/S1/Words/TraceMatrix
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Common strict-independent matrices refine finite native trace products. -/

import D5.S1.Words.TraceMultiCut

/-! # Common matrices for finite products of native traces -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TraceMatrix

open D5.S1.Words.TraceProjection D5.S1.Words.TraceLevi
  D5.S1.Words.TraceMultiCut

universe u
variable {α : Type u}

private theorem connected_flatten_family_iff (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    (xs : List (List α)) {n : ℕ} (ys : Fin n → List α) :
    Connected I xs.flatten (List.ofFn ys).flatten ↔
      ∃ w : Fin xs.length → Fin n → List α,
        (∀ i, Connected I xs[i] (List.ofFn (w i)).flatten) ∧
        (∀ j, Connected I (ys j) (List.ofFn (fun i => w i j)).flatten) ∧
        (∀ i i' j j', i < i' → j' < j →
          ∀ a ∈ w i j, ∀ b ∈ w i' j', I a b) := by
  induction xs generalizing n with
  | nil =>
      constructor
      · intro h
        refine ⟨Fin.elim0, (fun i => Fin.elim0 i), ?_, (fun i => Fin.elim0 i)⟩
        intro j
        have he : ys j = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro a ha
          have hm : a ∈ (List.ofFn ys).flatten :=
            List.mem_flatten.mpr ⟨ys j, List.mem_ofFn.mpr ⟨j, rfl⟩, ha⟩
          exact List.not_mem_nil (mem_of_connected I hs hi h hm)
        simpa [Connected, he] using (Relation.ReflTransGen.refl (r := Swap I) (a := []))
      · rintro ⟨w, _, hcol, _⟩
        have he : (List.ofFn ys).flatten = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro a ha
          obtain ⟨v, hv, hav⟩ := List.mem_flatten.mp ha
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
          have hm := mem_of_connected I hs hi (connected_symm I hs hi (hcol j)) hav
          simp at hm
        simpa [Connected, he] using (Relation.ReflTransGen.refl (r := Swap I) (a := []))
  | cons x xs ih =>
      have twoRow : Connected I (x ++ xs.flatten) (List.ofFn ys).flatten ↔
          ∃ p r : Fin n → List α,
            Connected I x (List.ofFn p).flatten ∧
            Connected I xs.flatten (List.ofFn r).flatten ∧
            (∀ j, Connected I (ys j) (p j ++ r j)) ∧
            (∀ j k, j < k → ∀ a ∈ p k, ∀ b ∈ r j, I a b) := by
        have hn : (List.ofFn ys).length = n := List.length_ofFn
        have reindex (f : Fin (List.ofFn ys).length → List α) :
            List.ofFn f = List.ofFn (fun j => f (Fin.cast hn.symm j)) :=
          List.ofFn_congr hn f
        constructor
        · intro h
          obtain ⟨p, r, hx, hr, hc, hcr⟩ :=
            (connected_append_flatten_iff I hs hi x xs.flatten (List.ofFn ys)).mp h
          refine ⟨(fun j => p (Fin.cast hn.symm j)),
            (fun j => r (Fin.cast hn.symm j)), ?_, ?_, ?_, ?_⟩
          · simpa only [← reindex p] using hx
          · simpa only [← reindex r] using hr
          · intro j
            simpa using hc (Fin.cast hn.symm j)
          · intro j k hjk
            exact hcr _ _ (by simpa using hjk)
        · rintro ⟨p, r, hx, hr, hc, hcr⟩
          apply (connected_append_flatten_iff I hs hi x xs.flatten (List.ofFn ys)).mpr
          refine ⟨(fun j => p (Fin.cast hn j)), (fun j => r (Fin.cast hn j)),
            ?_, ?_, ?_, ?_⟩
          · simpa only [reindex, Fin.cast_cast, Fin.cast_refl, id_eq] using hx
          · simpa only [reindex, Fin.cast_cast, Fin.cast_refl, id_eq] using hr
          · intro j
            simpa [Fin.cast] using hc (Fin.cast hn j)
          · intro j k hjk
            exact hcr _ _ (by simpa using hjk)
      constructor
      · intro h
        obtain ⟨p, r, hx, hr, hcol, hcross⟩ := twoRow.mp h
        obtain ⟨v, hvrow, hvcol, hvcross⟩ := (ih r).mp hr
        refine ⟨Fin.cons p v, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun k => ?_) i
          · simpa using hx
          · simpa using hvrow k
        · intro j
          simpa only [Connected, List.ofFn_succ, List.flatten_cons,
            Fin.cons_zero, Fin.cons_succ] using
            Relation.ReflTransGen.trans (hcol j)
              (connected_append I hs hi (Relation.ReflTransGen.refl (a := p j)) (hvcol j))
        · intro i i' j j' hii hjj
          revert hii
          refine Fin.cases ?_ (fun k => ?_) i
          · refine Fin.cases ?_ (fun k _ a ha b hb => ?_) i'
            · simp
            · have hm : b ∈ (List.ofFn (fun k => v k j')).flatten :=
                List.mem_flatten.mpr ⟨v k j', List.mem_ofFn.mpr ⟨k, rfl⟩, hb⟩
              exact hcross j' j hjj a ha b (mem_of_connected I hs hi (hvcol j') hm)
          · refine Fin.cases ?_ (fun k' hkk a ha b hb => ?_) i'
            · simp
            · exact hvcross k k' j j' (by simpa using hkk) hjj a ha b hb
      · rintro ⟨w, hrow, hcol, hcross⟩
        let v : Fin xs.length → Fin n → List α := fun i j => w i.succ j
        let r : Fin n → List α := fun j => (List.ofFn (fun i => v i j)).flatten
        have hr : Connected I xs.flatten (List.ofFn r).flatten :=
          (ih r).mpr ⟨v, (fun i => by simpa [v] using hrow i.succ),
            (fun _ => .refl),
            (fun i i' j j' hii hjj =>
              hcross i.succ i'.succ j j' (by simpa using hii) hjj)⟩
        apply twoRow.mpr
        refine ⟨w 0, r, ?_, hr, ?_, ?_⟩
        · simpa using hrow 0
        · intro j
          simpa only [r, v, List.ofFn_succ, List.flatten_cons] using hcol j
        · intro j' j hjj a ha b hb
          obtain ⟨v', hv', hbv⟩ := List.mem_flatten.mp hb
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv'
          exact hcross 0 i.succ j j' (Fin.succ_pos i) hjj a ha b hbv

/-- Native equality of two finite products is equivalent to one common matrix
whose earlier-row, later-column factors are strictly independent of all
later-row, earlier-column factors. -/
theorem connected_flatten_iff (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    (xs ys : List (List α)) :
    Connected I xs.flatten ys.flatten ↔
      ∃ w : Fin xs.length → Fin ys.length → List α,
        (∀ i, Connected I xs[i] (List.ofFn (w i)).flatten) ∧
        (∀ j, Connected I ys[j] (List.ofFn (fun i => w i j)).flatten) ∧
        (∀ i i' j j', i < i' → j' < j →
          ∀ a ∈ w i j, ∀ b ∈ w i' j', I a b) := by
  simpa using connected_flatten_family_iff I hs hi xs (fun j : Fin ys.length => ys[j])

#print axioms connected_flatten_iff

end D5.S1.Words.TraceMatrix
