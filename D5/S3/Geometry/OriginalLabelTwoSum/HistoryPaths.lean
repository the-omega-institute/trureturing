/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryPaths
   mirror-E: none(waiver:physical-history-paths)
   anchors: [mathlib/module/Mathlib.Data.List.Nodup]
   utility: none
   digest: Every distinct labelled path has an actual tagged noncover output via the two-leaf LINK recursion. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord

/-! SOURCE_ONLY_UNCOMPILED. Genuine path NONCOVERS are constructed here;
no inversion of a simplex-to-noncover filling is used. The existing literal
`AllMWheel.pathEdges` is the only path-edge definition. At lengths 0 and 1
the output is VOID, at length 2 it is UNIT, and from length 3 the two-leaf
constructor supplies actual main and separate core lists. No critical-size
formula is asserted for the tags. The critical profile below reads back this
very construction, including its empty-ground and tagged-tail branches.

The proof source remains uncompiled; no source or kernel acceptance follows.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths
open OriginalLabelTwoSum HistoryLeafCap AllMWheel
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem edge_supported (vs : List V) (q : Finset V) (hq : q ∈ pathEdges vs) :
    q ⊆ vs.toFinset := by
  induction vs with
  | nil => simp [pathEdges] at hq
  | cons a vs ih =>
      cases vs with
      | nil => simp [pathEdges] at hq
      | cons b vs =>
          rcases Finset.mem_insert.mp hq with rfl | hq
          · simp
          · exact (ih hq).trans (by simp)

/-- Literal consecutive chord rows. The declared ground includes internal
vertices that may disappear from all remaining nonempty faces. -/
def pathRows (vs : List V) : Rows V where
  ground := vs.toFinset
  chords := {q : Finset V // q ∈ pathEdges vs}
  row q := q.1
  row_supported q := edge_supported vs q.1 q.2

private def noncover (vs : List V) : Family V where
  carrier := {s | s ⊆ vs.toFinset ∧ ∃ q ∈ pathEdges vs, Disjoint q s}
  lower' := by
    rintro s t h ⟨hs, q, hq, hd⟩
    exact ⟨h.trans hs, q, hq, hd.mono_right h⟩

private theorem pathRows_root (vs : List V) : (pathRows vs).root = noncover vs := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨q, hs⟩
    exact ⟨hs.trans Finset.sdiff_subset, q.1, q.2,
      Finset.disjoint_left.mpr (fun x hxq hxs => (Finset.mem_sdiff.mp (hs hxs)).2 hxq)⟩
  · rintro ⟨hs, q, hq, hd⟩
    exact ⟨⟨q, hq⟩, fun x hx => Finset.mem_sdiff.mpr
      ⟨hs hx, fun hxq => Finset.disjoint_left.mp hd hxq hx⟩⟩

private theorem path_step (a b c : V) (vs : List V) (hd : (a::b::c::vs).Nodup) :
    noncover (a::b::c::vs) = twoLeafFamily vs.toFinset a b c (noncover (c::vs)) := by
  have ha := (List.nodup_cons.mp hd).1
  have hb := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
  have hac : a ≠ c := fun h => ha (by simp [h])
  have hab : a ≠ b := fun h => ha (by simp [h])
  have hbc : b ≠ c := fun h => hb (by simp [h])
  have haT : a ∉ (c::vs).toFinset := fun h =>
    ha (List.mem_cons_of_mem _ (List.mem_toFinset.mp h))
  have hbT : b ∉ (c::vs).toFinset := fun h => hb (List.mem_toFinset.mp h)
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs, q, hq, hqs⟩
    simp only [pathEdges, Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq
    · left; left
      intro v hv
      have hvs : v = a ∨ v = b ∨ v = c ∨ v ∈ vs.toFinset := by simpa using hs hv
      exact hvs.elim (fun h => False.elim (Finset.disjoint_left.mp hqs (by simp [h]) hv))
        (fun h => h.elim
          (fun h => False.elim (Finset.disjoint_left.mp hqs (by simp [h]) hv))
          (fun h => by simpa using h))
    · left; right
      intro v hv
      have hvs : v = a ∨ v = b ∨ v = c ∨ v ∈ vs.toFinset := by simpa using hs hv
      exact hvs.elim (fun h => Finset.mem_insert.mpr (Or.inl h)) (fun h =>
        h.elim (fun h => False.elim (Finset.disjoint_left.mp hqs (by simp [h]) hv))
          (fun h => h.elim
            (fun h => False.elim (Finset.disjoint_left.mp hqs (by simp [h]) hv))
            (fun h => Finset.mem_insert_of_mem h)))
    · right
      refine ⟨s ∩ {a,b}, Finset.inter_subset_right,
        s ∩ (c::vs).toFinset,
        ⟨Finset.inter_subset_right, q, hq, hqs.mono_right Finset.inter_subset_left⟩, ?_⟩
      ext v
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hv
        have h : v = a ∨ v = b ∨ v ∈ (c::vs).toFinset := by simpa using hs hv
        exact h.elim (fun h => Or.inl ⟨hv, by simp [h]⟩) (fun h =>
          h.elim (fun h => Or.inl ⟨hv, by simp [h]⟩) (fun h => Or.inr ⟨hv, h⟩))
      · tauto
  · rintro ((hs | hs) | ⟨x, hx, t, ⟨ht, q, hq, hqt⟩, rfl⟩)
    · refine ⟨hs.trans (by simpa only [List.toFinset_cons] using ((Finset.subset_insert b (insert c vs.toFinset)).trans (Finset.subset_insert a _))), {a,b}, by simp [pathEdges], ?_⟩
      apply Finset.disjoint_left.mpr
      intro v hv hvs
      have h : v = a ∨ v = b := by simpa using hv
      exact h.elim (fun h => haT (by simpa only [List.toFinset_cons] using (h ▸ hs hvs))) (fun h => hbT (by simpa only [List.toFinset_cons] using (h ▸ hs hvs)))
    · refine ⟨hs.trans (by simpa only [List.toFinset_cons] using (Finset.insert_subset_insert a ((Finset.subset_insert c vs.toFinset).trans (Finset.subset_insert b _)))), {b,c}, by simp [pathEdges], ?_⟩
      apply Finset.disjoint_left.mpr
      intro v hv hvs
      have hvU := hs hvs
      have h : v = b ∨ v = c := by simpa using hv
      rcases h with rfl | rfl
      · exact (Finset.mem_insert.mp hvU).elim (fun h => hab h.symm)
          (fun h => hb (by simp [List.mem_toFinset.mp h]))
      · exact (Finset.mem_insert.mp hvU).elim (fun h => hac h.symm)
          (fun h => (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
            (List.mem_toFinset.mp h))
    · refine ⟨Finset.union_subset (hx.trans (by simp)) (ht.trans (by simpa only [List.toFinset_cons] using ((Finset.subset_insert b (insert c vs.toFinset)).trans (Finset.subset_insert a _)))), 
        q, by simp only [pathEdges, Finset.mem_insert]; tauto, ?_⟩
      apply Finset.disjoint_left.mpr
      intro v hvq hvs
      rcases Finset.mem_union.mp hvs with hvx | hvt
      · have hqT := edge_supported (c::vs) q hq hvq
        have h : v = a ∨ v = b := by simpa using hx hvx
        exact h.elim (fun h => haT (h ▸ hqT)) (fun h => hbT (h ▸ hqT))
      · exact Finset.disjoint_left.mp hqt hvq hvt

private theorem path_link (c : V) (vs : List V) (hd : (c::vs).Nodup) :
    rawLink vs.toFinset c (noncover (c::vs)) = noncover vs := by
  have hc : c ∉ vs.toFinset := fun h => (List.nodup_cons.mp hd).1 (List.mem_toFinset.mp h)
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs, _, q, hq, hqs⟩
    refine ⟨hs, q, ?_, hqs.mono_right (Finset.subset_insert _ _)⟩
    cases vs with
    | nil => simp [pathEdges] at hq
    | cons d vs =>
        rcases Finset.mem_insert.mp hq with hq | hq
        · subst q
          exact False.elim (Finset.disjoint_left.mp hqs (show c ∈ ({c,d} : Finset V) from Finset.mem_insert_self _ _) (Finset.mem_insert_self c s))
        · exact hq
  · rintro ⟨hs, q, hq, hqs⟩
    refine ⟨hs, Finset.insert_subset (by simp) (hs.trans (by simp)),
      q, ?_, ?_⟩
    · cases vs <;> simp_all only [pathEdges, Finset.mem_insert] <;> tauto
    · apply Finset.disjoint_left.mpr
      intro v hvq hv
      rcases Finset.mem_insert.mp hv with he | hv
      · exact hc (he ▸ edge_supported vs q hq hvq)
      · exact Finset.disjoint_left.mp hqs hvq hv

private theorem two_vertex_unit (a b : V) : noncover [a,b] = delta ∅ := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs, q, hq, hd⟩
    have he : q = {a,b} := by simpa [pathEdges] using hq
    subst q
    have hs0 : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact Finset.disjoint_left.mp hd (by simpa using hs hv) hv
    simp [hs0]
  · intro hs
    have he : s = ∅ := Finset.subset_empty.mp hs
    subst s
    exact ⟨Finset.empty_subset _, {a,b}, by simp [pathEdges], by simp⟩

private def pathOutput : (vs : List V) → vs.Nodup → Output vs.toFinset (noncover vs)
  | [], hd => .void (by
      apply SetLike.ext; intro s
      simp [noncover, pathEdges])
  | [a], hd => .void (by
      apply SetLike.ext; intro s
      simp [noncover, pathEdges])
  | [a,b], hd => .unit (two_vertex_unit a b)
  | a::b::c::vs, hd => by
      have hdT : (c::vs).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2
      have hdU : vs.Nodup := (List.nodup_cons.mp hdT).2
      have ha : a ∉ insert b (insert c vs.toFinset) := by
        simpa using (List.nodup_cons.mp hd).1
      have hb : b ∉ insert c vs.toFinset := by
        simpa using (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
      have hc : c ∉ vs.toFinset := by simpa using (List.nodup_cons.mp hdT).1
      let tail : Output vs.toFinset (rawLink vs.toFinset c (noncover (c::vs))) :=
        changeOutput (pathOutput vs hdU) (path_link c vs hdT).symm
      exact widenOutput (by simp only [List.toFinset_cons]; exact le_rfl) (changeOutput
        (twoLeafOutput vs.toFinset a b c (noncover (c::vs)) ha hb hc
          (fun _ h => by simpa only [List.toFinset_cons] using h.1) tail) (path_step a b c vs hd).symm)
termination_by vs _ => vs.length
decreasing_by simp only [List.length_cons]; omega

/-- Genuine all-length path row output, with no supplied link/deletion/core
certificate. Recursion constructs the smaller path's output itself. The
strong branch contains actual native pairs and an independent C-only list. -/
def pathRowsOutput (vs : List V) (hd : vs.Nodup) :
    Output (pathRows vs).ground (pathRows vs).root :=
  changeOutput (pathOutput vs hd) (pathRows_root vs).symm

/-- Exact ordinary critical TOPS for the actual path construction. The first
three values are unused by strong outputs: 0/1 are VOID and 2 is UNIT. -/
def pathCriticalTops : List V → Finset (Finset V)
  | [] => ∅
  | [_] => ∅
  | [_,_] => ∅
  | [_,_,c] => {{c}}
  | [_,_,_,_] => ∅
  | [a,_,c,_,_] => {{a,c}}
  | a::_::c::d::e::f::vs =>
      (pathCriticalTops (d::e::f::vs)).image (fun q => ({a,c} : Finset V) ∪ q)

private def pathState (vs : List V) : CriticalState V :=
  match vs with
  | [] => .void
  | [_] => .void
  | [_,_] => .unit
  | _ => .strong (pathCriticalTops vs)

private theorem pathOutput_state (vs : List V) (hd : vs.Nodup) :
    (pathOutput vs hd).criticalState = pathState vs := by
  revert hd
  induction vs using List.length_induction with
  | _ vs ih =>
      intro hd
      match vs with
      | [] => simp only [pathOutput, pathState, Output.criticalState]
      | [a] => simp only [pathOutput, pathState, Output.criticalState]
      | [a,b] => simp only [pathOutput, pathState, Output.criticalState]
      | a::b::c::vs =>
          have hdT : (c::vs).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2
          have hdU : vs.Nodup := (List.nodup_cons.mp hdT).2
          have ha : a ∉ insert b (insert c vs.toFinset) := by
            simpa using (List.nodup_cons.mp hd).1
          have hb : b ∉ insert c vs.toFinset := by
            simpa using (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
          have hc : c ∉ vs.toFinset := by simpa using (List.nodup_cons.mp hdT).1
          rw [pathOutput, widenOutput_criticalState, changeOutput_criticalState]
          cases vs with
          | nil =>
              erw [twoLeafOutput_empty_criticalState (V := V)]
              have h0 : (∅ : Finset V) ∉ rawLink ∅ c (noncover [c]) := by
                rw [path_link c [] hdT]
                simp [noncover, pathEdges]
              simp [h0, pathState, pathCriticalTops]
          | cons d vs =>
              erw [twoLeafOutput_criticalState _ _ _ _ _ _ _ _ _ _ (show (d::vs).toFinset.Nonempty from ⟨d, by simp⟩),
                changeOutput_criticalState, ih (d::vs) (by simp only [List.length_cons]; omega) hdU]
              cases vs with
              | nil => rfl
              | cons e vs =>
                  cases vs with
                  | nil => rfl
                  | cons f vs => rfl

private theorem pathCriticalTops_supported (vs : List V) :
    ∀ q ∈ pathCriticalTops vs, q ⊆ vs.toFinset := by
  match vs with
  | [] => simp [pathCriticalTops]
  | [a] => simp [pathCriticalTops]
  | [a,b] => simp [pathCriticalTops]
  | [a,b,c] => simp [pathCriticalTops]
  | [a,b,c,d] => simp [pathCriticalTops]
  | [a,b,c,d,e] => simp [pathCriticalTops]
  | a::b::c::d::e::f::vs =>
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.union_subset (by simp)
        ((pathCriticalTops_supported (d::e::f::vs) t ht).trans (by
           simpa only [List.toFinset_cons] using ((Finset.subset_insert c (d::e::f::vs).toFinset).trans
             ((Finset.subset_insert b _).trans (Finset.subset_insert a _)))))
termination_by vs.length
decreasing_by simp only [List.length_cons]; omega

/-- The three strong-case formulas; no empty ordinary critical at n=2 is
encoded here. This predicate is proved for the constructed critical family. -/
def PathCriticalProfile (n : Nat) (D : Finset (Finset V)) : Prop :=
  (n % 3 = 1 → D = ∅) ∧
  (n % 3 = 0 → ∃ q, D = {q} ∧ q.card = 2 * (n / 3) - 1) ∧
  (n % 3 = 2 → ∃ q, D = {q} ∧ q.card = 2 * (n / 3))

private theorem pathCriticalTops_profile (vs : List V) (hd : vs.Nodup)
    (hn : 3 ≤ vs.length) : PathCriticalProfile vs.length (pathCriticalTops vs) := by
  match vs with
  | [] => simp at hn
  | [a] => simp at hn
  | [a,b] => simp at hn
  | [a,b,c] => simp [PathCriticalProfile, pathCriticalTops]
  | [a,b,c,d] => simp [PathCriticalProfile, pathCriticalTops]
  | [a,b,c,d,e] =>
      have hac : a ≠ c := fun he => (List.nodup_cons.mp hd).1 (by simp [he])
      simp [PathCriticalProfile, pathCriticalTops, hac]
  | a::b::c::d::e::f::vs =>
      let tail := d::e::f::vs
      have hdT : tail.Nodup := (List.nodup_cons.mp
        (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).2
      have htail : 3 ≤ tail.length := by simp [tail]
      have ih := pathCriticalTops_profile tail hdT htail
      have ha : a ∉ tail.toFinset := by
        intro h
        exact (List.nodup_cons.mp hd).1 (by simp [List.mem_toFinset.mp h, tail])
      have hc : c ∉ tail.toFinset := by
        simpa [tail] using (List.nodup_cons.mp
          (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
      have hac : a ≠ c := fun he => (List.nodup_cons.mp hd).1 (by simp [he])
      have card_pad : ∀ q ∈ pathCriticalTops tail,
          (({a,c} : Finset V) ∪ q).card = q.card + 2 := by
        intro q hq
        have hqT := pathCriticalTops_supported tail q hq
        have haq : a ∉ q := fun h => ha (hqT h)
        have hcq : c ∉ q := fun h => hc (hqT h)
        simp [Finset.insert_union, Finset.singleton_union, haq, hcq, hac,
          Nat.add_assoc]
      have hnT : (a::b::c::d::e::f::vs).length = tail.length + 3 := by simp [tail]
      change PathCriticalProfile _ ((pathCriticalTops tail).image _)
      refine ⟨?_, ?_, ?_⟩
      · intro h1
        rw [ih.1 (by omega), Finset.image_empty]
      · intro h0
        obtain ⟨q, hq, hcard⟩ := ih.2.1 (by omega)
        refine ⟨{a,c} ∪ q, by rw [hq, Finset.image_singleton], ?_⟩
        have hp := card_pad q (by rw [hq]; simp)
        omega
      · intro h2
        obtain ⟨q, hq, hcard⟩ := ih.2.2 (by omega)
        refine ⟨{a,c} ∪ q, by rw [hq, Finset.image_singleton], ?_⟩
        have hp := card_pad q (by rw [hq]; simp)
        omega
termination_by vs.length
decreasing_by simp only [List.length_cons]; omega

/-- First missing D9 assertion, about the ACTUALLY CONSTRUCTED output. For
every distinct labelled path of length at least three, it is strong; residue
one has no critical, and residues zero/two have exactly one of the stated
cardinality. No certificate or desired profile is an input. -/
theorem pathRowsOutput_critical_profile (vs : List V) (hd : vs.Nodup)
    (hn : 3 ≤ vs.length) :
    ∃ c : Certificate (pathRows vs).ground (pathRows vs).root,
      pathRowsOutput vs hd = .strong c ∧
      PathCriticalProfile vs.length c.critical := by
  have hs : (pathRowsOutput vs hd).criticalState = .strong (pathCriticalTops vs) := by
    rw [pathRowsOutput, changeOutput_criticalState, pathOutput_state]
    match vs with
    | [] => simp at hn
    | [a] => simp at hn
    | [a,b] => simp at hn
    | a::b::c::vs => rfl
  generalize he : pathRowsOutput vs hd = o at hs
  cases o with
  | void h => cases hs
  | unit h => cases hs
  | strong c =>
      have hc : c.critical = pathCriticalTops vs := by
        exact CriticalState.strong.inj hs
      exact ⟨c, rfl, hc.symm ▸ pathCriticalTops_profile vs hd hn⟩

/-- Literal row membership, for identifying the existing all-m path root. -/
theorem pathRows_mem (vs : List V) (s : Finset V) :
    s ∈ (pathRows vs).root ↔
      s ⊆ vs.toFinset ∧ ∃ q ∈ pathEdges vs, Disjoint q s := by
  rw [pathRows_root]
  rfl

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths
