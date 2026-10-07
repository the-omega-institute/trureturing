/- GID: D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: History-forced outside frontiers yield one common literal output hole and same-size rigidity. -/

import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualHistorySingleHoleRecovery

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves Positive)
open ActualImageSevenLeafSeparation (thirdImage E A C leafAddresses leafLabel)
open ActualLeafHistoryRigidity

/-- Filling a literal output context adds the filled tree's leaves to the outside leaves. -/
theorem context_length (K : OutputContext) (Z : Source) :
    (K.plug Z).length = K.outsideLeaves + Z.length := by
  induction K with
  | hole => simp [OutputContext.plug, OutputContext.outsideLeaves]
  | left K R ih => simp [OutputContext.plug, OutputContext.outsideLeaves, FreeMagma.length, ih]; omega
  | right L K ih => simp [OutputContext.plug, OutputContext.outsideLeaves, FreeMagma.length, ih, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
-- Native canonical blocks and both literal-hole cases share the proof budget.
/-- Complete leaf-history rigidity, with a size-free common literal output context. -/
theorem complete_history_rigidity (H : LeafHistory) (P : Source) (hP : Compatible H P) :
    ((uncovered H P).card = 0 → ∀ P' : Source, Compatible H P' → P' = P) ∧
    ((uncovered H P).card = 1 →
      ∃ (J : OutputContext) (h : Address) (X : Source),
        J.holeAddress = h ∧ (X = A ∨ X = E) ∧ subtree h P = some X ∧ J.plug X = P ∧
        (∀ d ∈ forcedBlocks H, ¬ d.1.IsPrefix h ∧ ¬ h.IsPrefix d.1) ∧
        ∀ P' : Source, Compatible H P' →
          (∀ u ∈ leaves P, ¬ h.IsPrefix u → readout u P' = readout u P) ∧
          ∃ Y : Source, subtree h P' = some Y ∧ J.plug Y = P') ∧
    ((uncovered H P).card ≤ 1 → ∀ P' : Source, Compatible H P' →
      P'.length = P.length → P' = P) := by
  rcases actual_address_geometry with
    ⟨classify, small, rows, _report, historyLaw, overlap, zeroRecovery, _absent,
      _leafPrefix, contextRecovery, gammaShape, _gammaBlocks, singletonPosition,
      readAt, appendSubtree, leafNode, alphaSem⟩
  have acDistinct : A ≠ C := by
    intro he
    have hn := congrArg FreeMagma.length he
    norm_num [A, C, E, FreeMagma.length] at hn
  have coveredRead (P' : Source) (hP' : Compatible H P') (u : Address)
      (hu : u ∈ gamma H) : readout u P' = .alpha :=
    (alphaSem P' u).mp ((historyLaw H P' hP').2 hu)
  have fixedA (w : Address) (hw : w ++ [false, true] ∈ gamma H)
      (P' : Source) (hP' : Compatible H P') : subtree w P' = some A :=
    (rows P' hP'.1 w).2.2.1 (coveredRead P' hP' _ hw)
  have fixedC (w : Address) (hw : w ++ [true, true] ∈ gamma H)
      (P' : Source) (hP' : Compatible H P') : subtree w P' = some C :=
    (rows P' hP'.1 w).2.2.2.2 (coveredRead P' hP' _ hw)
  have canonicalLeaf (u : Address) (hu : u ∈ leaves P) :
      ∃ (v : Address) (b : Bool) (z : Address),
        u = v ++ z ∧ subtree v P = some (if b then A else C) := by
    obtain ⟨Q, hQ⟩ := hP.1
    change thirdImage Q = P at hQ
    have hm : u ∈ leafAddresses P := by
      simpa only [leafAddresses, List.mem_toFinset] using hu
    obtain ⟨c, hc⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).2 u |>.mp hm
    have hr : readout u P = (if c then .alpha else .beta) := by
      cases he : readout u P <;> cases c <;> simp [leafLabel, he] at hc ⊢
    have hn := leafNode P u c hr
    rw [← hQ] at hn
    rcases (classify Q u (.of c)).mp hn with ⟨q, r, _, he⟩ | ⟨v, b, z, hv, he, _hz⟩
    · cases he
    · refine ⟨v, b, z, he, ?_⟩
      rw [← hQ]
      have hb : (if b then A else C) = thirdImage (.of b) := by cases b <;> rfl
      rw [hb]
      apply (classify Q v _).mpr
      refine Or.inr ⟨v, b, [], hv, by simp, ?_⟩
      cases b <;> exact Or.inl ⟨rfl, rfl⟩
  have singletonResult (hc : (uncovered H P).card = 1) :
      ∃ (J : OutputContext) (h : Address) (X : Source),
        J.holeAddress = h ∧ (X = A ∨ X = E) ∧ subtree h P = some X ∧ J.plug X = P ∧
        (∀ d ∈ forcedBlocks H, ¬ d.1.IsPrefix h ∧ ¬ h.IsPrefix d.1) ∧
        ∀ P' : Source, Compatible H P' →
          (∀ u ∈ leaves P, ¬ h.IsPrefix u → readout u P' = readout u P) ∧
          ∃ Y : Source, subtree h P' = some Y ∧ J.plug Y = P' := by
    obtain ⟨x, hx, hposition⟩ := singletonPosition H P hP hc
    have hxmem : x ∈ uncovered H P := by rw [hx]; simp
    have hxng := (Finset.mem_sdiff.mp hxmem).2
    have other (u : Address) (hu : readout u P = .alpha) (hne : u ≠ x) :
        u ∈ gamma H := by
      by_contra hn
      have hm : u ∈ uncovered H P :=
        Finset.mem_sdiff.mpr ⟨(alphaSem P u).mpr hu, hn⟩
      rw [hx] at hm
      exact hne (Finset.mem_singleton.mp hm)
    rcases hposition with ⟨h, hat, hxe⟩ | ⟨v, hvat, hxe, _hleft, leftFixed⟩
    · have outside (P' : Source) (hP' : Compatible H P') :
          ∀ u ∈ leaves P, ¬ h.IsPrefix u → readout u P' = readout u P := by
        intro u hu hout
        obtain ⟨w, b, z, he, hw⟩ := canonicalLeaf u hu
        subst u
        cases b with
        | true =>
          change subtree w P = some A at hw
          have hne : w ++ [false, true] ≠ x := by
            intro heq
            have wh : w = h := List.append_left_injective [false, true] (heq.trans hxe)
            subst w
            exact hout (List.prefix_append h z)
          have ha : w ++ [false, true] ∈ gamma H := by
            apply other _ _ hne
            rw [readAt, hw]
            rfl
          rw [readAt, fixedA w ha P' hP', readAt, hw]
        | false =>
          change subtree w P = some C at hw
          have hne : w ++ [true, true] ≠ x := by
            intro heq
            have hr := congrArg List.reverse (heq.trans hxe)
            simp [List.reverse_append] at hr
          have hc' : w ++ [true, true] ∈ gamma H := by
            apply other _ _ hne
            rw [readAt, hw]
            rfl
          rw [readAt, fixedC w hc' P' hP', readAt, hw]
      have disjoint (d : Address × BlockKind) (hd : d ∈ forcedBlocks H) :
          ¬ d.1.IsPrefix h ∧ ¬ h.IsPrefix d.1 := by
        have hdP := (historyLaw H P hP).1 d hd
        have hkind : d.2.tree = A ∨ d.2.tree = C := by cases d.2 <;> simp [BlockKind.tree]
        rcases overlap P d.1 h d.2.tree A hkind (Or.inl rfl) hdP hat with
          ⟨he, ht⟩ | hdis | ⟨ht, _, he⟩ | ⟨_, ht, _⟩
        · exfalso
          apply hxng
          have hk : d.2 = .a := by
            cases hk : d.2 with
            | a => rfl
            | c => exact False.elim (acDistinct (by simpa only [hk, BlockKind.tree] using ht.symm))
          apply (gammaShape H x).mpr
          exact Or.inl ⟨d.1, by simpa only [hk] using (show (d.1, d.2) ∈ forcedBlocks H from hd), hxe.trans (congrArg (· ++ [false, true]) he.symm)⟩
        · exact hdis
        · exfalso
          apply hxng
          have hk : d.2 = .c := by
            cases hk : d.2 with
            | c => rfl
            | a => exact False.elim (acDistinct (by simpa only [hk, BlockKind.tree] using ht))
          apply (gammaShape H x).mpr
          refine Or.inr ⟨d.1, by simpa only [hk] using (show (d.1, d.2) ∈ forcedBlocks H from hd), Or.inl ?_⟩
          simpa only [he, List.append_assoc, List.cons_append, List.nil_append] using hxe
        · exact False.elim (acDistinct ht)
      obtain ⟨J, hj, hp, recover⟩ := contextRecovery h P A hat
      refine ⟨J, h, A, hj, Or.inl rfl, hat, hp, disjoint, ?_⟩
      intro P' hP'
      exact ⟨outside P' hP', recover P' (outside P' hP')⟩
    · let h : Address := v ++ [true]
      have hat : subtree h P = some E := by
        rw [show h = v ++ [true] from rfl, appendSubtree, hvat]
        rfl
      have outside (P' : Source) (hP' : Compatible H P') :
          ∀ u ∈ leaves P, ¬ h.IsPrefix u → readout u P' = readout u P := by
        intro u hu hout
        obtain ⟨w, b, z, he, hw⟩ := canonicalLeaf u hu
        subst u
        cases b with
        | true =>
          change subtree w P = some A at hw
          have hne : w ++ [false, true] ≠ x := by
            intro heq
            have hr := congrArg List.reverse (heq.trans hxe)
            simp [List.reverse_append] at hr
          have ha : w ++ [false, true] ∈ gamma H := by
            apply other _ _ hne
            rw [readAt, hw]
            rfl
          rw [readAt, fixedA w ha P' hP', readAt, hw]
        | false =>
          change subtree w P = some C at hw
          by_cases heq : w ++ [true, true] = x
          · have wv : w = v := List.append_left_injective [true, true] (heq.trans hxe)
            subst w
            cases z with
            | nil =>
              have hm : v ++ [] ∈ leafAddresses P := by
                simpa only [leafAddresses, List.mem_toFinset] using hu
              obtain ⟨c, hl⟩ := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).2 _ |>.mp hm
              have hr : readout (v ++ []) P = .branch := by rw [readAt, hvat]; rfl
              simp only [List.append_nil] at hr
              simp [leafLabel, hr] at hl
            | cons d z =>
              cases d with
              | true =>
                exfalso
                apply hout
                exact ⟨z, by simp [h, List.append_assoc]⟩
              | false =>
                have hpL := leftFixed P' hP'
                have hPL : subtree (v ++ [false]) P = some A := by
                  rw [appendSubtree, hvat]
                  rfl
                have eu : v ++ (false :: z) = (v ++ [false]) ++ z := by simp [List.append_assoc]
                rw [eu, readAt, hpL, readAt, hPL]
          · have hc' : w ++ [true, true] ∈ gamma H := by
              apply other _ _ heq
              rw [readAt, hw]
              rfl
            rw [readAt, fixedC w hc' P' hP', readAt, hw]
      have disjoint (d : Address × BlockKind) (hd : d ∈ forcedBlocks H) :
          ¬ d.1.IsPrefix h ∧ ¬ h.IsPrefix d.1 := by
        have hdP := (historyLaw H P hP).1 d hd
        have hkind : d.2.tree = A ∨ d.2.tree = C := by cases d.2 <;> simp [BlockKind.tree]
        rcases overlap P d.1 v d.2.tree C hkind (Or.inr rfl) hdP hvat with
          ⟨he, ht⟩ | hdis | ⟨_, ht, _⟩ | ⟨_, _, he⟩
        · exfalso
          apply hxng
          have hk : d.2 = .c := by
            cases hk : d.2 with
            | c => rfl
            | a => exact False.elim (acDistinct (by simpa only [hk, BlockKind.tree] using ht))
          apply (gammaShape H x).mpr
          exact Or.inr ⟨d.1, by simpa only [hk] using (show (d.1, d.2) ∈ forcedBlocks H from hd),
            Or.inr (hxe.trans (congrArg (· ++ [true, true]) he.symm))⟩
        · constructor
          · intro hpref
            rcases List.prefix_or_prefix_of_prefix hpref (List.prefix_append v [true]) with hdv | hvd
            · exact hdis.1 hdv
            · exact hdis.2 hvd
          · intro hpref
            exact hdis.2 ((List.prefix_append v [true]).trans hpref)
        · exact False.elim (acDistinct ht.symm)
        · rw [he]
          constructor <;> intro hpref <;>
            simp [h, List.prefix_append_right_inj] at hpref
      obtain ⟨J, hj, hp, recover⟩ := contextRecovery h P E hat
      refine ⟨J, h, E, hj, Or.inr rfl, hat, hp, disjoint, ?_⟩
      intro P' hP'
      exact ⟨outside P' hP', recover P' (outside P' hP')⟩
  refine ⟨zeroRecovery H P hP, singletonResult, ?_⟩
  intro hc P' hP' hn
  by_cases hz : (uncovered H P).card = 0
  · exact zeroRecovery H P hP hz P' hP'
  · have hone : (uncovered H P).card = 1 := by omega
    obtain ⟨J, h, X, _hj, hX, _hat, hp, _hd, competitors⟩ := singletonResult hone
    obtain ⟨Y, hy, hpy⟩ := (competitors P' hP').2
    have hlength : Y.length = X.length := by
      rw [← hp, ← hpy, context_length, context_length] at hn
      omega
    have hYX : Y = X := by
      rcases hX with rfl | rfl
      · exact (small P' hP'.1 h Y hy).2 (by simpa [A, E, FreeMagma.length] using hlength)
      · exact (small P' hP'.1 h Y hy).1 (by simpa [E, FreeMagma.length] using hlength)
    rw [← hpy, hYX, hp]

end D5.S3.Arith.FibonacciAtomic.ActualHistorySingleHoleRecovery

#print axioms D5.S3.Arith.FibonacciAtomic.ActualHistorySingleHoleRecovery.complete_history_rigidity
