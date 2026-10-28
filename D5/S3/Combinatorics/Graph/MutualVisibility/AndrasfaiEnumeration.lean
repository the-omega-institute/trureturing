/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiEnumeration
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Periodic labelled words are counted by transfer traces. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiCounting

/-! Labelled periodic avoiding words and their unique closed lifts. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration

open AndrasfaiLanguage AndrasfaiCounting
open scoped Classical

private theorem live_ne_reject (q : Fin 4) : liveState q ≠ 4 :=
  Fin.castSucc_ne_last q

private def forgetRun (N : ℕ) (hN : N % 3 ≠ 0) (p : ClosedRun N) :
    {labels : Fin N → Bool // PeriodicAvoidance (List.ofFn labels)} :=
  ⟨p.val.1, (exists_unique_closed_run _ (by simpa using hN)).mpr
    ⟨liveState p.val.2, ⟨live_ne_reject _, p.property⟩, by
      intro r hr
      exact closed_run_unique _ (by simpa using hN) r (liveState p.val.2)
        hr.1 (live_ne_reject _) hr.2 p.property⟩⟩

/-- Forgetting the live starting state is an actual equivalence: the unique
nonrejecting lift supplies its inverse, without identifying rotated words. -/
noncomputable def periodicWordEquivClosedRun (N : ℕ) (hN : N % 3 ≠ 0) :
    {labels : Fin N → Bool // PeriodicAvoidance (List.ofFn labels)} ≃ ClosedRun N :=
  (Equiv.ofBijective (forgetRun N hN) (by
    constructor
    · intro p r h
      have hl : p.val.1 = r.val.1 := congrArg Subtype.val h
      apply Subtype.ext
      apply Prod.ext hl
      apply Fin.castSucc_inj.mp
      exact closed_run_unique (List.ofFn p.val.1) (by simpa using hN)
        (liveState p.val.2) (liveState r.val.2)
        (live_ne_reject _) (live_ne_reject _) p.property (by rw [hl]; exact r.property)
    · intro w
      obtain ⟨q, hq, _⟩ :=
        (exists_unique_closed_run (List.ofFn w.val) (by simpa using hN)).mp w.property
      have hlt : q.val < 4 := by
        have hb := q.isLt
        have hn : q.val ≠ 4 := by
          intro hv
          apply hq.1
          apply Fin.ext
          simpa using hv
        omega
      let s : Fin 4 := ⟨q.val, hlt⟩
      have hs : liveState s = q := by apply Fin.ext; rfl
      refine ⟨⟨(w.val, s), ?_⟩, ?_⟩
      · change machine.evalFrom (liveState s) (List.ofFn w.val) = liveState s
        rw [hs]
        exact hq.2
      · apply Subtype.ext
        rfl)).symm

/-- Every positive labelled period of length not divisible by three is counted
by the original transfer trace, via the finite equivalence of closed lifts. -/
theorem periodic_word_card_eq_trace (N : ℕ) (hpos : 0 < N) (hN : N % 3 ≠ 0) :
    (Fintype.card {labels : Fin N → Bool // PeriodicAvoidance (List.ofFn labels)} : ℚ) =
      Matrix.trace (AndrasfaiTransfer.transfer ^ N) := by
  rw [Fintype.card_congr (periodicWordEquivClosedRun N hN)]
  exact closed_run_card_eq_trace N hpos

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiEnumeration
