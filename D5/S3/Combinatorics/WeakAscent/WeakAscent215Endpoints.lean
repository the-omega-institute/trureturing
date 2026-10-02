/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints
   mirror-E: none(waiver:record-endings-and-surviving-old-sites)
   anchors: []
   utility: none
   digest: Removes final records bijectively and counts the old sites surviving original cuts. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Decomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Endpoints

open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Decomposition

noncomputable def oldCount (history : PureHistory) : ℕ :=
  (Classical.choose history.property).count true

def finalPiece {gap : ℕ} : OriginalPieces gap → PureHistory
  | .final history => history
  | .cut _ _ rest => finalPiece rest
theorem record_endings :
    (∃ replayEquiv :
        {history : PureHistory //
          ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]} ≃
          PureHistory × ℕ,
      ∀ data, (replayEquiv.symm data).val.val = data.1.val ++ [.record data.2] ∧
        (replayEquiv.symm data).val.val.length = data.1.val.length + 1 ∧
        spend (replayEquiv.symm data).val.val = spend data.1.val + data.2) := by
  classical
  have split_run (initialSteps suffix : List PureStep) (stack ending : List Bool) :
      PureRun stack (initialSteps ++ suffix) ending ↔
        ∃ middle, PureRun stack initialSteps middle ∧ PureRun middle suffix ending := by
    induction initialSteps generalizing stack with
    | nil =>
      constructor
      · intro hrun
        exact ⟨stack, PureRun.nil _, hrun⟩
      · rintro ⟨middle, hprefix, hsuffix⟩
        cases hprefix
        exact hsuffix
    | cons first rest ih =>
      cases first with
      | record gap =>
        constructor
        · intro hrun
          cases hrun with
          | record _ _ _ _ htail =>
            obtain ⟨middle, hprefix, hsuffix⟩ := (ih _).mp htail
            exact ⟨middle, PureRun.record _ _ _ _ hprefix, hsuffix⟩
        · rintro ⟨middle, hprefix, hsuffix⟩
          cases hprefix with
          | record _ _ _ _ htail =>
            exact PureRun.record _ _ _ _ ((ih _).mpr ⟨middle, htail, hsuffix⟩)
      | descend site =>
        constructor
        · intro hrun
          cases hrun with
          | descend _ _ _ _ hsite hfresh htail =>
            obtain ⟨middle, hprefix, hsuffix⟩ := (ih _).mp htail
            exact ⟨middle, PureRun.descend _ _ _ _ hsite hfresh hprefix, hsuffix⟩
        · rintro ⟨middle, hprefix, hsuffix⟩
          cases hprefix with
          | descend _ _ _ _ hsite hfresh htail =>
            exact PureRun.descend _ _ _ _ hsite hfresh ((ih _).mpr ⟨middle, htail, hsuffix⟩)
  have spendAppend (initialSteps suffix : List PureStep) :
      spend (initialSteps ++ suffix) = spend initialSteps + spend suffix := by
    induction initialSteps with
    | nil => simp [spend]
    | cons first rest ih => cases first <;> simp [spend, ih, Nat.add_assoc]
  have lastUnique (first second : List PureStep) (firstGap secondGap : ℕ)
      (heq : first ++ [.record firstGap] = second ++ [.record secondGap]) :
      first = second ∧ firstGap = secondGap := by
    have hlength : first.length = second.length := by
      have h := congrArg List.length heq
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      omega
    obtain ⟨hprefix, hlast⟩ := List.append_inj heq hlength
    exact ⟨hprefix, by simpa using hlast⟩
  let endingHistory :=
    {history : PureHistory // ∃ initialSteps gap, history.val = initialSteps ++ [.record gap]}
  let remove : endingHistory → PureHistory × ℕ := fun history => by
    let initialSteps := Classical.choose history.property
    let gap := Classical.choose (Classical.choose_spec history.property)
    have heq : history.val.val = initialSteps ++ [.record gap] :=
      Classical.choose_spec (Classical.choose_spec history.property)
    have hpure : ∃ middle, PureRun [] initialSteps middle := by
      obtain ⟨ending, hrun⟩ := history.val.property
      rw [heq] at hrun
      obtain ⟨middle, hprefix, _⟩ := (split_run initialSteps [.record gap] [] ending).mp hrun
      exact ⟨middle, hprefix⟩
    exact (⟨initialSteps, hpure⟩, gap)
  let append : PureHistory × ℕ → endingHistory := fun data => by
    refine ⟨⟨data.1.val ++ [.record data.2], ?_⟩, data.1.val, data.2, rfl⟩
    obtain ⟨ending, hrun⟩ := data.1.property
    refine ⟨ending ++ List.replicate data.2 false ++ [true], ?_⟩
    apply (split_run _ _ _ _).mpr
    exact ⟨ending, hrun, PureRun.record _ _ _ _ (PureRun.nil _)⟩
  have remove_spec (history : endingHistory) :
      history.val.val = (remove history).1.val ++ [.record (remove history).2] := by
    exact Classical.choose_spec (Classical.choose_spec history.property)
  have append_spec (data : PureHistory × ℕ) :
      (append data).val.val = data.1.val ++ [.record data.2] := by
    rfl
  let replayEquiv : endingHistory ≃ PureHistory × ℕ :=
    { toFun := remove
      invFun := append
      left_inv := fun history => by
        apply Subtype.ext
        apply Subtype.ext
        rw [append_spec, ← remove_spec]
      right_inv := fun data => by
        have heq := (remove_spec (append data)).symm.trans (append_spec data)
        obtain ⟨hprefix, hgap⟩ := lastUnique _ _ _ _ heq
        apply Prod.ext
        · exact Subtype.ext hprefix
        · exact hgap }
  refine ⟨replayEquiv, ?_⟩
  intro data
  have heq : (replayEquiv.symm data).val.val = data.1.val ++ [.record data.2] := append_spec data
  refine ⟨heq, (congrArg List.length heq).trans (by simp), ?_⟩
  exact (congrArg spend heq).trans (by rw [spendAppend]; simp [spend])
end D5.S3.Combinatorics.WeakAscent.WeakAscent215Endpoints
