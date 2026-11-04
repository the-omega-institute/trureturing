/- GID: D5/S3/Observer/RationalRouting/Prices
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/Prices
   mirror-E: none(waiver:actual-finite-acquisition)
   anchors: []
   utility: none
   digest: Exact original-view action prices are two for acquired control and four for preset control. -/

import D5.S3.Observer.RationalRouting.Acquisition
import D5.S3.Observer.RationalRouting.Views

/-! Exact least uniform action caps for the original finite views. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting

/-- Only the finite whole-output calculation changes. All physical instructions,
read exponents, report continuations and local state remain those of the code. -/
def mapOutput {State A B : Type} (f : A → B) (code : State → Command State A) :
    State → Command State B := fun st =>
  match code st with
  | .halt a => .halt (f a)
  | .work next => .work next
  | .move b next => .move b next
  | .read s next => .read s next

/-- Feasibility quantifies over a larger extensional deterministic class.
The attaining codes below are explicit finite executable definitions. -/
def Feasible (V : View) (h : ℕ) (preset : Bool) : Prop :=
  ∃ (State : Type) (code : State → Command State (ViewOutput V)) (init : State),
    Correct code init (originalView V) ∧ ActionCap code init h ∧
    (preset = true → ∃ schedule : ℕ → Bool, Preset code init schedule)

private theorem map_run {State A B : Type} {code : State → Command State A}
    (f : A → B) {x : ℚ} {st : State} {w : List Bool} {out : A} {v : List Bool}
    {reads : List (List Bool × ℕ)} (run : Run code x st w out v reads) :
    Run (mapOutput f code) x st w (f out) v reads := by
  induction run with
  | halt h => exact Run.halt (by simp [mapOutput,h])
  | work h _ ih => exact Run.work (by simp [mapOutput,h]) ih
  | move h _ ih => exact Run.move (by simp [mapOutput,h]) ih
  | read h _ ih => exact Run.read (by simp [mapOutput,h]) ih

private theorem mapped_correct {State B : Type} {code : State → Command State ℚ}
    {init : State} (f : ℚ → B) (correct : Correct code init id) :
    Correct (mapOutput f code) init f := by
  intro x hx
  obtain ⟨out,v,reads,run⟩ := (correct x hx).1
  have hout : out = x := (correct x hx).2 _ _ _ run
  subst out
  have mapped := map_run f run
  refine ⟨⟨f x,v,reads,mapped⟩,?_⟩
  intro out v' reads' run'
  exact (run_unique run' mapped).1

private theorem mapped_cap {State B : Type} {code : State → Command State ℚ}
    {init : State} (f : ℚ → B) (correct : Correct code init id) {h : ℕ}
    (cap : ActionCap code init h) : ActionCap (mapOutput f code) init h := by
  intro x hx out v reads run
  obtain ⟨out',v',reads',original⟩ := (correct x hx).1
  have same := (run_unique run (map_run f original)).2.1
  rw [same]
  exact cap x hx out' v' reads' original

private theorem mapped_preset {State B : Type} {code : State → Command State ℚ}
    {init : State} (f : ℚ → B) (correct : Correct code init id) {schedule : ℕ → Bool}
    (preset : Preset code init schedule) : Preset (mapOutput f code) init schedule := by
  intro x hx out v reads run
  obtain ⟨out',v',reads',original⟩ := (correct x hx).1
  have same := (run_unique run (map_run f original)).2.1
  rw [same]
  exact preset x hx out' v' reads' original

/-- Each original boundary, chronological word, named rooted path, indexed
prefix-memory table and their joint full output has least uniform acquired
cap two and least uniform preset cap four. Both included endpoints and every
unbounded tail index are covered by actual finite same-source executions. -/
theorem original_view_action_prices (V : View) :
    Feasible V 2 false ∧ (∀ h, Feasible V h false → 2 ≤ h) ∧
    Feasible V 4 true ∧ (∀ h, Feasible V h true → 4 ≤ h) := by
  obtain ⟨crec,brec,cpre,bpre,ppre,pos⟩ := actual_rational_acquisition
  have hinj : Set.InjOn (originalView V) {x | Prior x} := by
    intro x hx y hy heq
    have h1 := original_views_reconstruct.2.2.1 V x (pos x hx)
    have h2 := original_views_reconstruct.2.2.1 V y (pos y hy)
    exact h1.symm.trans ((congrArg (recoverView V) heq).trans h2)
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨AcquisitionState,mapOutput (originalView V) (acquisitionCode false),
      .start,mapped_correct _ crec,mapped_cap _ crec brec,?_⟩
    intro h; cases h
  · rintro h ⟨State,code,init,correct,cap,_⟩
    exact (original_action_lower_bounds correct hinj).1 h cap
  · refine ⟨AcquisitionState,mapOutput (originalView V) (acquisitionCode true),
      .start,mapped_correct _ cpre,mapped_cap _ cpre bpre,?_⟩
    intro _
    exact ⟨_,mapped_preset _ cpre ppre⟩
  · rintro h ⟨State,code,init,correct,cap,preset⟩
    obtain ⟨schedule,hs⟩ := preset rfl
    exact (original_action_lower_bounds correct hinj).2 schedule hs h cap

#print axioms original_view_action_prices

end D5.S3.Observer.RationalRouting
