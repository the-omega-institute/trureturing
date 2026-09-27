/- GID: D5/S0/Computability/PhysicalDivider/ExecutionBounds
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical support and head displacement through every prefix of a bit execution. -/

import D5.S0.Computability.PhysicalDivider.SourceSimulation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing

/-- A fixed interval contains both the physical support and the current head. -/
def LocatedWithin (c : LocatedCfg) (low high : ActiveTape → ℤ) : Prop :=
  ∀ k, Within (c.1.tapes k) ⟨c.2 k, low k, high k⟩

/-- Every prefix exists, projects to the actual physical execution, and retains
all initially occupied and subsequently visited cells in a bounded interval.
The bound uses the starting head, never a reset of an erased tape's footprint. -/
theorem located_run_bounds (initial final : LocatedCfg) (n : ℕ)
    (hrun : ((fun o : Option LocatedCfg => o.bind locatedStep)^[n]) (some initial) = some final)
    (low high : ActiveTape → ℤ) (hwithin : LocatedWithin initial low high) :
    ∀ i ≤ n, ∃ c,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some initial) = some c ∧
      ((fun o : Option PhysicalCfg => o.bind physicalStep)^[i]) (some initial.1) = some c.1 ∧
      (∀ k, initial.2 k - i ≤ c.2 k ∧ c.2 k ≤ initial.2 k + i) ∧
      LocatedWithin c (fun k => min (low k) (initial.2 k - i))
        (fun k => max (high k) (initial.2 k + i)) := by
  have one (c d : LocatedCfg) (hs : locatedStep c = some d) (k : ActiveTape) :
      c.2 k - 1 ≤ d.2 k ∧ d.2 k ≤ c.2 k + 1 ∧
      ∀ j : ℤ, (d.1.tapes k).nth j = true →
        (∃ h : ℤ, (c.1.tapes k).nth h = true ∧ d.2 k + j = c.2 k + h) ∨
        d.2 k + j = c.2 k := by
    unfold locatedStep at hs
    cases ha : instruction c.1.control with
    | none => simp [ha] at hs
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hs
      subst d
      cases a with
      | read t next =>
        simp only [executeInstruction, advanceHeads]
        refine ⟨by omega, by omega, ?_⟩
        intro j hj
        exact Or.inl ⟨j, hj, rfl⟩
      | write t bit next =>
        simp only [executeInstruction, advanceHeads]
        refine ⟨by omega, by omega, ?_⟩
        intro j hj
        by_cases hk : k = t
        · subst k
          simp only [Function.update_self] at hj
          by_cases hj0 : j = 0
          · right; omega
          · rw [Tape.write_nth, if_neg hj0] at hj
            exact Or.inl ⟨j, hj, rfl⟩
        · rw [Function.update_of_ne hk] at hj
          exact Or.inl ⟨j, hj, rfl⟩
      | move t dir next =>
        cases dir <;> simp only [executeInstruction, advanceHeads]
        all_goals
          by_cases hk : k = t
          · subst k
            simp only [Function.update_self]
            refine ⟨by omega, by omega, ?_⟩
            intro j hj
            first
            | rw [Tape.move_left_nth] at hj
              exact Or.inl ⟨j - 1, hj, by omega⟩
            | rw [Tape.move_right_nth] at hj
              exact Or.inl ⟨j + 1, hj, by omega⟩
          · simp only [Function.update_of_ne hk]
            refine ⟨by omega, by omega, ?_⟩
            intro j hj
            exact Or.inl ⟨j, hj, rfl⟩
  have project : Function.Semiconj (Option.map Prod.fst)
      (fun o : Option LocatedCfg => o.bind locatedStep)
      (fun o : Option PhysicalCfg => o.bind physicalStep) := by
    intro o
    cases o with
    | none => rfl
    | some c =>
      simp only [Option.map_some, Option.bind_some, locatedStep, physicalStep,
        Option.map_map, Function.comp_def]
  have hasPrefix (i : ℕ) (hi : i ≤ n) : ∃ c,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some initial) = some c := by
    cases hc : ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some initial) with
    | some c => exact ⟨c, rfl⟩
    | none =>
      rw [show n = (n - i) + i by omega, Function.iterate_add_apply, hc,
        Function.iterate_fixed (show (none : Option LocatedCfg).bind locatedStep = none from rfl)] at hrun
      contradiction
  have inv (i : ℕ) (c : LocatedCfg)
      (hc : ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some initial) = some c) :
      (∀ k, initial.2 k - i ≤ c.2 k ∧ c.2 k ≤ initial.2 k + i) ∧
      LocatedWithin c (fun k => min (low k) (initial.2 k - i))
        (fun k => max (high k) (initial.2 k + i)) := by
    induction i generalizing c with
    | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hc
      subst c
      constructor
      · intro k; simp
      · intro k
        rcases hwithin k with ⟨hl, hh, ht⟩
        simpa [Within, min_eq_left hl, max_eq_left hh] using hwithin k
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at hc
      cases he : ((fun o : Option LocatedCfg => o.bind locatedStep)^[i]) (some initial) with
      | none => simp [he] at hc
      | some previous =>
        rw [he] at hc
        have hp := ih previous he
        have hs := fun k => one previous c hc k
        constructor
        · intro k
          have := hp.1 k
          have := (hs k).1
          have := (hs k).2.1
          push_cast
          omega
        · intro k
          rcases hp.2 k with ⟨hl, hh, ht⟩
          dsimp only at hl hh ht
          have hd := hp.1 k
          have hd' := hs k
          dsimp only [Within]
          push_cast
          refine ⟨by omega, by omega, ?_⟩
          intro j hj
          rcases hd'.2.2 j hj with ⟨h, hdata, hpos⟩ | hpos
          · have := ht h hdata
            constructor <;> omega
          · constructor <;> omega
  intro i hi
  obtain ⟨c, hc⟩ := hasPrefix i hi
  obtain ⟨hb, hw⟩ := inv i c hc
  refine ⟨c, hc, ?_, hb, hw⟩
  have h := (project.iterate_right i) (some initial)
  rw [hc] at h
  exact h.symm

end D5.S0.Computability.PhysicalDivider
