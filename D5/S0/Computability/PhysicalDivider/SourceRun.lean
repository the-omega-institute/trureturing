/- GID: D5/S0/Computability/PhysicalDivider/SourceRun
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded physical refinement of complete finite source executions. -/

import D5.S0.Computability.PhysicalDivider.ExecutionBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- One fixed physical time constant for the entire divider program. -/
def sourceStepBudget : ℕ := 1 + ∑ l : DivLabel, statementBudget (divMachine.m l)

/-- Every head and support point remains inside the same fixed interval through
all source statements and their physical interiors. Bounds on source occupancy
are supplied per checkpoint, independently of the total arithmetic runtime. -/
theorem source_run_refinement (n : ℕ) (initial final : divMachine.Cfg)
    (hrun : ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[n])
      (some initial) = some final)
    (L : ℕ)
    (hlength : ∀ i ≤ n, ∀ c,
      ((fun o : Option divMachine.Cfg => o.bind divMachine.step)^[i])
        (some initial) = some c → ∀ k, (c.stk k).length ≤ L)
    (frame : FrameTape → Tape Bool) (frameHeads : FrameTape → ℤ)
    (hframe : ∀ k, 0 ≤ frameHeads k ∧ frameHeads k ≤ 2 * L)
    (hwithin : LocatedWithin (locatedSourceCfg initial frame frameHeads)
      (fun _ => -(sourceStepBudget : ℤ))
      (fun _ => 2 * L + sourceStepBudget)) :
    ∃ m ≤ sourceStepBudget * n,
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[m])
        (some (locatedSourceCfg initial frame frameHeads)) =
        some (locatedSourceCfg final frame frameHeads) ∧
      ∀ j ≤ m, ∃ c,
        ((fun o : Option LocatedCfg => o.bind locatedStep)^[j])
          (some (locatedSourceCfg initial frame frameHeads)) = some c ∧
        LocatedWithin c (fun _ => -(sourceStepBudget : ℤ))
          (fun _ => 2 * L + sourceStepBudget) := by
  classical
  let src := fun o : Option divMachine.Cfg => o.bind divMachine.step
  let phy := fun o : Option LocatedCfg => o.bind locatedStep
  have one (a b : divMachine.Cfg) (hs : divMachine.step a = some b) :
      ∃ m ≤ sourceStepBudget, (phy^[m])
        (some (locatedSourceCfg a frame frameHeads)) =
        some (locatedSourceCfg b frame frameHeads) := by
    rcases a with ⟨label, state, words⟩
    cases label with
    | none => simp [FinTM2.step, TM2.step] at hs
    | some label =>
      simp only [FinTM2.step, TM2.step, Option.some.injEq] at hs
      subst b
      by_cases hd : label = .done
      · subst label
        refine ⟨1, by dsimp [sourceStepBudget]; omega, ?_⟩
        rfl
      · obtain ⟨m, hm, he⟩ := source_statement_execution (sourceEntry label)
          state words frame frameHeads
        refine ⟨m + 1, ?_, ?_⟩
        · have hb := Finset.single_le_sum (s := (Finset.univ : Finset DivLabel)) (f := fun l : DivLabel => statementBudget (divMachine.m l))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (α := DivLabel) label)
          dsimp [sourceEntry] at hm
          dsimp [sourceStepBudget]
          omega
        · rw [Function.iterate_succ_apply]
          have first : locatedStep (locatedSourceCfg ⟨some label, state, words⟩ frame frameHeads) =
              some (locatedStmtCfg (sourceEntry label) state words frame frameHeads) := by
            cases label <;> simp_all [locatedSourceCfg, sourceCfg, locatedStmtCfg, locatedStep,
              instruction, controlRead, executeInstruction, advanceHeads]
          change (phy^[m]) (locatedStep _) = _
          rw [first]
          exact he
  induction n generalizing initial with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
    subst final
    refine ⟨0, by omega, rfl, ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    exact ⟨locatedSourceCfg initial frame frameHeads, rfl, hwithin⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hrun
    cases hs : divMachine.step initial with
    | none =>
      change (src^[n]) (divMachine.step initial) = _ at hrun
      rw [hs, Function.iterate_fixed (show src none = none from rfl)] at hrun
      contradiction
    | some next =>
      change (src^[n]) (divMachine.step initial) = _ at hrun
      rw [hs] at hrun
      obtain ⟨m, hm, hfirst⟩ := one initial next hs
      have hheads : ∀ k, 0 ≤ (locatedSourceCfg initial frame frameHeads).2 k ∧
          (locatedSourceCfg initial frame frameHeads).2 k ≤ 2 * L := by
        intro k
        cases k with
        | inl k =>
          have h := hlength 0 (by omega) initial rfl k
          dsimp [locatedSourceCfg, logicalHeads]
          constructor <;> omega
        | inr k => exact hframe k
      have hfirstWithin : ∀ j ≤ m, ∃ c,
          (phy^[j]) (some (locatedSourceCfg initial frame frameHeads)) = some c ∧
          LocatedWithin c (fun _ => -(sourceStepBudget : ℤ))
            (fun _ => 2 * L + sourceStepBudget) := by
        intro j hj
        obtain ⟨c, hc, _, hb, hw⟩ := located_run_bounds _ _ m hfirst _ _ hwithin j hj
        refine ⟨c, hc, ?_⟩
        intro k
        have hk := hheads k
        have hlow : min (-(sourceStepBudget : ℤ))
            ((locatedSourceCfg initial frame frameHeads).2 k - j) = -(sourceStepBudget : ℤ) := by
          apply min_eq_left; omega
        have hhigh : max (2 * (L : ℤ) + sourceStepBudget)
            ((locatedSourceCfg initial frame frameHeads).2 k + j) = 2 * L + sourceStepBudget := by
          apply max_eq_left; omega
        simpa only [hlow, hhigh] using hw k
      have hnextWithin : LocatedWithin (locatedSourceCfg next frame frameHeads)
          (fun _ => -(sourceStepBudget : ℤ)) (fun _ => 2 * L + sourceStepBudget) := by
        obtain ⟨c, hc, hw⟩ := hfirstWithin m le_rfl
        rw [hfirst] at hc
        cases hc
        exact hw
      have htail : ∀ i ≤ n, ∀ c, (src^[i]) (some next) = some c →
          ∀ k, (c.stk k).length ≤ L := by
        intro i hi c hc
        apply hlength (i + 1) (by omega) c
        rw [Function.iterate_succ_apply]
        change (src^[i]) (divMachine.step initial) = some c
        rw [hs]
        exact hc
      obtain ⟨p, hp, hrest, hall⟩ := ih next hrun htail hnextWithin
      refine ⟨p + m, ?_, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply]
        change (phy^[p]) ((phy^[m]) _) = _
        rw [hfirst]
        exact hrest
      · intro j hj
        by_cases hjm : j ≤ m
        · exact hfirstWithin j hjm
        · obtain ⟨c, hc, hw⟩ := hall (j - m) (by omega)
          refine ⟨c, ?_, hw⟩
          rw [show j = (j - m) + m by omega, Function.iterate_add_apply]
          change (phy^[j-m]) ((phy^[m]) _) = _
          rw [hfirst]
          exact hc

end D5.S0.Computability.PhysicalDivider
