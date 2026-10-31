import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

open MeasureTheory

example {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (a : Measure α) (b : Measure β) (c : Measure γ)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c] :
    let μ := a.prod (b.prod c)
    (μ.fst = a ∧ μ.snd.fst = b ∧ μ.snd.snd = c) ∧
    InformationTheory.klDiv μ (μ.fst.prod (μ.snd.fst.prod μ.snd.snd)) = 0 := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact (by
      dsimp only
      haveI : IsProbabilityMeasure (b.prod c) := inferInstance
      haveI : IsProbabilityMeasure (a.prod (b.prod c)) := inferInstance
      haveI : IsFiniteMeasure (a.prod (b.prod c)) := inferInstance
      haveI : SigmaFinite (a.prod (b.prod c)) := inferInstance
      have ha : (a.prod (b.prod c)).fst = a :=
        Measure.fst_prod (μ := a) (ν := b.prod c)
      have hbc : (a.prod (b.prod c)).snd = b.prod c :=
        Measure.snd_prod (μ := a) (ν := b.prod c)
      have hb : (a.prod (b.prod c)).snd.fst = b := by
        rw [hbc]
        exact Measure.fst_prod (μ := b) (ν := c)
      have hc : (a.prod (b.prod c)).snd.snd = c := by
        rw [hbc]
        exact Measure.snd_prod (μ := b) (ν := c)
      exact ⟨⟨ha, hb, hc⟩, by
        rw [ha, hb, hc]
        exact InformationTheory.klDiv_self (a.prod (b.prod c))⟩)))
    let proof ← Lean.instantiateMVars (Lean.mkMVar goal)
    unless !proof.hasMVar && !proof.hasSorry do
      throwError "exact application contains unresolved metavariables or sorry"
    Lean.Meta.checkWithKernel proof
    let ty ← Lean.Meta.inferType proof
    let mut axs : Lean.NameSet := {}
    for c in (proof.getUsedConstants ++ ty.getUsedConstants) do
      for ax in (← Lean.collectAxioms c) do
        axs := axs.insert ax
    for ax in axs.toArray do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unaccepted exact-application axiom: {ax}"
    Lean.logInfo m!"EXACT_KERNEL_ACCEPTED axioms={axs.toArray}"
