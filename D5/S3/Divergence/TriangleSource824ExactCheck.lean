import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

open MeasureTheory

run_elab do
  let proof ← Lean.Elab.Term.elabTerm (← `(term|
    (fun {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] (a : Measure α) (b : Measure β) (c : Measure γ)
      [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c] =>
      (show
        let μ := Measure.prod a (Measure.prod b c)
        (Measure.fst μ = a ∧ Measure.fst (Measure.snd μ) = b ∧
          Measure.snd (Measure.snd μ) = c) ∧
        InformationTheory.klDiv μ
          (Measure.prod (Measure.fst μ)
            (Measure.prod (Measure.fst (Measure.snd μ)) (Measure.snd (Measure.snd μ)))) = 0
      from by
        dsimp only
        haveI : IsProbabilityMeasure (Measure.prod b c) := inferInstance
        haveI : IsProbabilityMeasure (Measure.prod a (Measure.prod b c)) := inferInstance
        haveI : IsFiniteMeasure (Measure.prod a (Measure.prod b c)) := inferInstance
        haveI : SigmaFinite (Measure.prod a (Measure.prod b c)) := inferInstance
        have ha : Measure.fst (Measure.prod a (Measure.prod b c)) = a :=
          Measure.fst_prod (μ := a) (ν := Measure.prod b c)
        have hbc : Measure.snd (Measure.prod a (Measure.prod b c)) = Measure.prod b c :=
          Measure.snd_prod (μ := a) (ν := Measure.prod b c)
        have hb : Measure.fst (Measure.snd (Measure.prod a (Measure.prod b c))) = b := by
          rw [hbc]
          exact Measure.fst_prod (μ := b) (ν := c)
        have hc : Measure.snd (Measure.snd (Measure.prod a (Measure.prod b c))) = c := by
          rw [hbc]
          exact Measure.snd_prod (μ := b) (ν := c)
        exact ⟨⟨ha, hb, hc⟩, by
          rw [ha, hb, hc]
          exact InformationTheory.klDiv_self (Measure.prod a (Measure.prod b c))⟩)))) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← Lean.instantiateMVars proof
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
