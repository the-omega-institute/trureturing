import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

open MeasureTheory

run_elab do
  let proof ← Lean.Elab.Term.elabTerm (← `(term|
    (show ∀ {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] (a : Measure α) (b : Measure β) (c : Measure γ)
      [IsProbabilityMeasure a] [IsProbabilityMeasure b] [IsProbabilityMeasure c],
      let μ := a.prod (b.prod c)
      (μ.fst = a ∧ μ.snd.fst = b ∧ μ.snd.snd = c) ∧
      InformationTheory.klDiv μ (μ.fst.prod (μ.snd.fst.prod μ.snd.snd)) = 0
    from by
      intro α β γ _ _ _ a b c _ _ _
      dsimp only
      haveI : IsProbabilityMeasure (b.prod c) := inferInstance
      haveI : IsProbabilityMeasure (a.prod (b.prod c)) := inferInstance
      haveI : IsFiniteMeasure (a.prod (b.prod c)) := inferInstance
      haveI : SigmaFinite (a.prod (b.prod c)) := inferInstance
      have ha : (a.prod (b.prod c)).fst = a := Measure.fst_prod
      have hb : (a.prod (b.prod c)).snd.fst = b := by
        rw [Measure.snd_prod, Measure.fst_prod]
      have hc : (a.prod (b.prod c)).snd.snd = c := by
        rw [Measure.snd_prod, Measure.snd_prod]
      exact ⟨⟨ha, hb, hc⟩, by
        rw [ha, hb, hc]
        exact InformationTheory.klDiv_self (a.prod (b.prod c))⟩))) none

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
