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
      dsimp
      constructor
      · simp only [Measure.fst_prod, Measure.snd_prod, and_self]
      · simpa only [Measure.fst_prod, Measure.snd_prod] using
          InformationTheory.klDiv_self (a.prod (b.prod c))))) none

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
  logInfo m!"EXACT_KERNEL_ACCEPTED axioms={axs.toArray}"
