import D5.S3.ConceptDynamics.PartialIdentification.ConditionalMarkovianBenefitBoundary
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.ConditionalMarkovianBenefitBoundary

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

run_elab do
  let proof ← Lean.Elab.Term.elabTerm (← `(term|
    (show ∃ (μα μβ μγ : Measure Bool)
      (A B C : Kernel (Bool × Bool) (Bool × Bool))
      (P : Measure ((Bool × Bool) × ((Bool × Bool) × (Bool × Bool)))),
      IsProbabilityMeasure μα ∧ IsProbabilityMeasure μβ ∧ IsProbabilityMeasure μγ ∧
      IsMarkovKernel A ∧ IsMarkovKernel B ∧ IsMarkovKernel C ∧
      IsProbabilityMeasure P ∧
      (∀ s : Bool × (Bool × Bool),
        (μα.prod (μβ.prod μγ)) {s} = ENNReal.ofReal
          (sharedRootSourceLaw.mass (s.2.2, (s.2.1, s.1)) : ℝ)) ∧
      (∀ a b c : Bool × Bool,
        P {(a, (b, c))} = ∫⁻ s : Bool × (Bool × Bool),
          A (s.2.1, s.2.2) {a} * B (s.2.2, s.1) {b} * C (s.1, s.2.1) {c}
          ∂(μα.prod (μβ.prod μγ))) ∧
      (∀ a b : Bool × Bool,
        (P.map (fun o => (o.1, o.2.1))) {(a, b)} =
          ENNReal.ofReal (sharedRootJointLaw.mass (a, b) : ℝ)) ∧
      P ≠ P.fst.prod (P.snd.fst.prod P.snd.snd)
    from by
      classical
      let root : PMF Bool := PMF.ofFintype (fun _ => (1 / 2 : ℝ≥0∞))
        (by
          simp only [Fintype.sum_bool, one_div, ← two_mul]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
      let μα : Measure Bool := Measure.dirac false
      let μβ : Measure Bool := Measure.dirac false
      let μγ : Measure Bool := root.toMeasure
      let μ := μα.prod (μβ.prod μγ)
      let fA : Bool × Bool → Bool × Bool := fun bg => (false, bg.2)
      let fB : Bool × Bool → Bool × Bool := fun ga => (false, ga.1)
      let fC : Bool × Bool → Bool × Bool := fun _ => (false, false)
      let A := Kernel.deterministic fA (measurable_of_countable _)
      let B := Kernel.deterministic fB (measurable_of_countable _)
      let C := Kernel.deterministic fC (measurable_of_countable _)
      let diag : Bool → (Bool × Bool) × ((Bool × Bool) × (Bool × Bool)) :=
        fun g => ((false, g), ((false, g), (false, false)))
      let P : Measure ((Bool × Bool) × ((Bool × Bool) × (Bool × Bool))) :=
        μγ.map diag
      have hd : Measurable diag := measurable_of_countable _
      haveI : IsProbabilityMeasure μα := by dsimp [μα]; infer_instance
      haveI : IsProbabilityMeasure μβ := by dsimp [μβ]; infer_instance
      haveI : IsProbabilityMeasure μγ := by dsimp [μγ]; infer_instance
      haveI : IsProbabilityMeasure P := by
        dsimp [P]
        infer_instance
      have hsource (s : Bool × (Bool × Bool)) :
          μ {s} = ENNReal.ofReal
            (sharedRootSourceLaw.mass (s.2.2, (s.2.1, s.1)) : ℝ) := by
        rcases s with ⟨a, b, c⟩
        cases a <;> cases b <;> cases c <;>
          norm_num [ENNReal.ofReal_div_of_pos, μ, μα, μβ, μγ, root, ← Set.singleton_prod_singleton,
            Measure.prod_prod, PMF.toMeasure_apply_singleton, PMF.ofFintype_apply,
            sharedRootSourceLaw, productResponseLaw, productResponseMass,
            balancedCovariateLaw, boolPointLaw, boolPointMass]
      have hformula (a b c : Bool × Bool) :
          P {(a, (b, c))} = ∫⁻ s : Bool × (Bool × Bool),
            A (s.2.1, s.2.2) {a} * B (s.2.2, s.1) {b} * C (s.1, s.2.1) {c} ∂μ := by
        rw [lintegral_fintype]
        simp_rw [hsource]
        rcases a with ⟨a₀, a₁⟩
        rcases b with ⟨b₀, b₁⟩
        rcases c with ⟨c₀, c₁⟩
        cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
          cases c₀ <;> cases c₁ <;>
          norm_num [ENNReal.ofReal_div_of_pos, P, μγ, root, Measure.map_apply hd (measurableSet_singleton _),
            PMF.toMeasure_apply_fintype, PMF.ofFintype_apply, Set.indicator,
            A, B, C, Kernel.deterministic_apply, fA, fB, fC, diag,
            sharedRootSourceLaw, productResponseLaw, productResponseMass,
            balancedCovariateLaw, boolPointLaw, boolPointMass,
            Fintype.sum_prod_type, Fintype.sum_bool]
      have hpair (a b : Bool × Bool) :
          (P.map (fun o => (o.1, o.2.1))) {(a, b)} =
            ENNReal.ofReal (sharedRootJointLaw.mass (a, b) : ℝ) := by
        dsimp [P]
        rw [Measure.map_map (measurable_of_countable _) hd]
        rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
        rcases a with ⟨a₀, a₁⟩
        rcases b with ⟨b₀, b₁⟩
        cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
          norm_num [ENNReal.ofReal_div_of_pos, μγ, root, PMF.toMeasure_apply_fintype, PMF.ofFintype_apply,
            sharedRootJointLaw_mass, diag, Set.indicator, Fintype.sum_bool]
      let first := pushforwardResponseLaw sharedRootJointLaw Prod.fst
      let second := pushforwardResponseLaw sharedRootJointLaw Prod.snd
      have hfirst (a : Bool × Bool) :
          P.fst {a} = ENNReal.ofReal (first.mass a : ℝ) := by
        change (P.map Prod.fst) {a} = _
        dsimp [P]
        rw [Measure.map_map measurable_fst hd]
        rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
        rcases a with ⟨a₀, a₁⟩
        cases a₀ <;> cases a₁ <;>
          norm_num [ENNReal.ofReal_div_of_pos, μγ, root, PMF.toMeasure_apply_fintype, PMF.ofFintype_apply,
            first, pushforwardResponseLaw, pushforwardSignatureMass,
            sharedRootJointLaw_mass, diag, Set.indicator,
            Fintype.sum_prod_type, Fintype.sum_bool]
      have hsecond (b : Bool × Bool) :
          P.snd.fst {b} = ENNReal.ofReal (second.mass b : ℝ) := by
        change ((P.map Prod.snd).map Prod.fst) {b} = _
        dsimp [P]
        rw [Measure.map_map measurable_snd hd,
          Measure.map_map measurable_fst (measurable_snd.comp hd)]
        rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
        rcases b with ⟨b₀, b₁⟩
        cases b₀ <;> cases b₁ <;>
          norm_num [ENNReal.ofReal_div_of_pos, μγ, root, PMF.toMeasure_apply_fintype, PMF.ofFintype_apply,
            second, pushforwardResponseLaw, pushforwardSignatureMass,
            sharedRootJointLaw_mass, diag, Set.indicator,
            Fintype.sum_prod_type, Fintype.sum_bool]
      refine ⟨μα, μβ, μγ, A, B, C, P, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance, hsource, hformula,
        hpair, ?_⟩
      intro hfactor
      apply shared_root_responses_do_not_factorize
      refine ⟨first, second, ?_⟩
      funext ab
      rcases ab with ⟨a, b⟩
      have hmass : ENNReal.ofReal (sharedRootJointLaw.mass (a, b) : ℝ) =
          ENNReal.ofReal (first.mass a : ℝ) * ENNReal.ofReal (second.mass b : ℝ) := by
        calc
          _ = (P.map (fun o => (o.1, o.2.1))) {(a, b)} := (hpair a b).symm
          _ = P ({a} ×ˢ ({b} ×ˢ Set.univ)) := by
            rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
            congr 1
            ext o
            simp
          _ = (P.fst.prod (P.snd.fst.prod P.snd.snd))
              ({a} ×ˢ ({b} ×ˢ Set.univ)) := congrArg
                (fun ν : Measure ((Bool × Bool) × ((Bool × Bool) × (Bool × Bool))) =>
                  ν ({a} ×ˢ ({b} ×ˢ Set.univ))) hfactor
          _ = P.fst {a} * (P.snd.fst {b} * P.snd.snd Set.univ) := by
            rw [Measure.prod_prod, Measure.prod_prod]
          _ = _ := by rw [measure_univ, mul_one, hfirst, hsecond]
      have hj : 0 ≤ (sharedRootJointLaw.mass (a, b) : ℝ) := by
        exact_mod_cast sharedRootJointLaw.nonnegative (a, b)
      have hf : 0 ≤ (first.mass a : ℝ) := by exact_mod_cast first.nonnegative a
      have hs : 0 ≤ (second.mass b : ℝ) := by exact_mod_cast second.nonnegative b
      have hreal := congrArg ENNReal.toReal hmass
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hj,
        ENNReal.toReal_ofReal hf, ENNReal.toReal_ofReal hs] at hreal
      exact_mod_cast hreal))) none

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
