import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins

open MeasureTheory ProbabilityTheory Filter Set LeanInformationAudit
open scoped ENNReal Topology
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := (ℕ → Type u) × ℕ
  State p := History p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Past p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p ω i => ω i) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p ω i =>
    (Classical.choice (show Nonempty (History p.1) from ⟨ω⟩)) i)
    (fun e => nomatch e)

def changeArena : Arena where
  signature := signature.{u}
  Law R := ∀ (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]
    (P Q : Measure (History X)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    (κ : (n : ℕ) → Kernel (Past X n) (Future X n)) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n, P.map (split X n) = (P.map (past X n)) ⊗ₘ κ n),
    Measurable (likelihood P Q) ∧
    (∀ ω, 0 ≤ likelihood P Q ω) ∧
    Integrable (likelihood P Q) P ∧
    (∫ ω, likelihood P Q ω ∂P) = 1 ∧
    P.withDensity (finiteDensity P Q) = Q ∧
    (∀ᵐ ω ∂Q, 0 < likelihood P Q ω) ∧
    ∀ n, Measurable (rowMass (κ n) (splitDensity X P Q n)) ∧
      Measurable (Function.uncurry (rowDensity (κ n) (splitDensity X P Q n))) ∧
      (∀ a b, rowDensity (κ n) (splitDensity X P Q n) a b ≠ ∞) ∧
      (∀ a, (∫⁻ b, rowDensity (κ n) (splitDensity X P Q n) a b ∂κ n a) = 1) ∧
      IsMarkovKernel (changedKernel X P Q n (κ n)) ∧
      Q.map (R.readout () (X, n)) =
        (P.map (past X n)).withDensity (rowMass (κ n) (splitDensity X P Q n)) ∧
      (∫⁻ a, rowMass (κ n) (splitDensity X P Q n) a ∂P.map (past X n)) = 1 ∧
      Q.map (split X n) = (Q.map (past X n)) ⊗ₘ changedKernel X P Q n (κ n) ∧
      ((fun ω => (rowMass (κ n) (splitDensity X P Q n) (past X n ω)).toReal)
        =ᵐ[P] P[likelihood P Q | Filtration.piLE (X := X) n]) ∧
      (∀ᵐ a ∂Q.map (past X n), a ∈ goodRows (κ n) (splitDensity X P Q n))

def mergingArena : Arena where
  signature := signature.{u}
  Law R := ∀ (X : ℕ → Type u) [∀ i, MeasurableSpace (X i)]
    (P Q : Measure (History X)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P)
    (κ : (n : ℕ) → Kernel (Past X n) (Future X n)) [∀ n, IsMarkovKernel (κ n)]
    (hκ : ∀ n, P.map (split X n) = (P.map (past X n)) ⊗ₘ κ n),
    ∃ eta : (n : ℕ) → Kernel (Past X n) (Future X n),
      (∀ n, IsMarkovKernel (eta n)) ∧
      (∀ n, Q.map (split X n) = (Q.map (R.readout () (X, n))) ⊗ₘ eta n) ∧
      ∀ᵐ ω ∂Q, Tendsto
        (fun n => sSup (Set.range (fun C : {C : Set (Future X n) // MeasurableSet C} =>
          |(κ n (past X n ω)).real C.val - (eta n (past X n ω)).real C.val|)))
        atTop (𝓝 0)

private abbrev Toy : ℕ → Type u := fun _ => ULift.{u} Bool

private def seed : History.{u} Toy := fun _ => ⟨false⟩

private def basePath : History.{u} Toy :=
  Classical.choice (show Nonempty (History.{u} Toy) from ⟨seed⟩)

private def counterPath : History.{u} Toy := fun i =>
  ULift.up.{u} (!((basePath i).down))

private def toyLaw : Measure (History Toy) := Measure.dirac counterPath

private instance : IsProbabilityMeasure toyLaw := by
  dsimp [toyLaw]
  infer_instance

private def toyKernel (n : ℕ) : Kernel (Past Toy n) (Future Toy n) :=
  Kernel.const _ (Measure.dirac ((split Toy n) counterPath).2)

private instance (n : ℕ) : IsMarkovKernel (toyKernel n) := by
  dsimp [toyKernel]
  infer_instance

private theorem toy_past_measurable (n : ℕ) : Measurable (past Toy n) :=
  Measurable.of_eval fun i => measurable_pi_apply (i : ℕ)

private theorem toy_predictive (n : ℕ) :
    toyLaw.map (split Toy n) = (toyLaw.map (past Toy n)) ⊗ₘ toyKernel n := by
  simp only [toyLaw, toyKernel, Measure.map_dirac' (split Toy n).measurable,
    Measure.map_dirac' (toy_past_measurable n), Measure.compProd_const,
    Measure.dirac_prod_dirac] <;> rfl

private theorem toy_marginals_ne :
    toyLaw.map (rejected.readout () (Toy, 0)) ≠ toyLaw.map (past Toy 0) := by
  have hread : rejected.readout () (Toy, 0) = fun _ => past Toy 0 basePath := rfl
  have hdiff : past Toy 0 basePath ≠ past Toy 0 counterPath := by
    intro heq
    have hh := congrArg (fun p : Past Toy 0 => (p ⟨0, by simp⟩).down) heq
    change (basePath 0).down = !(basePath 0).down at hh
    have hb : ∀ b : Bool, b ≠ !b := by decide
    exact hb _ hh
  intro heq
  rw [hread] at heq
  have hh := congrArg (fun μ : Measure (Past Toy 0) => μ {past Toy 0 counterPath}) heq
  have hdiff' : past Toy 0 counterPath ≠ past Toy 0 basePath := by
    intro h
    exact hdiff h.symm
  simpa [toyLaw, Measure.map_const, Measure.map_dirac' (toy_past_measurable 0),
    hdiff, hdiff'] using hh

private theorem rejected_change : ¬ changeArena.{u}.Law rejected := by
  intro h
  have hb := h Toy toyLaw toyLaw Measure.AbsolutelyContinuous.rfl toyKernel toy_predictive
  have hg := predictive_change_of_measure Toy toyLaw toyLaw
    Measure.AbsolutelyContinuous.rfl toyKernel toy_predictive
  exact toy_marginals_ne
    ((hb.2.2.2.2.2.2 0).2.2.2.2.2.1.trans
      (hg.2.2.2.2.2.2 0).2.2.2.2.2.1.symm)

private theorem rejected_merging : ¬ mergingArena.{u}.Law rejected := by
  intro h
  obtain ⟨eta, hmarkov, hsplit, _⟩ :=
    h Toy toyLaw toyLaw Measure.AbsolutelyContinuous.rfl toyKernel toy_predictive
  letI : IsMarkovKernel (eta 0) := hmarkov 0
  have heq := congrArg Measure.fst (hsplit 0)
  rw [Measure.fst_compProd] at heq
  have hfst : (toyLaw.map (split Toy 0)).fst = toyLaw.map (past Toy 0) := by
    change (toyLaw.map (split Toy 0)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (split Toy 0).measurable] <;> rfl
  rw [hfst] at heq
  exact toy_marginals_ne heq.symm

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro _
  refine ⟨(Toy, 0), (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  intro heq
  have hh := congrArg (fun p : Past Toy 0 => (p ⟨0, by simp⟩).down) heq
  cases hh

def changeFamily : Registration changeArena.{u}
    (type_of% (@predictive_change_of_measure.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@predictive_change_of_measure.{u}, rejected, rejected_change⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_change⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def mergingFamily : Registration mergingArena.{u}
    (type_of% (@blackwell_dubins_predictive_merging.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@blackwell_dubins_predictive_merging.{u}, rejected, rejected_merging⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_merging⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def changeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@predictive_change_of_measure.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins.changeUnit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins.changeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨changeArena⟩
  objectArena := .source ⟨changeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source changeArena ⟨changeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p ω i => ω i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins
    definition := none
    coordinates := #[0, 10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","arg","arg","arg","arg","arg","body",
        "arg","arg","arg","arg","arg","fn","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def mergingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@blackwell_dubins_predictive_merging.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins.mergingUnit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins.mergingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨mergingArena⟩
  objectArena := .source ⟨mergingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mergingArena ⟨mergingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p ω i => ω i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins
    definition := none
    coordinates := #[0, 11]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","body","arg","fn","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging.BlackwellDubins
