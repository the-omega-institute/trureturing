import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.Measures.AtomicMomentRepair
import Reg.Support.SingleDependentReadout

/-! Escape registration for the absolute correction budget. -/

open Set LeanInformationAudit
open _root_.D5.S3.Topology.Measures.AtomicMomentRepair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.Topology.Measures.AtomicMomentRepair

noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ cost budget => cost < budget) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have heq := congrFun h 1
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  have h11 : (1 : ℝ) < 1 := Eq.mp heq h01
  exact (lt_irrefl _) h11

abbrev repairArena : Arena where
  signature := signature
  Law R := ∀ {Atom E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ]
    (moment : Atom → E) (admissible : Set Atom) (basisNode : κ → admissible)
    (basis : Module.Basis κ ℝ E),
    (∀ j, basis j = moment (basisNode j)) →
    ∀ (oldMoment : ι → E) (weight : ι → ℝ),
    (∀ i, oldMoment i ∈ closure (moment '' admissible)) →
    ∀ {ε : ℝ}, 0 < ε →
    ∃ (node : ι → admissible) (correction : κ → ℝ),
      (∑ i, weight i • moment (node i)) + (∑ j, correction j • moment (basisNode j)) =
        (∑ i, weight i • oldMoment i) ∧ R.readout () () (∑ j, |correction j|) ε

private theorem repair_rejected : ¬ repairArena.Law rejected := by
  intro h
  let basis : Module.Basis (ULift Unit) ℝ (ULift Unit → ℝ) :=
    (Pi.basisFun ℝ (ULift Unit)).reindex (Equiv.ofUnique _ _)
  let moment : ULift Unit → (ULift Unit → ℝ) := fun _ => basis default
  have hApprox : ∀ _ : ULift Unit, basis default ∈ closure (moment '' univ) :=
    fun _ => subset_closure ⟨default, mem_univ _, rfl⟩
  obtain ⟨_, _, _, bad⟩ :=
    h (ι := ULift Unit) moment univ (fun _ => ⟨default, mem_univ _⟩) basis
      (fun i => congrArg basis (Unique.eq_default i))
      (fun _ => basis default) (fun _ => -1) hApprox (ε := 1) zero_lt_one
  exact bad

def repairFamily : Registration repairArena (type_of% @exists_exact_moment_repair) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_exact_moment_repair, rejected, repair_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    repairArena.Law actual rejected repair_rejected
  dependence := dependence

def repairAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_exact_moment_repair) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Topology.Measures.AtomicMomentRepair.exists_exact_moment_repair
    "__information_unit"
  realizationName := `Reg.D5.S3.Topology.Measures.AtomicMomentRepair.repairFamily
  realizationSource := none
  generated := false
  arena := .source ⟨repairArena⟩
  objectArena := .source ⟨repairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source repairArena ⟨repairFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.AtomicMomentRepair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Topology.Measures.AtomicMomentRepair
