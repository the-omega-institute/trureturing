import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ComplexOrder ENNReal
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness

structure HilbertInput where
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]

attribute [instance] HilbertInput.normed HilbertInput.inner HilbertInput.complete

abbrev signature : Signature where
  Params := HilbertInput.{u}
  State p := Set (TraceClass p.H)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (TraceClass p.H)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ S => S) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => Set.univ) (fun a => nomatch a)

def compactLaw (R : Realization signature.{u}) : Prop :=
  ∀ (p : HilbertInput.{u}) (T : Reference p.H) (M : ℝ), 0 ≤ M →
    IsCompact (R.readout () p (energySublevel T M))

abbrev compactArena : Arena where
  signature := signature.{u}
  Law := compactLaw

theorem actual_compact : compactArena.{u}.Law actual := by
  intro p T M hM
  exact isCompact_energySublevel T M hM

private def testInput : HilbertInput.{u} := ⟨EuclideanSpace ℂ (ULift.{u} Unit)⟩

private instance : Nontrivial (TraceClass testInput.{u}.H) := by
  haveI : FiniteDimensional ℂ testInput.{u}.H := inferInstanceAs (FiniteDimensional ℂ (EuclideanSpace ℂ (ULift.{u} Unit)))
  refine ⟨⟨TraceClass.ofOperator 1 (isTraceClass_of_finiteDimensional _), 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun x : TraceClass testInput.{u}.H => x.1) h
  haveI : Nontrivial testInput.{u}.H :=
    inferInstanceAs (Nontrivial (EuclideanSpace ℂ (ULift.{u} Unit)))
  exact (show (1 : testInput.{u}.H →L[ℂ] testInput.{u}.H) ≠ 0 from one_ne_zero) hh

theorem rejected_compact : ¬ compactArena.{u}.Law rejected := by
  intro h
  let T : Reference testInput.{u}.H := ⟨0, le_rfl, zero_le_one⟩
  have hc : IsCompact (Set.univ : Set (TraceClass testInput.{u}.H)) := h testInput.{u} T 0 le_rfl
  exact NormedSpace.unbounded_univ ℂ (TraceClass testInput.{u}.H) hc.isBounded

def compactFamily : Registration compactArena.{u}
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : Reference H) (M : ℝ), 0 ≤ M → IsCompact (energySublevel T M)) where
  actual := realize signature (fun _ _ S => S) (fun a => nomatch a)
  bridge := by
    constructor
    · intro h p; exact h
    · intro h H _ _ _; exact h ⟨H⟩
  variation := ⟨actual_compact, rejected, rejected_compact⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_compact⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a; exact nomatch a
  dependence := by
    intro i
    refine ⟨testInput.{u}, ∅, Set.univ, ?_⟩
    exact Set.empty_ne_univ

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.isCompact_energySublevel.{u})
    (type_of% (realize signature.{u} (fun _ _ S => S) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness.compactUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness.compactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨compactArena.{u}⟩
  objectArena := .source ⟨compactArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compactArena.{u} ⟨compactFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ S => S) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compactFamily


def boundedLaw (R : Realization signature.{u}) : Prop :=
  ∀ (p : HilbertInput.{u}) (T : Reference p.H) (M : ℝ), 0 ≤ M → TotallyBounded (R.readout () p (energySublevel T M))
abbrev boundedArena : Arena where
  signature := signature.{u}
  Law := boundedLaw

theorem actual_bounded : boundedArena.{u}.Law actual := by
  intro p T M hM
  exact totallyBounded_energySublevel T M hM

theorem rejected_bounded : ¬ boundedArena.{u}.Law rejected := by
  intro h
  let T : Reference testInput.{u}.H := ⟨0, le_rfl, zero_le_one⟩
  have hc : TotallyBounded (Set.univ : Set (TraceClass testInput.{u}.H)) := h testInput.{u} T 0 le_rfl
  exact NormedSpace.unbounded_univ ℂ (TraceClass testInput.{u}.H) hc.isBounded

def boundedFamily : Registration boundedArena.{u}
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : Reference H) (M : ℝ), 0 ≤ M → TotallyBounded (energySublevel T M)) where
  actual := realize signature (fun _ _ S => S) (fun a => nomatch a)
  bridge := by
    constructor
    · intro h p; exact h
    · intro h H _ _ _; exact h ⟨H⟩
  variation := ⟨actual_bounded, rejected, rejected_bounded⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bounded⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a; exact nomatch a
  dependence := by
    intro i
    exact ⟨testInput.{u}, ∅, Set.univ, Set.empty_ne_univ⟩

def boundedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.totallyBounded_energySublevel.{u})
    (type_of% (realize signature.{u} (fun _ _ S => S) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness.boundedUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness.boundedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundedArena.{u}⟩
  objectArena := .source ⟨boundedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundedArena.{u} ⟨boundedFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ S => S) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def punctured := realize signature.{u} (fun _ _ _ => ({0} : Set _)ᶜ) (fun a => nomatch a)

def closedLaw (R : Realization signature.{u}) : Prop :=
  ∀ (p : HilbertInput.{u}) (T : Reference p.H) (M : ℝ), IsClosed (R.readout () p (energySublevel T M))
abbrev closedArena : Arena where
  signature := signature.{u}
  Law := closedLaw

theorem actual_closed : closedArena.{u}.Law actual := by
  intro p T M
  exact isClosed_energySublevel T M

theorem rejected_closed : ¬ closedArena.{u}.Law punctured := by
  intro h
  let T : Reference testInput.{u}.H := ⟨0, le_rfl, zero_le_one⟩
  haveI := Module.punctured_nhds_neBot ℂ (TraceClass testInput.{u}.H) (0 : TraceClass testInput.{u}.H)
  have hc : IsClosed (({0} : Set (TraceClass testInput.{u}.H))ᶜ) := h testInput.{u} T 0
  exact not_isOpen_singleton (0 : TraceClass testInput.{u}.H) (by simpa only [compl_compl] using hc.isOpen_compl)

def closedFamily : Registration closedArena.{u}
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : Reference H) (M : ℝ), IsClosed (energySublevel T M)) where
  actual := realize signature (fun _ _ S => S) (fun a => nomatch a)
  bridge := by
    constructor
    · intro h p; exact h
    · intro h H _ _ _; exact h ⟨H⟩
  variation := ⟨actual_closed, punctured, rejected_closed⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨punctured, ?_, rfl, rejected_closed⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a; exact nomatch a
  dependence := by
    intro i
    exact ⟨testInput.{u}, ∅, Set.univ, Set.empty_ne_univ⟩

def closedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.isClosed_energySublevel.{u})
    (type_of% (realize signature.{u} (fun _ _ S => S) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness.closedUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness.closedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨closedArena.{u}⟩
  objectArena := .source ⟨closedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closedArena.{u} ⟨closedFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ S => S) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]



abbrev stateSignature : Signature where
  Params := HilbertInput.{u}
  State p := TraceClass p.H → ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := TraceClass p.H → ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def stateActual := realize stateSignature.{u} (fun _ _ f => f) (fun a => nomatch a)

def stateLaw (R : Realization stateSignature.{u}) : Prop :=
  ∀ (p : HilbertInput.{u}) (T : Reference p.H),
    LowerSemicontinuousOn (R.readout () p (spectralEnergy T))
      {rho : TraceClass p.H | 0 ≤ rho.1}

theorem state_actual : stateLaw stateActual.{u} := by
  intro p T
  exact lowerSemicontinuousOn_spectralEnergy_state T

theorem state_bridge :
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : Reference H), LowerSemicontinuousOn (spectralEnergy T)
        {rho : TraceClass H | 0 ≤ rho.1}) ↔ stateLaw stateActual.{u} := by
  constructor
  · intro h p; exact h
  · intro h H _ _ _; exact h ⟨H⟩

end Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness
