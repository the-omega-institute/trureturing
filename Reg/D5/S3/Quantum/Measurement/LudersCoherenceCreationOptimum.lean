import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the sharp coherence-creation bound. -/

namespace Reg.D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum

open _root_.D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum
open _root_.D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation (l1Coherence)
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe real comparison at the lower endpoint of the gain bound. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ lower upper => lower < upper) (fun e => nomatch e)

/-- Retain attainment, density, outcome count and both equality criteria. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (ρ : Matrix (Fin 2) (Fin 2) ℂ) (_hρ : IsDensity ρ)
    (n : ℕ) (_hn : 2 ≤ n),
    IsGreatest {c | ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      IsPOVM e ∧ c = l1Coherence (luders e ρ)} ((l1Coherence ρ + blochNorm ρ) / 2) ∧
    ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 0 ↔ ρ 0 0 = ρ 1 1) ∧
    r.readout () () ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ) (1 / 2) ∧
    ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 1 / 2 ↔
      ρ = Matrix.diagonal ![1, 0] ∨ ρ = Matrix.diagonal ![0, 1])

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hρ : IsDensity (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
    constructor
    · apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      fin_cases i <;> norm_num
    · norm_num [Matrix.trace_fin_two]
  have hbad := (h _ hρ 2 (by norm_num)).2.2.1
  have heq := ((result _ hρ 2 (by norm_num)).2.2.2).mpr (Or.inl rfl)
  change (l1Coherence _ + blochNorm _) / 2 - l1Coherence _ < 1 / 2 at hbad
  rw [heq] at hbad
  exact (lt_irrefl _) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (fun upper : ℝ => 0 ≤ upper) = (fun upper : ℝ => 1 ≤ upper) at h
  have hfalse : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le_of_gt zero_lt_one) hfalse

def source_registration : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ lower upper => lower ≤ upper) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum
