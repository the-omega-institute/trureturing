import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization
import Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts of the exact logistic phase cost and ordinary Petz trace bound. -/

set_option autoImplicit false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open _root_.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram (recoveredState)
open _root_.D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open PetzExponentialBoundaryEvaluation (petzWeight)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)

open private completed exists_retainedFirst_stinespring from
  D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

open private unitModel unitChannel from Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip

namespace Reg.D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

namespace PhaseDiscrepancy

open _root_.Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.UpperDeficit (actual rejected)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b e : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e] [DecidableEq e]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (W : Matrix (b × e) a ℂ) (_hW : Wᴴ * W = 1)
    (_hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = act Φ X)
    (assign : ℝ → ℝ),
    R.readout () ()
      (∫ t : ℝ, petzWeight t * ‖completed M.data W t - quantizedCompleted M.data W assign t‖ ^ 2)
      (phaseCost M.data assign)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let M := unitModel.{u,u}
  obtain ⟨W, hW, hAction⟩ := exists_retainedFirst_stinespring
    (unitChannel (ULift.{u} Unit) (ULift.{u} Unit))
  have he := exact_phase_discrepancy M W hW hAction id
  have hb := law M W hW hAction id
  change (∫ t : ℝ, petzWeight t *
    ‖completed M.data W t - quantizedCompleted M.data W id t‖ ^ 2) + 1 =
    phaseCost M.data id at hb
  linarith only [he, hb]

def family : Registration arena.{u} (type_of% @exact_phase_discrepancy.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_phase_discrepancy.{u}, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence :=
    _root_.Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.UpperDeficit.family.{u}.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_phase_discrepancy.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization.exact_phase_discrepancy.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization.PhaseDiscrepancy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PhaseDiscrepancy

namespace TraceBound

open _root_.Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.TraceError (actual rejected)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (assign : ℝ → ℝ)
    (centres : Finset ℝ) (_hc : UsesCentres M.data assign centres),
    let D := M.data
    let Δ := finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
    R.readout () () (traceNorm (D.R - recoveredState D) ^ 2)
      (4 * ((centres.card : ℝ) + 1) * (Real.sqrt Δ + Real.sqrt (phaseCost D assign)) ^ 2)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let M := unitModel.{u,u}
  have hc : UsesCentres M.data (fun _ => 0) {0} := fun _ _ => Finset.mem_singleton_self _
  exact (not_lt_of_ge (ordinary_petz_traceNorm_sq_le_quantized_phase_cost M _ _ hc))
    (law M _ _ hc)

def family : Registration arena.{u}
    (type_of% @ordinary_petz_traceNorm_sq_le_quantized_phase_cost.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_petz_traceNorm_sq_le_quantized_phase_cost.{u}, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence :=
    _root_.Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.TraceError.family.{u}.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_petz_traceNorm_sq_le_quantized_phase_cost.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization.ordinary_petz_traceNorm_sq_le_quantized_phase_cost.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization.TraceBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TraceBound

end Reg.D5.S3.Quantum.Recovery.PetzModularFrequencyQuantization
