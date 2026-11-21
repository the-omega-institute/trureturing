import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzSupportedLogisticBound
import Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the physical ordinary Petz trace bound. -/

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
open _root_.D5.S3.Quantum.Recovery.PetzSupportedLogisticBound
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped ComplexOrder MatrixOrder

open private unitModel from Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip

namespace Reg.D5.S3.Quantum.Recovery.PetzSupportedLogisticBound

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

open _root_.Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.TraceError (actual)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x + 1 ≤ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    let D := M.data
    R.readout () () (traceNorm (D.R - recoveredState D) ^ 2)
      ((4 * (↑(1 + D.T.rank * D.Q.rank) : ℝ)) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)))

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let M := unitModel.{u,u}
  have bad := law M
  change traceNorm (M.data.R - recoveredState M.data) ^ 2 + 1 ≤
    (4 * (↑(1 + M.data.T.rank * M.data.Q.rank) : ℝ)) * (_ - _) at bad
  simp only [finiteTraceLogRelativeEntropy_self, sub_zero, mul_zero] at bad
  linarith only [bad, sq_nonneg (traceNorm (M.data.R - recoveredState M.data))]

def family : Registration arena.{u} (type_of% @ordinary_petz_traceNorm_sq_le_entropy_loss.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_petz_traceNorm_sq_le_entropy_loss.{u}, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence :=
    _root_.Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.TraceError.family.{u}.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_petz_traceNorm_sq_le_entropy_loss.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedLogisticBound.ordinary_petz_traceNorm_sq_le_entropy_loss.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedLogisticBound.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedLogisticBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzSupportedLogisticBound
