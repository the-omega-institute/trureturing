import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentTraceNorm
import Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical

/-! Source-bound dependence of the faithful trace-norm estimate on the marginal multiplier. -/

namespace Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentTraceNorm

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzTangentTraceNorm
open _root_.D5.S3.Quantum.Recovery.PetzTangentReciprocalGram
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open _root_.D5.S3.Divergence.LogDerivTrace (logDeriv)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentPhysical.FaithfulWitness
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ δ => parityMultiplier δ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (hZ : Z.PosDef)
    (_htrace : Z.trace.re = 1),
    let P := partialTraceRight Z
    let M := partialTraceRight H
    let p := (partialTraceRight_posDef Z hZ).isHermitian.eigenvalues
    traceNorm (H - partialTracePetz Z M) ^ 2 ≤ R.readout () () (2*Real.sqrt (p 0*p 1)) *
      ((Hᴴ * logDeriv Z H).trace.re - (Mᴴ * logDeriv P M).trace.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law reference direction reference_pos reference_trace
  dsimp only at h
  rw [direction_recovery, sub_zero] at h
  have hgram : directionᴴ * direction = 1 := by
    rw [show directionᴴ = direction by simp [direction, Matrix.diagonal_conjTranspose]]
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i.2 = 0 <;> simp [hi]
  have hnorm : traceNorm direction = 4 := by
    norm_num [_root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm,
      hgram, Matrix.trace_one, Fintype.card_prod]
  rw [hnorm] at h
  norm_num [rejected, realize] at h

def source_registration : Registration arena (type_of% @faithful_traceNorm_tangent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@faithful_traceNorm_tangent, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (1/4 : ℝ), ?_⟩
    change parityMultiplier 1 ≠ parityMultiplier (1/4)
    norm_num [parityMultiplier, max_def]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Recovery.PetzTangentTraceNorm.faithful_traceNorm_tangent)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentTraceNorm.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentTraceNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ δ => parityMultiplier δ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentTraceNorm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentTraceNorm
