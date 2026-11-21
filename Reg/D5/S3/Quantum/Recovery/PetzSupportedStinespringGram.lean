import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
import Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
import Reg.Support.SingleDependentReadout

/-! Register the upper-deficit equality and physical trace inequality. -/

set_option autoImplicit false

noncomputable section

universe u

open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open _root_.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open _root_.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.Frobenius

open private sourceAmplitude completed physicalGram rotatedGram
  exists_retainedFirst_stinespring from D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
open private unitModel unitChannel from Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip

namespace Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

namespace UpperDeficit

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x + 1 = y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b e : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e] [DecidableEq e]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (W : Matrix (b × e) a ℂ) (_hW : Wᴴ * W = 1)
    (_hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X),
    let D := M.data
    let A : Matrix D.J (D.I ⊕ (b × e)) ℂ := sourceAmplitude D
    let B := completed D W
    (∀ t, R.readout () () (‖A - B t‖ ^ 2) (deficit D (1 / 2) t) ∧
      B t * (B t)ᴴ = rotatedGram D t) ∧
      physicalGram D A = D.R ∧ physicalGram D (B 0) = recoveredState D

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let M := unitModel.{u,u}
  obtain ⟨W, hW, hAction⟩ := exists_retainedFirst_stinespring
    (unitChannel (ULift.{u} Unit) (ULift.{u} Unit))
  have h := ((supported_stinespring_gram M W hW hAction).1 0).1
  have bad := ((law M W hW hAction).1 0).1
  change ‖sourceAmplitude M.data - completed M.data W 0‖ ^ 2 =
    deficit M.data (1 / 2) 0 at h
  change ‖sourceAmplitude M.data - completed M.data W 0‖ ^ 2 + 1 =
    deficit M.data (1 / 2) 0 at bad
  linarith only [h, bad]

def family : Registration arena.{u} (type_of% @supported_stinespring_gram.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@supported_stinespring_gram.{u}, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro same
    have h := congrFun same 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@supported_stinespring_gram.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.supported_stinespring_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.UpperDeficit.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UpperDeficit

namespace TraceError

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => y < x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    let D := M.data
    R.readout () () (traceNorm (D.R - recoveredState D) ^ 2)
      ((8 * (↑(1 + D.T.rank * D.Q.rank) : ℝ)) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)))

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let M := unitModel.{u,u}
  exact (not_lt_of_ge (ordinary_petz_traceNorm_sq_le_entropy_loss M)) (law M)

def family : Registration arena.{u} (type_of% @ordinary_petz_traceNorm_sq_le_entropy_loss.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_petz_traceNorm_sq_le_entropy_loss.{u}, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro same
    have h := congrFun same 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_petz_traceNorm_sq_le_entropy_loss.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.ordinary_petz_traceNorm_sq_le_entropy_loss.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram.TraceError.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
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

end TraceError

end Reg.D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
