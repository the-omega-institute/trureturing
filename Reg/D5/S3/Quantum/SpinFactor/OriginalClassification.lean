import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.SpinFactor.OriginalClassification

/-!
Source-only registration attempt for the complete original endpoint.

The source theorem has an exact original telescope, but this phase has no
compiler or audit authority.  In particular, no closed source selector,
template enrollment, compiled witness, or declared_validated registration is
claimed.  The following arena records the target and leaves the required
family factory as an explicit later obligation rather than manufacturing an
audit result.
-/

noncomputable section

open _root_.D5.S3.Quantum.SpinFactor.OriginalDContract
open _root_.D5.S3.Quantum.SpinFactor.OriginalClassification
open _root_.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.SpinFactor.OriginalClassification

abbrev signature : Signature where
  Params := Unit
  State _ := E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a b => crossD .plus a b) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : E → E → E),
    (∀ a b, D a b = R.readout () a b) →
      _root_.D5.S3.Quantum.SpinFactor.OriginalClassification.complete_classification D

abbrev consequencesArena : Arena where
  signature := signature
  Law R := ∀ (D : E → E → E) (_ : P2 D) (_ : PB D),
    (∀ a b, D a b = R.readout () a b) →
      ∃ ε : Orientation,
        (ε = .plus ∨ ε = .minus) ∧
        (∀ a b, D a b = crossD ε a b) ∧
        (Consequences D ∧ MatrixInterfaces (orientationBool ε) D)

/- A later compiler-owned factory must supply the four-slot registration.  This
   source deliberately contains no fabricated proof of the rejected law, no
   guessed selector and no validation claim. -/

end Reg.D5.S3.Quantum.SpinFactor.OriginalClassification
