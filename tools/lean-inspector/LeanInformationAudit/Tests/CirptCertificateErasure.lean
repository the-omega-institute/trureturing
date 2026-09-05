import D5.S3.ConceptDynamics.CIRPT.SemanticIntegrity
import LeanInformationAudit.Tests.SealSuccess

/-! AC-CIRPT-011 / IE-C016: proof certificates add no object distinction. -/

open D5.S3.ConceptDynamics.CIRPT

namespace LeanInformationAudit.Tests.CirptCertificateErasure

abbrev Certificate : Prop :=
  LeanInformationAudit.Tests.SealSuccess.arena.__information_catalog.LowersEscape
    (0 : Fin 2)

def certificateReadout (_certificate : Certificate) (_state : Bool) : Unit := ()

def certificateObserver : PackedObserver Bool where
  Output := Unit
  outputDecidableEq := inferInstance
  observe := certificateReadout
    LeanInformationAudit.Tests.SealSuccess.fstTheorem.__lowers_escape

theorem certificateObserver_is_constant (state : Bool) :
    certificateObserver.observe state = () := by
  rfl

example (x y : Bool) :
    ((certificateObserver.toPrimitiveAtom .anchor).kernel.relation x y) := by
  exact constant_packed_observer_has_universal_kernel
    .anchor certificateObserver ()
    certificateObserver_is_constant x y

def objectBundle : PrimitiveBundle Bool :=
  constantCutBundle (X := Bool) (fun _ : Fin 1 => true)

example (x y : Bool) :
    (bundleWithAtom objectBundle
      (certificateObserver.toPrimitiveAtom .anchor)).agrees x y <->
    objectBundle.agrees x y := by
  exact universal_kernel_atom_does_not_change_agrees
    objectBundle (certificateObserver.toPrimitiveAtom .anchor)
    (constant_packed_observer_has_universal_kernel
      .anchor certificateObserver ()
      certificateObserver_is_constant) x y

/-- error: IE-C011 GeneratedCertificateRegistered:
LeanInformationAudit.Tests.SealSuccess.fstTheorem.__lowers_escape -/
#guard_msgs (error) in
register_information_theorem
  LeanInformationAudit.Tests.SealSuccess.fstTheorem.__lowers_escape
  in LeanInformationAudit.Tests.SealSuccess.arena
  primitives LeanInformationAudit.Tests.SealSuccess.fstRealization.toPrimitiveBundle
  realization LeanInformationAudit.Tests.SealSuccess.fstTheorem

end LeanInformationAudit.Tests.CirptCertificateErasure
