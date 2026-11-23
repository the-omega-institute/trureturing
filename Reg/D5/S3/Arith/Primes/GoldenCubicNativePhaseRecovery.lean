import D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
open _root_.D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Option ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ j => decode5 (nativeWord5 j)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => some 24) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ) (_hj : 1≤j),
    let phase := R.readout () () j
    phase = some (if j=1 then 24 else j%24) ∧
    Separates {0,1,9,10,13} ∧ SignedSeparates orientationBlindSet ∧
    ∀ S : Finset (Fin 21), Separates S → 5≤S.card ∧ (9:Fin 21)∈S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h 3 (by decide)).1
  change some 24 = (some 3 : Option Nat) at H
  exact (by decide : (24:Nat)≠3) (Option.some.inj H)

private theorem actual_dependence : actual.readout () () 1 ≠ actual.readout () () 3 := by
  change decode5 (nativeWord5 1) ≠ decode5 (nativeWord5 3)
  rw [(native_phase_recovery 1 (by decide)).1,(native_phase_recovery 3 (by decide)).1]
  decide +kernel

def family : Registration arena (type_of% @native_phase_recovery) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_phase_recovery,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 1, 3, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@native_phase_recovery) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery.native_phase_recovery.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Arith.Primes.GoldenCubicNativePhaseRecovery
