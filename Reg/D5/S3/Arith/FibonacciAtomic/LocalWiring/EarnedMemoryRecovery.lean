import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery
import Reg.Support.DependentFamily

/-! Source-equivalent registration of the actual physical-incidence recovery route. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery
open AttainedPrefixAcquisition KnownSeedCurrentFibers PhysicalBirthClock
open OrderedBirthPrefix PublicRowSeedReadiness LawfulSourceReadiness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Promise
  State _ := List Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Bundle
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p xs => recoverIncidence p xs) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (P : Promise) (s : OutputStream) (n : Nat)
    (code : Code) (_hn : 2 ≤ n) (_hm : P.target ≤ matureSize n)
    (_hc : reify P (prefixBits (birthOf s) P.target) = some code)
    (_he : code.eval = s),
    F.readout () P (acquired .incidence n s) =
      some (direct s ⟨prefixBits (birthOf s) P.target, code, n, clockSum n⟩)

private def zeroRow : Promise := .row 0 Fin.elim0
private def zeroCode : Code := .row 0 Fin.elim0 (seedFromPrefix [])
private def zeroStream : OutputStream := fun _ => false

private theorem zeroCode_value : zeroCode.eval = zeroStream :=
  row_zero_unique _ _

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h zeroRow zeroStream 2 zeroCode (by decide) (by decide) rfl zeroCode_value
  change none = some _ at hb
  cases hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨zeroRow, acquired .incidence 2 zeroStream, acquired .incidence 3 zeroStream, ?_⟩
  change recoverIncidence zeroRow (acquired .incidence 2 zeroStream) ≠
    recoverIncidence zeroRow (acquired .incidence 3 zeroStream)
  intro hh
  rw [recover_incidence_exact zeroRow zeroStream 2 zeroCode (by decide) (by decide)
      rfl zeroCode_value,
    recover_incidence_exact zeroRow zeroStream 3 zeroCode (by decide) (by decide)
      rfl zeroCode_value] at hh
  have hb := congrArg (fun b : Bundle => b.memory.cut) (Option.some.inj hh)
  change (2 : Nat) = 3 at hb
  omega

def family : Registration arena (type_of% recover_incidence_exact) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨recover_incidence_exact, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    recover_incidence_exact (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.EarnedMemoryRecovery
