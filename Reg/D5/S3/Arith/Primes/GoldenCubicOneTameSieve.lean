import D5.S3.Arith.Primes.GoldenCubicOneTameSieve
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicOneTameSieve

open _root_.D5.S3.Arith.Primes.GoldenCubicOneTameSieve
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ZMod 3)

def actual : Realization signature :=
  realize signature (fun _ _ n => nativeDigit 2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (R.readout () () n = if n%2=0 then 1 else 2) ∧
    ∀ P : ℕ, Compatible P n → FiveNoncubes P

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 0).1
  change (0 : ZMod 3) = 1 at bad
  exact (by decide +kernel : (0 : ZMod 3) ≠ 1) bad

private theorem actual_dependence :
    actual.readout () () 0 ≠ actual.readout () () 1 := by
  change nativeDigit 2 0 ≠ nativeDigit 2 1
  rw [(marked_one_tame_sieve 0).1, (marked_one_tame_sieve 1).1]
  decide +kernel

def family : Registration arena (type_of% @marked_one_tame_sieve) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨marked_one_tame_sieve, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@marked_one_tame_sieve) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicOneTameSieve.marked_one_tame_sieve.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicOneTameSieve.family
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
    owner := `D5.S3.Arith.Primes.GoldenCubicOneTameSieve
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Primes.GoldenCubicOneTameSieve
