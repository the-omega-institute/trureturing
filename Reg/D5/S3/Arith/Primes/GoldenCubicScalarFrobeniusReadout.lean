import D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.ULift
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout

open _root_.D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ ZMod ZMod

def actual : Realization signature :=
  realize signature (fun _ q x => numer x (probePower q)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

universe u
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [Field K] (q : ℕ) [CharP K q]
    (_hp : q.Prime) (_hgt : 3<q) (x : ZMod q) (δ : K) (_hδ : δ^2=-3)
    (_hB : block x≠0),
    let m := probePower q
    let z := rationalCardano q (ZMod.castHom (dvd_rfl : q∣q) K x) δ
    let w := if q%3=1 then omegaOf δ else (omegaOf δ)⁻¹
    (R.readout () q x = 0 ↔ z=1) ∧
    (numer x m = (block x)^m ↔ z=w) ∧
    (numer x m = -(block x)^m ↔ z=w⁻¹)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp : Nat.Prime 7 := by decide
  let _ : Fact (Nat.Prime 7) := ⟨hp⟩
  -- ULift ensures the concrete rejection remains valid in every universe.
  let δ : ULift.{u} (ZMod 7) := ULift.up 2
  have hδR : δ^2 = -3 := ULift.down_injective (by decide +kernel +revert)
  have hbad := (h (K := ULift.{u} (ZMod 7)) 7 hp (by decide) (1:ZMod 7) δ
    hδR (by decide +kernel +revert)).1.mp rfl
  -- The actual extension readout is two, not one.
  exact (by decide +kernel +revert :
    (rationalCardano 7 (ZMod.castHom (dvd_rfl : 7∣7) (ULift.{u} (ZMod 7)) (1:ZMod 7))
      δ).down ≠ 1) (congrArg ULift.down hbad)

private theorem actual_dependence :
    actual.readout () 7 (0:ZMod 7) ≠ actual.readout () 7 (1:ZMod 7) := by
  decide +kernel

def family : Registration arena.{u} (type_of% @prime_field_scalar_oriented_readout.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_field_scalar_oriented_readout.{u},rejected,rejected_law.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law.{u}
  dependence := fun _ => ⟨7,0,1,actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prime_field_scalar_oriented_readout.{u}) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout.prime_field_scalar_oriented_readout.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body",
        "body","body","fn","arg","fn","arg","fn","arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout
