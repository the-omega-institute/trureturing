import D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.ULift
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition
open _root_.D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p d => if p^d%3=1 then (p^d-1)/3 else (p^d+1)/3)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [CommRing K] [Nontrivial K]
    (p d : ℕ) [CharP K p] (_hp : p.Prime) (_hp3 : 3<p) (_hd : 0<d) (_h2 : IsUnit (2:K)),
    let m := R.readout () p d
    let q := p^d
    let split := q%3=1
    let z := (⟨(X:K[X]),1⟩ : QA K[X])^m
    let U := z.re
    let V := z.im
    let c : K := if split then -3 else 3
    0<m ∧ c*(m:K)=1 ∧
    (C c*V).Monic ∧ (C c*V).natDegree=m-1 ∧
    (U-V).Monic ∧ (U-V).natDegree=m ∧ (U+V).Monic ∧ (U+V).natDegree=m ∧
    (if split then (X^2+3)*(C c*V)*(U-V)*(U+V) else (C c*V)*(U-V)*(U+V)) =
        X^q-X

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let K := ULift.{u} (ZMod 5)
  have h23 : (2:K)*3=1 := ULift.down_injective (by decide +kernel : (2:ZMod 5)*3=1)
  have h32 : (3:K)*2=1 := ULift.down_injective (by decide +kernel : (3:ZMod 5)*2=1)
  have h2 : IsUnit (2:K) := ⟨⟨2,3,h23,h32⟩,rfl⟩
  have H := @h K inferInstance inferInstance 5 1 inferInstance
    (by decide) (by decide) (by decide) h2
  have hz := H.2.1
  change (3:K)*0=1 at hz
  exact zero_ne_one (by simpa only [mul_zero] using hz)

private theorem actual_dependence :
    actual.readout () 5 1 ≠ actual.readout () 5 2 := by decide +kernel

def family : Registration arena.{u} (type_of% @monic_oriented_polynomial_partition.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@monic_oriented_polynomial_partition.{u},rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := fun _ => ⟨5,1,2,actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@monic_oriented_polynomial_partition.{u}) (type_of% actual) Unit Unit where
  unitName :=
    `D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition.monic_oriented_polynomial_partition.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition.family
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
    owner := `D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition
