import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion
import D5.S3.Arith.GoldenResource.GoldenCell5040Congruence
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion

open _root_.D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => ℕ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ p n => p ∣ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n p : ℕ} (_h5040 : 5040 ∣ n)
    (_hmod : Nat.ModEq n (3 ^ n) 2241) (_hp : p.Prime)
    (_hlo : 7 < p) (_hhi : p < 47), ¬ R.readout () p n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmod : Nat.ModEq 5040 (3 ^ 5040) 2241 :=
    _root_.D5.S3.Arith.GoldenResource.GoldenCell5040Congruence.goldenCell5040_modEq_2241
      5040 (by decide)
  exact h (n := 5040) (p := 11) (dvd_refl 5040) hmod
    (by decide) (by decide) (by decide) trivial

def family : Registration arena (type_of% (@modEq_2241_small_prime_not_dvd)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@modEq_2241_small_prime_not_dvd, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨11, 0, 1, ?_⟩
    change (11 ∣ 0) ≠ (11 ∣ 1)
    intro h
    have hbad : 11 ∣ 1 := Eq.mp h (dvd_zero 11)
    norm_num at hbad

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@modEq_2241_small_prime_not_dvd) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion.modEq_2241_small_prime_not_dvd.__information_unit
  realizationName := `Reg.D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion.family
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
    owner := `D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion
