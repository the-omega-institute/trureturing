import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.QuadraticPrimeCrossPeriod
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset
open _root_.D5.S3.CharacterSums.QuadraticPrimeCrossPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.QuadraticPrimeCrossPeriod

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℕ → ℕ → ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ p => corr p) (fun e => nomatch e)

def constantOne : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (p r A L : ℕ),
    (0 ≤ corr p p A L ∧ corr p p A L ≤ (L : ℤ)) ∧
    (p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      V.readout () () p r A (8*(p*r)) = 0 ∧ |corr p r A L| ≤ (L % (8*(p*r)) : ℕ))

private theorem constant_fails : ¬ arena.Law constantOne := by
  intro h
  have bad := ((h 3 5 0 0).2 (by decide) (by decide) (by decide) (by decide) (by decide)).1
  exact (by decide : (1 : ℤ) ≠ 0) bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, 3, ?_⟩
  change corr 1 ≠ corr 3
  intro he
  have h := congrFun (congrFun (congrFun he 1) 3) 1
  have hz : jacobiSym 3 3 = 0 := jacobiSym.eq_zero_iff.2 (by decide)
  norm_num [corr, weight, hz, jacobiSym.one_left] at h

def family : Registration arena (type_of% @quadratic_prime_cross_period) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quadratic_prime_cross_period, constantOne, constant_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantOne constant_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quadratic_prime_cross_period) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.QuadraticPrimeCrossPeriod.quadratic_prime_cross_period
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.QuadraticPrimeCrossPeriod "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ p => corr p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.QuadraticPrimeCrossPeriod
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.QuadraticPrimeCrossPeriod
