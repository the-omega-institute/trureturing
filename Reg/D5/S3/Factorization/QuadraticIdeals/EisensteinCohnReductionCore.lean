import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore

set_option maxHeartbeats 800000
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore

@[reducible] def signature : Signature where
  Params := ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2 + 3) (fun a => nomatch a)

def zeroFamily : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (x y : ℤ) (e : ℕ), 2 ≤ x → 2 ≤ e →
    R.readout () e x ≠ y ^ e

theorem zeroFamily_fails : ¬ arena.Law zeroFamily := by
  intro h
  exact h 2 0 2 (by norm_num) (by norm_num) rfl

theorem actual_dependence : actual.readout () 2 2 ≠ actual.readout () 2 3 := by
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨int_sq_add_three_not_pow, zeroFamily, zeroFamily_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, zeroFamily_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨2, 2, 3, actual_dependence⟩

noncomputable def audit_main :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@int_sq_add_three_not_pow)
      (type_of% (realize signature (fun _ _ x => x ^ 2 + 3) (fun a => nomatch a)))
      (Type) (Unit) := {
  unitName := `EisensteinCohnReductionMain,
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => x ^ 2 + 3) (fun a => nomatch a)),
  variation := .absent, sensitivity := .absent,
  partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore,
    definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.norm_unit_oneAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := Unit
  State p := EisensteinOrderˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ u => (u : EisensteinOrder)) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : EisensteinOrderˣ),
    QuadraticAlgebra.norm (r.readout () () u) = 1
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h 1
  norm_num [bad, realize, Polynomial.coeff_one] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, -1, ?_⟩
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  simp only [actual, realize, Units.val_neg, Units.val_one, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] at hr
  omega
def evidence : Registration arena (∀ (u : EisensteinOrderˣ),
    QuadraticAlgebra.norm (u : EisensteinOrder) = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.norm_unit_one, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.norm_unit_one) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.norm_unit_oneAudit.unit
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.norm_unit_oneAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => (u : EisensteinOrder)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.norm_unit_oneAudit

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.unit_modTwoAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := Unit
  State p := {u : EisensteinOrderˣ // modTwo u = 1}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ u => (u.val : EisensteinOrder)) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => QuadraticAlgebra.omega) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : EisensteinOrderˣ) (hu : modTwo u = 1),
    (r.readout () () ⟨u, hu⟩).im = 0
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := h 1 (by change modTwo (1 : EisensteinOrder) = 1; exact map_one _)
  norm_num [bad, realize, QuadraticAlgebra.omega] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⟨1, by change modTwo (1 : EisensteinOrder) = 1; exact map_one _⟩,
    ⟨-1, ?_⟩, ?_⟩
  · change modTwo (-1 : EisensteinOrder) = 1
    rw [map_neg, map_one]
    decide
  · intro h
    have hr := congrArg QuadraticAlgebra.re h
    simp only [actual, realize, Units.val_neg, Units.val_one, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one] at hr
    omega
def evidence : Registration arena (∀ (u : EisensteinOrderˣ) (hu : modTwo u = 1),
    (u : EisensteinOrder).im = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.unit_modTwo, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.unit_modTwo) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.unit_modTwoAudit.unit
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.unit_modTwoAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => (u.val : EisensteinOrder)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore.unit_modTwoAudit
