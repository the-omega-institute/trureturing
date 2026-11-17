import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
import Reg.Support.DependentFamily

/-! # Full-telescope source-family preparation for the two-bit zero theorems

This file is prepared source, not compiled registration or binding evidence.
The mathematical source is unchanged.  The three laws below retain its entire
telescope and conclusions.  Only the actual source-vector occurrence is varied.

`Reg.Support.DependentFamily.enrollment_1` supplies the existing typed
`Contract.TemplateEnrollment` of `DependentFamily.realize`; no new template or
enrollment is invented here.  The final three functions are typed contract
constructors, deliberately parameterized by a `Contract.SourceSelection`.
They are not closed audit declarations.  A later native writer must extract
the exact raw paths from the compiled original declarations and materialize
closed registrations before inspection can establish any binding.

The count law retains `Nat.gcd` and `Even`.  Issue #11434 describes a possible
source-operand closure boundary in other invocations, not a diagnostic obtained
for this uncompiled file.  No accepted certificate or audit state is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ZeroSumSubsets
open _root_.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets
open scoped BigOperators

/-- The parameter is the number of physical labels; the state is the exponent.
The output is the complete integer source vector, not a primitive Boolean or
the truth of the target theorem.  States are all naturals; the original law
itself retains exactly its three domain hypotheses. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ r := Fin r → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r a => actualSource r (1 + 2 ^ a))
    (fun e => nomatch e)

/-- One intervention changes the whole family to the constant-one vector. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (1 : ℤ)) (fun e => nomatch e)

abbrev classificationArena : Arena where
  signature := signature
  Law R := ∀ (r a : ℕ) (_hr : 2 ≤ r) (_ha : 0 < a) (_har : a < r)
    (A : Finset (Fin r)),
    (∑ i ∈ A, R.readout () r a i) = 0 ↔
      A = ∅ ∨ A = Finset.univ ∨
        A.image ((finRotate r : Equiv.Perm (Fin r)) ^ a) = Aᶜ

abbrev divisibilityArena : Arena where
  signature := signature
  Law R := ∀ (r a : ℕ) (_hr : 2 ≤ r) (_ha : 0 < a) (_har : a < r)
    (A : Finset (Fin r)),
    (∑ i ∈ A, R.readout () r a i) = 0 ↔
      (2 ^ r - 1) ∣ (1 + 2 ^ a) * mask A

abbrev countArena : Arena where
  signature := signature
  Law R := ∀ (r a : ℕ) (_hr : 2 ≤ r) (_ha : 0 < a) (_har : a < r),
    (Finset.univ.filter (fun A : Finset (Fin r) =>
      (∑ i ∈ A, R.readout () r a i) = 0)).card =
      if Even (r / Nat.gcd a r) then 2 ^ (Nat.gcd a r) + 2 else 2

private theorem rejected_classification : ¬ classificationArena.Law rejected := by
  intro h
  have hz := (h 2 1 (by decide) (by decide) (by decide)
    (Finset.univ : Finset (Fin 2))).mpr (Or.inr (Or.inl rfl))
  norm_num [rejected, realize] at hz

private theorem rejected_divisibility : ¬ divisibilityArena.Law rejected := by
  intro h
  have hd : (2 ^ 2 - 1 : ℕ) ∣ (1 + 2 ^ 1) *
      mask (Finset.univ : Finset (Fin 2)) := by
    norm_num [mask, Fin.sum_univ_succ]
  have hz := (h 2 1 (by decide) (by decide) (by decide)
    (Finset.univ : Finset (Fin 2))).mpr hd
  norm_num [rejected, realize] at hz

private theorem rejected_count : ¬ countArena.Law rejected := by
  intro h
  have hf : (Finset.univ.filter (fun A : Finset (Fin 2) =>
      (∑ i ∈ A, rejected.readout () 2 1 i) = 0)) = {∅} := by
    ext A
    simp [rejected, realize]
  have hh := h 2 1 (by decide) (by decide) (by decide)
  rw [hf] at hh
  norm_num at hh

/-- This uses two valid exponents at r=3.  At label zero the actual centered
source values are 3 and -2, respectively.  It does not require nondegeneracy
in every fiber: the permitted r=2,a=1 source is identically zero. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 1, 2, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def classification_registration : Registration classificationArena
    (type_of% (@actual_zero_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_iff, rejected, rejected_classification⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_classification⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def divisibility_registration : Registration divisibilityArena
    (type_of% (@actual_zero_iff_dvd)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_iff_dvd, rejected, rejected_divisibility⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_divisibility⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def count_registration : Registration countArena
    (type_of% (@actual_zero_subsets_card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_zero_subsets_card, rejected, rejected_count⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_count⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The three registrations below are closed literals.  Their source paths were
obtained from the native compiled-expression occurrence extractor and are
checked again by the current inspector during report production. -/

def classification_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.actual_zero_iff)
      (type_of% (realize signature
        (fun _ r a => actualSource r (1 + 2 ^ a)) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.actual_zero_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.classification_registration
  realizationSource := none
  generated := false
  arena := .source ⟨classificationArena⟩
  objectArena := .source ⟨classificationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classificationArena ⟨classification_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r a => actualSource r (1 + 2 ^ a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def divisibility_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.actual_zero_iff_dvd)
      (type_of% (realize signature
        (fun _ r a => actualSource r (1 + 2 ^ a)) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.actual_zero_iff_dvd.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.divisibility_registration
  realizationSource := none
  generated := false
  arena := .source ⟨divisibilityArena⟩
  objectArena := .source ⟨divisibilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source divisibilityArena ⟨divisibility_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r a => actualSource r (1 + 2 ^ a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def count_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.actual_zero_subsets_card)
      (type_of% (realize signature
        (fun _ r a => actualSource r (1 + 2 ^ a)) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.actual_zero_subsets_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets.count_registration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨count_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r a => actualSource r (1 + 2 ^ a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.TwoBitZeroSubsets
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg",
        "fn", "fn", "arg", "body", "fn", "arg", "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms classification_registration
#print axioms divisibility_registration
#print axioms count_registration
#print axioms classification_audit
#print axioms divisibility_audit
#print axioms count_audit

end Reg.D5.S3.Combinatorics.Circle.TwoBitZeroSubsets
