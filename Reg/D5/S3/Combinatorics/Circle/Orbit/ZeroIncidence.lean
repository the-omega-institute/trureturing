import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
import Reg.Support.DependentFamily

/-! Source-bound registration for the actual orbitwise zero-incidence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence

open _root_.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open scoped BigOperators

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output role k := match role with
    | false => Fin k → Bool
    | true => Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role k t => match role with
    | false => negativeBit k t
    | true => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun role k t => match role with
    | false => negativeBit k t
    | true => fun _ => -1) (fun e => nomatch e)

def rejectedBits : Realization signature :=
  realize signature (fun role k t => match role with
    | false => fun _ => false
    | true => actualSource k t) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (hk : 0 < k) (t : ℕ) (S : Finset (Fin k)),
    let b := R.readout false k t
    let n := (negativeSupport k t hk).card
    let E := orbitNegativeCount k hk S b ⟨0, by omega⟩
    ((∀ h, orbitSum k hk S (R.readout true k t) h = 0) ↔
      (∀ h, orbitNegativeCount k hk S b h = E)) ∧
    ((∀ h, orbitSum k hk S (R.readout true k t) h = 0) → k * E = S.card * n) ∧
    (Nat.Coprime k n →
      (∀ h, orbitSum k hk S (R.readout true k t) h = 0) →
      (S = ∅ ∨ S = Finset.univ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) 0 ({0} : Finset (Fin 1))
  have hbal : ∀ h : Fin 1,
      orbitNegativeCount 1 (by decide) ({0} : Finset (Fin 1))
          (negativeBit 1 0) h =
        orbitNegativeCount 1 (by decide) ({0} : Finset (Fin 1))
          (negativeBit 1 0) ⟨0, by decide⟩ := by
    intro hphase
    simp [orbitNegativeCount, negativeBit, actualSource, centered, modulus]
  have hz := hh.1.2 hbal
  have hz0 := hz (0 : Fin 1)
  norm_num [rejected, realize, orbitSum, finCycle_apply] at hz0

private theorem rejected_bits_law : ¬ arena.Law rejectedBits := by
  intro h
  have hh := h 3 (by decide) 1 ({0} : Finset (Fin 3))
  have hbal : ∀ h : Fin 3,
      orbitNegativeCount 3 (by decide) ({0} : Finset (Fin 3))
          (fun _ => false) h =
        orbitNegativeCount 3 (by decide) ({0} : Finset (Fin 3))
          (fun _ => false) ⟨0, by decide⟩ := by
    intro hphase
    simp [orbitNegativeCount]
  have hz0 := hh.1.2 hbal (0 : Fin 3)
  norm_num [rejectedBits, realize, orbitSum, finCycle_apply,
    actualSource, centered, modulus] at hz0

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i with
  | false =>
    refine ⟨3, 0, 4, ?_⟩
    intro he
    have hh := congrFun he (0 : Fin 3)
    norm_num [actual, realize, negativeBit, actualSource, centered, modulus] at hh
  | true =>
    refine ⟨3, 0, 1, ?_⟩
    intro he
    have hh := congrFun he (0 : Fin 3)
    norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena
    (type_of% @actualSource_orbit_zero_balanced) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualSource_orbit_zero_balanced, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i with
      | false =>
        refine ⟨rejectedBits, ?_, rfl, rejected_bits_law⟩
        intro j hji
        cases j with
        | false => exact False.elim (hji rfl)
        | true => rfl
      | true =>
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j hji
        cases j with
        | false => rfl
        | true => exact False.elim (hji rfl)
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.actualSource_orbit_zero_balanced)
    (Realization signature) Nat Bool where
  unitName := Lean.Name.str
    `D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.actualSource_orbit_zero_balanced
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun role k t => match role with
    | false => negativeBit k t
    | true => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "value"],
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence

namespace Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence

open _root_.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence

abbrev allEqualSignature : Signature where
  Params := Σ k : ℕ, Fin k
  State p := Fin p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def allEqualActual : Realization allEqualSignature :=
  realize allEqualSignature (fun _ p g => g p.2)
    (fun e => nomatch e)

def allEqualRejected : Realization allEqualSignature :=
  realize allEqualSignature (fun _ p g => g p.2 + 1) (fun e => nomatch e)

abbrev allEqualArena : Arena where
  signature := allEqualSignature
  Law R := ∀ {k : ℕ} (hk : 0 < k) (g : Fin k → ℕ),
    (∀ h, g h = g (finRotate k h)) →
      ∀ h, R.readout () ⟨k, h⟩ g = g ⟨0, by omega⟩

private theorem allEqualRejectedLaw : ¬ allEqualArena.Law allEqualRejected := by
  intro h
  have hbad := h (k := 1) (by decide) (fun _ => 0) (by intro; rfl) (0 : Fin 1)
  norm_num [allEqualRejected, realize] at hbad

private theorem allEqualDependence :
    ObservationalDependence allEqualSignature allEqualActual := by
  intro i
  refine ⟨⟨2, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [allEqualActual, realize]

def allEqualSourceRegistration :
    Registration allEqualArena (type_of% @all_equal_of_adjacent) where
  actual := allEqualActual
  bridge := Iff.rfl
  variation := ⟨all_equal_of_adjacent, allEqualRejected, allEqualRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨allEqualRejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, allEqualRejectedLaw⟩
    · intro e
      exact nomatch e
  dependence := allEqualDependence

def allEqualRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.all_equal_of_adjacent)
      (Realization allEqualSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.all_equal_of_adjacent.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.allEqualSourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨allEqualArena⟩
  objectArena := .source ⟨allEqualArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source allEqualArena ⟨allEqualSourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize allEqualSignature (fun _ p g => g p.2)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms allEqualSourceRegistration
#print axioms allEqualRegistration

end Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
