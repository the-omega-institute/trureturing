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
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (hk : 0 < k) (t : ℕ) (S : Finset (Fin k)),
    let s := R.readout () k t
    let b : Fin k → Bool := fun i => decide (s i < 0)
    let n := (Finset.univ.filter (fun i : Fin k => s i < 0)).card
    let E := orbitNegativeCount k hk S b ⟨0, by omega⟩
    ((∀ h, orbitSum k hk S s h = 0) ↔
      (∀ h, orbitNegativeCount k hk S b h = E)) ∧
    ((∀ h, orbitSum k hk S s h = 0) → k * E = S.card * n) ∧
    (Nat.Coprime k n →
      (∀ h, orbitSum k hk S s h = 0) →
      (S = ∅ ∨ S = Finset.univ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) 0 ({0} : Finset (Fin 1))
  have hbal : ∀ h : Fin 1,
      orbitNegativeCount 1 (by decide) ({0} : Finset (Fin 1))
          (fun _ => decide ((-1 : ℤ) < 0)) h =
        orbitNegativeCount 1 (by decide) ({0} : Finset (Fin 1))
          (fun _ => decide ((-1 : ℤ) < 0)) ⟨0, by decide⟩ := by
    intro hphase
    simp [orbitNegativeCount]
  have hz := hh.1.2 hbal
  have hz0 := hz (0 : Fin 1)
  norm_num [rejected, realize, orbitSum, finCycle_apply] at hz0

private theorem actual_law : arena.Law actual := by
  intro k hk t S
  dsimp [actual, realize]
  exact actualSource_orbit_zero_balanced k hk t S

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.actualSource_orbit_zero_balanced)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualSource_orbit_zero_balanced, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.actualSource_orbit_zero_balanced)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.actualSource_orbit_zero_balanced.__information_unit
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
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "fn", "arg"],
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end Reg.D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
