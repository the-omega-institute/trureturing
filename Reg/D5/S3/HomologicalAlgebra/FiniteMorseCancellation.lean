import D5.S3.HomologicalAlgebra.FiniteMorseCancellation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source audit for the polynomial cutoff in the contraction predicate. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.HomologicalAlgebra.FiniteMorseCancellation
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.FiniteMorseCancellation

universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law out := ∀ {F : Type u} [Fintype F] (m : Matching F)
    [DecidableEq F] (r : F → ℕ) (k N : ℕ) (_positive : 1 ≤ N)
    (_bound : ∀ j, r j < N)
    (_unmatched : ∀ i j, i ≠ m.mate j → m.D i j ≠ 0 → r i < r j)
    (_matched : ∀ j, m.d j + 1 = m.d (m.mate j) → r (m.mate j) < r j)
    (_critical_size : ∀ j, m.mate j = j → m.d j = k),
      m.Contraction (out.readout () () N)

private def sample : Matching (ULift.{u} Unit) where
  d := fun _ => 0
  mate := id
  D := 0
  involutive := fun _ => rfl
  adjacent := by simp
  differential_sq := by simp
  downward := by simp
  unit_entry := by simp

private theorem sample_zero_fails : ¬ sample.{u}.Contraction 0 := by
  intro h
  let j : sample.{u}.Critical := ⟨ULift.up (), rfl⟩
  have hdiag := congrFun (congrFun h.critical_coefficients j) j
  simp [Matching.I, Matching.K,
    _root_.D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial] at hdiag

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  exact sample_zero_fails (law sample (fun _ => 0) 0 1 (by decide) (fun _ => by decide)
    (by simp [sample]) (by simp [sample]) (by simp [sample]))

def source_registration : Registration arena.{u}
    (type_of% @Matching.finite_morse_cancellation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Matching.finite_morse_cancellation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rejected, fun other hne => (hne (Subsingleton.elim other role)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro role
    exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Matching.finite_morse_cancellation.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.HomologicalAlgebra.FiniteMorseCancellation.finite_morse_cancellation
  realizationName := `Reg.D5.S3.HomologicalAlgebra.FiniteMorseCancellation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteMorseCancellation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.HomologicalAlgebra.FiniteMorseCancellation
