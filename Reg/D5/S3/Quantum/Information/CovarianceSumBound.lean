import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.CovarianceSumBound
import Reg.Support.DependentFamily

/-! Source-bound registrations for the public density-state expectation laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

namespace Reg.D5.S3.Quantum.Information.CovarianceSumBound

open _root_.D5.S3.Quantum.Information.CovarianceSumBound
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder

namespace ExpectSmul

abbrev signature : Signature where
  Params := Σ n : Type u, Σ _ : Fintype n, DecidableEq n
  State p := @DensityState (Sigma.fst p) (Sigma.fst (Sigma.snd p))
    (Sigma.snd (Sigma.snd p)) × (ℝ × Matrix (Sigma.fst p) (Sigma.fst p) ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u}
    (fun _ p s =>
      @expectation (Sigma.fst p) (Sigma.fst (Sigma.snd p))
        (Sigma.snd (Sigma.snd p)) s.1 (s.2.1 • s.2.2))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : (signature.{u}).Params,
    ∀ ρ : @DensityState (Sigma.fst p) (Sigma.fst (Sigma.snd p))
      (Sigma.snd (Sigma.snd p)),
    ∀ t : ℝ, ∀ A : Matrix (Sigma.fst p) (Sigma.fst p) ℂ,
      R.readout () p (ρ, (t, A)) =
        t * @expectation (Sigma.fst p) (Sigma.fst (Sigma.snd p))
          (Sigma.snd (Sigma.snd p)) ρ A

theorem bridge : (type_of% @expect_smul.{u}) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p
    intro ρ t A
    exact @h (Sigma.fst p) (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p)) ρ t A
  · intro h n hn hd ρ t A
    exact h ⟨n, hn, hd⟩ ρ t A

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let p : signature.Params := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  let ρ : @DensityState (ULift.{u} Unit) inferInstance inferInstance :=
    ⟨1, zero_le_one, by
      change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
      simp [Matrix.trace]⟩
  have he := h p ρ 1 1
  change (0 : ℝ) = 1 * expectation ρ (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) at he
  rw [expect_one, mul_one] at he
  norm_num at he

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let p : signature.Params := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  let ρ : @DensityState (ULift.{u} Unit) inferInstance inferInstance :=
    ⟨1, zero_le_one, by
      change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
      simp [Matrix.trace]⟩
  refine ⟨p, (ρ, (0, 1)), (ρ, (1, 1)), ?_⟩
  change expectation ρ (0 • (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)) ≠
    expectation ρ (1 • (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ))
  rw [zero_smul, one_smul]
  have hz : expectation ρ (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0 := by
    simp [expectation]
  rw [hz, expect_one]
  norm_num

def source_registration : Registration arena.{u} (type_of% @expect_smul.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @expect_smul.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Information.CovarianceSumBound.expect_smul.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CovarianceSumBound.ExpectSmul.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.CovarianceSumBound.ExpectSmul.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p s =>
      @expectation (Sigma.fst p) (Sigma.fst (Sigma.snd p))
        (Sigma.snd (Sigma.snd p)) s.1 (s.2.1 • s.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CovarianceSumBound
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ExpectSmul

namespace ExpectOne

abbrev signature : Signature where
  Params := Σ n : Type u, Σ _ : Fintype n, DecidableEq n
  State p := @DensityState (Sigma.fst p) (Sigma.fst (Sigma.snd p))
    (Sigma.snd (Sigma.snd p)) × Matrix (Sigma.fst p) (Sigma.fst p) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u}
    (fun _ p s =>
      @expectation (Sigma.fst p) (Sigma.fst (Sigma.snd p))
        (Sigma.snd (Sigma.snd p)) s.1 s.2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : (signature.{u}).Params,
    ∀ ρ : @DensityState (Sigma.fst p) (Sigma.fst (Sigma.snd p))
      (Sigma.snd (Sigma.snd p)),
      R.readout () p (ρ, @One.one (Matrix (Sigma.fst p) (Sigma.fst p) ℂ)
        (@Matrix.one (Sigma.fst p) ℂ (Sigma.snd (Sigma.snd p)) inferInstance inferInstance)) = 1

theorem bridge : (type_of% @expect_one.{u}) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p
    intro ρ
    exact @h (Sigma.fst p) (Sigma.fst (Sigma.snd p)) (Sigma.snd (Sigma.snd p)) ρ
  · intro h n hn hd ρ
    exact h ⟨n, hn, hd⟩ ρ

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let p : signature.Params := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  let ρ : @DensityState (ULift.{u} Unit) inferInstance inferInstance :=
    ⟨1, zero_le_one, by
      change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
      simp [Matrix.trace]⟩
  have he := h p ρ
  change (0 : ℝ) = 1 at he
  norm_num at he

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let p : signature.Params := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  let ρ : @DensityState (ULift.{u} Unit) inferInstance inferInstance :=
    ⟨1, zero_le_one, by
      change Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 1
      simp [Matrix.trace]⟩
  refine ⟨p, (ρ, 0), (ρ, 1), ?_⟩
  change expectation ρ (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) ≠
    expectation ρ (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
  rw [expect_one]
  norm_num [expectation]

def source_registration : Registration arena.{u} (type_of% @expect_one.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @expect_one.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Information.CovarianceSumBound.expect_one.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.CovarianceSumBound.ExpectOne.unit
  realizationName := `Reg.D5.S3.Quantum.Information.CovarianceSumBound.ExpectOne.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p s =>
      @expectation (Sigma.fst p) (Sigma.fst (Sigma.snd p))
        (Sigma.snd (Sigma.snd p)) s.1 s.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.CovarianceSumBound
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ExpectOne

end Reg.D5.S3.Quantum.Information.CovarianceSumBound
