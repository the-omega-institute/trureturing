import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.SymmetricRankOneGuards
import Reg.Support.UniverseSingleReadout

/-! Source-bound audits for the polynomial guard criteria. -/

namespace Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards

open _root_.D5.S3.QuadraticForms.SymmetricRankOneKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open Polynomial
open scoped BigOperators
open scoped RealInnerProductSpace

set_option autoImplicit false

universe u v w
noncomputable section

abbrev IndexData := Σ ι : Type u, Σ _ : Fintype ι, DecidableEq ι

abbrev degreeSignature := signature IndexData.{u} (fun _ => ℤ[X]) (fun _ => ℕ)

def degreeActual : Realization degreeSignature.{u} :=
  realize degreeSignature.{u} (fun _ _ P => P.natDegree) (fun e => nomatch e)

def degreeRejected : Realization degreeSignature.{u} :=
  realize degreeSignature.{u} (fun _ _ _ => 1) (fun e => nomatch e)

/-- Observe the degree of the common response numerator. -/
abbrev degreeArena : Arena where
  signature := degreeSignature.{u}
  Law R := ∀ {ι : Type u} [index : Fintype ι] [Nonempty ι] [dec : DecidableEq ι]
    (P Q : ι → ℤ[X]) (t : ℤ) (n : ι → ℕ) (_hpos : ∀ i, 0 < n i)
    (_hQ : ∀ i, (Q i).Monic ∧ (Q i).natDegree = n i)
    (_hP : ∀ i, (P i).natDegree = n i - 1 ∧ (P i).leadingCoeff = -(n i : ℤ)),
    let N := ∑ i, n i
    R.readout () ⟨ι, index, dec⟩ (responseNumerator P Q) = N - 1 ∧
    (responseNumerator P Q).leadingCoeff = -(N : ℤ) ∧
    (responseGuard P Q t).Monic ∧ (responseGuard P Q t).natDegree = N

private theorem degreeRejected_law : ¬ degreeArena.{u}.Law degreeRejected.{u} := by
  intro h
  have bad := (h (ι := ULift.{u} Unit) (fun _ => -1) (fun _ => X) 0 (fun _ => 1)
    (by simp) (by simp) (by simp)).1
  change (1 : ℕ) = (∑ _ : Unit, (1 : ℕ)) - 1 at bad
  simp at bad

def degreeSource : Registration degreeArena.{u} (type_of% @responseGuard_degrees.{u}) where
  actual := degreeActual.{u}
  bridge := Iff.rfl
  variation := ⟨@responseGuard_degrees.{u}, degreeRejected.{u}, degreeRejected_law.{u}⟩
  sensitivity := sensitivity degreeArena.{u}.Law degreeActual.{u} degreeRejected.{u} degreeRejected_law.{u}
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, inferInstance, inferInstance⟩, (1 : ℤ[X]), X, ?_⟩
    change (1 : ℤ[X]).natDegree ≠ X.natDegree
    simp

abbrev countSignature := signature Unit (fun _ => Finset ℝ) (fun _ => ℕ)

def countActual : Realization countSignature :=
  realize countSignature (fun _ _ candidates => candidates.card) (fun e => nomatch e)

def countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Observe the distinct candidate count while retaining the exact existence criterion. -/
abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ {ι : Type u} (s : Finset ι) (Q : ι → ℤ[X])
    (_hQ : ∀ i ∈ s, Q i ≠ 0) (target : ℝ → Prop)
    (_hoff : ∀ x : ℝ, (∀ i ∈ s, (Q i).eval₂ (Int.castRingHom ℝ) x ≠ 0) → ¬ target x),
    R.readout () () (realGuardCandidates s Q) ≤ ∑ i ∈ s, (Q i).natDegree ∧
      ((∃ x : ℝ, target x) ↔ ∃ x ∈ realGuardCandidates s Q, target x)

private theorem countRejected_law : ¬ countArena.{u}.Law countRejected := by
  intro h
  have bad := (h (∅ : Finset (ULift.{u} Unit)) (fun _ => 1) (by simp)
    (fun _ => False) (by simp)).1
  change 1 ≤ ∑ i ∈ (∅ : Finset (ULift.{u} Unit)), (1 : ℤ[X]).natDegree at bad
  simp at bad

def countSource : Registration countArena.{u} (type_of% @realGuardCandidates_spec.{u}) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@realGuardCandidates_spec.{u}, countRejected, countRejected_law.{u}⟩
  sensitivity := sensitivity countArena.{u}.Law countActual countRejected countRejected_law.{u}
  dependence := by
    intro i
    refine ⟨(), ∅, {0}, ?_⟩
    change (∅ : Finset ℝ).card ≠ ({0} : Finset ℝ).card
    simp

def degreeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@responseGuard_degrees.{u}) (Realization degreeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards.degreeUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards.degreeSource
  realizationSource := none
  generated := false
  arena := .source ⟨degreeArena.{u}⟩
  objectArena := .source ⟨degreeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source degreeArena.{u} ⟨degreeSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize degreeSignature.{u} (fun _ _ P => P.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneGuards
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def countAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@realGuardCandidates_spec.{u}) (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards.countUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards.countSource
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u}⟩
  objectArena := .source ⟨countArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena.{u} ⟨countSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ candidates => candidates.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneGuards
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev evaluationSignature :=
  signature (Σ ι : Type v, Σ _ : Fintype ι, Σ _ : DecidableEq ι, ℝ)
    (fun _ => ℤ[X]) (fun _ => ℝ)

def evaluationActual : Realization evaluationSignature.{v} :=
  realize evaluationSignature.{v} (fun _ p P => P.eval₂ (Int.castRingHom ℝ) p.2.2.2) (fun e => nomatch e)

def evaluationRejected : Realization evaluationSignature.{v} :=
  realize evaluationSignature.{v} (fun _ _ _ => 1) (fun e => nomatch e)

/-- Observe the numerator at the same real shift used to test every guard. -/
abbrev evaluationArena : Arena where
  signature := evaluationSignature.{v}
  Law R := ∀ {ι : Type v} [index : Fintype ι] [dec : DecidableEq ι]
    {F : ι → Type w} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)]
    (A : ∀ i, F i →ₗ[ℝ] F i) (_hA : ∀ i, (A i).IsSymmetric) (u : PiLp 2 F)
    (P Q : ι → ℤ[X]) (t : ℤ) (x : ℝ)
    (_hQ : ∀ i, (Q i).eval₂ (Int.castRingHom ℝ) x ≠ 0)
    (_hguard : (responseGuard P Q t).eval₂ (Int.castRingHom ℝ) x ≠ 0)
    (_hchild : ∀ i, Module.finrank ℝ (LinearMap.ker (A i)) = 0 ∧
      ScalarResponse (A i) (u i)
        ((P i).eval₂ (Int.castRingHom ℝ) x / (Q i).eval₂ (Int.castRingHom ℝ) x)),
    Module.finrank ℝ (LinearMap.ker (update (blockDiagonal A) u (t : ℝ))) = 0 ∧
    ScalarResponse (update (blockDiagonal A) u (t : ℝ)) u
      (R.readout () ⟨ι, index, dec, x⟩ (responseNumerator P Q) /
        (responseGuard P Q t).eval₂ (Int.castRingHom ℝ) x)

private theorem evaluationRejected_law :
    ¬ evaluationArena.{v,w}.Law evaluationRejected.{v} := by
  intro law
  let I := ULift.{v} Empty
  let A : ∀ _ : I, EuclideanSpace ℝ (ULift.{w} Unit) →ₗ[ℝ]
      EuclideanSpace ℝ (ULift.{w} Unit) := fun i => i.down.elim
  let P : I → ℤ[X] := fun i => i.down.elim
  let Q : I → ℤ[X] := fun i => i.down.elim
  have guard : (responseGuard P Q 0).eval₂ (Int.castRingHom ℝ) 0 = 1 := by
    simp [responseGuard]
  have bad := (law A (fun i => i.down.elim) 0 P Q 0 0 (fun i => i.down.elim)
    (by rw [guard]; exact one_ne_zero) (fun i => i.down.elim)).2
  obtain ⟨y, hy⟩ := bad.1
  have h := bad.2 y hy
  change ⟪(0 : PiLp 2 (fun _ : I => EuclideanSpace ℝ (ULift.{w} Unit))), y⟫ =
    1 / (responseGuard P Q 0).eval₂ (Int.castRingHom ℝ) 0 at h
  simp [guard] at h

def evaluationSource :
    Registration evaluationArena.{v,w} (type_of% @update_block_of_guard_ne_zero.{v,w}) where
  actual := evaluationActual.{v}
  bridge := Iff.rfl
  variation := ⟨@update_block_of_guard_ne_zero.{v,w}, evaluationRejected.{v}, evaluationRejected_law.{v,w}⟩
  sensitivity := sensitivity evaluationArena.{v,w}.Law evaluationActual.{v}
    evaluationRejected.{v} evaluationRejected_law.{v,w}
  dependence := by
    intro i
    refine ⟨⟨ULift.{v} Unit, inferInstance, inferInstance, 0⟩, 0, 1, ?_⟩
    change (0 : ℤ[X]).eval₂ (Int.castRingHom ℝ) 0 ≠ (1 : ℤ[X]).eval₂ (Int.castRingHom ℝ) 0
    simp

def evaluationAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_block_of_guard_ne_zero.{v,w}) (Realization evaluationSignature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards.evaluationUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards.evaluationSource
  realizationSource := none
  generated := false
  arena := .source ⟨evaluationArena.{v,w}⟩
  objectArena := .source ⟨evaluationArena.{v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evaluationArena.{v,w} ⟨evaluationSource.{v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature.{v} (fun _ p P => P.eval₂ (Int.castRingHom ℝ) p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneGuards
    definition := none
    coordinates := #[0, 13]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.QuadraticForms.SymmetricRankOneGuards
