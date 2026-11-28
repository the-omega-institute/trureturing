import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! Source-bound registration for the signed phase product. -/

namespace Reg.D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation

open _root_.D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators NumberField

universe u v

noncomputable section

set_option linter.checkUnivs false in
abbrev Parameters :=
  Σ K : Type u, Σ _ : Field K, Σ ι : Type v, Finset ι × (ι → K)

abbrev signature : Signature where
  Params := Parameters.{u, v}
  State p := p.2.2.1 → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p n => letI := p.2.1; ∏ i ∈ p.2.2.2.1, p.2.2.2.2 i ^ n i)
    (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p _ => letI := p.2.1; 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {K : Type u} [F : Field K] [NumberField K] {ι : Type v}
    (s : Finset ι) (phase : ι → K) (n : ι → ℤ) (D : ℕ) (_hD : D ≠ 0)
    (_hpos : ∀ i ∈ s, IsIntegral ℤ ((D : K) * phase i))
    (_hneg : ∀ i ∈ s, IsIntegral ℤ ((D : K) * (phase i)⁻¹))
    (_hunit : ∀ (τ : K →+* ℂ) (i : ι), i ∈ s → ‖τ (phase i)‖ = 1)
    (_hnontrivial : (∏ i ∈ s, phase i ^ n i) ≠ 1) (σ : K →+* ℂ),
    let B := D ^ (∑ i ∈ s, (n i).natAbs)
    1 ≤ ‖σ (R.readout () ⟨K, F, ι, s, phase⟩ n) - 1‖ *
      ((B : ℝ) * (2 * B) ^ (Module.finrank ℚ K - 1))

private def Q := ULift.{u} ℚ
private def X := ULift.{v} Unit

private noncomputable instance : Field Q := inferInstanceAs (Field (ULift ℚ))
private instance : CharZero Q := charZero_of_inj_zero fun n h =>
  Nat.cast_eq_zero.mp (show (n : ℚ) = 0 from congrArg ULift.down h)

private instance : NumberField Q where
  to_charZero := inferInstance
  to_finiteDimensional := Module.Finite.of_surjective (Algebra.linearMap ℚ Q)
    (fun ⟨q⟩ => ⟨q, rfl⟩)
private instance : DecidableEq X := inferInstanceAs (DecidableEq (ULift Unit))

private def exampleIndex : X := ⟨()⟩
private def examplePhase : X → Q := fun _ => -1
private def exampleExponent : X → ℤ := fun _ => 1

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hzero := h (K := Q) {exampleIndex} examplePhase exampleExponent 1 (by decide)
    (by intro i hi; simpa only [Nat.cast_one, one_mul, examplePhase] using (isIntegral_one.neg : IsIntegral ℤ (-1 : Q)))
    (by intro i hi; simp only [Nat.cast_one, one_mul, examplePhase, inv_neg, inv_one]; exact isIntegral_one.neg)
    (by intro τ i hi; simp [examplePhase])
    (by
      simp only [examplePhase, exampleExponent, Finset.prod_singleton, zpow_one]
      intro h
      have he : (-1 : ℚ) = 1 := congrArg ULift.down h
      norm_num at he)
    ((Rat.castHom ℂ).comp ULift.ringEquiv.toRingHom)
  norm_num [rejected, realize] at hzero

theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  let s : Finset X := {exampleIndex}
  refine ⟨⟨Q, inferInstance, X, s, examplePhase⟩, fun _ => 0, exampleExponent, ?_⟩
  intro h
  have he : (1 : Q) = -1 := by
    simpa [actual, realize, s, examplePhase, exampleExponent] using h
  have hd : (1 : ℚ) = -1 := congrArg ULift.down he
  norm_num at hd

def source_registration : Registration arena.{u, v}
    (type_of% @signed_product_separation.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_product_separation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@signed_product_separation.{u, v}) (Realization signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => letI := p.2.1; ∏ i ∈ p.2.2.2.1, p.2.2.2.2 i ^ n i)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation
    definition := none
    coordinates := #[0, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "arg",
        "arg", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end

end Reg.D5.S3.Fourier.Asymptotics.AlgebraicPhaseSeparation
