import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.SymmetricRankOneKernel
import Reg.Support.UniverseSingleReadout

/-! Source-bound audits for the exact rank-one transitions. -/

namespace Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel

open _root_.D5.S3.QuadraticForms.SymmetricRankOneKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.UniverseSingleReadout (signature sensitivity)
open scoped BigOperators
open scoped RealInnerProductSpace

set_option autoImplicit false

universe u v
noncomputable section

abbrev scalarSignature := signature Unit (fun _ => ℝ) (fun _ => ℝ)

def factorActual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x => 1 + x) (fun e => nomatch e)

def inverseActual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x => 1 / x) (fun e => nomatch e)

def scalarZero : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => 0) (fun e => nomatch e)

def scalarOne : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem factorDepends : ObservationalDependence scalarSignature factorActual := by
  intro i
  exact ⟨(), 0, 1, by change (1 : ℝ) + 0 ≠ 1 + 1; norm_num⟩

/-- A single real coordinate in the same universe as the original vector space. -/
private abbrev Line := EuclideanSpace ℝ (ULift.{u} Unit)

private def unitVector : Line.{u} :=
  WithLp.toLp 2 (fun _ => 1)

private theorem unitPairing : ⟪unitVector.{u}, unitVector.{u}⟫ = 1 := by
  rw [PiLp.inner_apply]
  simp [unitVector]

private theorem identityResponse :
    ScalarResponse (LinearMap.id : Line.{u} →ₗ[ℝ] Line.{u}) unitVector 1 := by
  refine ⟨⟨unitVector, rfl⟩, ?_⟩
  intro y hy
  change y = unitVector at hy
  simpa [hy] using unitPairing.{u}

/-- Observe the inverse coupling appearing in the response after a flagged input. -/
abbrev flaggedArena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : E →ₗ[ℝ] E} {e : E} {t : ℝ} [FiniteDimensional ℝ E]
    (_hB : B.IsSymmetric) (_ht : t ≠ 0) (_h : HasNonzeroPairing B e),
    Module.finrank ℝ (LinearMap.ker (update B e t)) + 1 =
      Module.finrank ℝ (LinearMap.ker B) ∧
      ScalarResponse (update B e t) e (R.readout () () t)

private theorem flaggedRejected : ¬ flaggedArena.{u}.Law scalarZero := by
  intro law
  have hflag : HasNonzeroPairing (0 : Line.{u} →ₗ[ℝ] Line.{u}) unitVector :=
    ⟨⟨unitVector, by simp⟩, by
      change ⟪unitVector.{u}, unitVector.{u}⟫ ≠ 0
      rw [unitPairing]
      exact one_ne_zero⟩
  have actual := (update_of_nonzero_pairing (B := (0 : Line.{u} →ₗ[ℝ] Line.{u}))
    (e := unitVector) (t := 1) (by simp [LinearMap.IsSymmetric]) one_ne_zero hflag).2
  have bad := (law (B := (0 : Line.{u} →ₗ[ℝ] Line.{u})) (e := unitVector) (t := 1)
    (by simp [LinearMap.IsSymmetric]) one_ne_zero hflag).2
  obtain ⟨y, hy⟩ := actual.1
  have hy0 := bad.2 y hy
  have hy1 := actual.2 y hy
  change ⟪unitVector.{u}, y⟫ = 0 at hy0
  rw [hy0] at hy1
  norm_num at hy1

def flaggedSource : Registration flaggedArena.{u} (type_of% @update_of_nonzero_pairing.{u}) where
  actual := inverseActual
  bridge := Iff.rfl
  variation := ⟨@update_of_nonzero_pairing.{u}, scalarZero, flaggedRejected.{u}⟩
  sensitivity := sensitivity flaggedArena.{u}.Law inverseActual scalarZero flaggedRejected.{u}
  dependence := by
    intro i
    exact ⟨(), 0, 1, by change (1 : ℝ) / 0 ≠ 1 / 1; norm_num⟩

/-- Observe the factor whose zero creates a new kernel direction. -/
abbrev resonantArena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : E →ₗ[ℝ] E} {e : E} {t S : ℝ} [FiniteDimensional ℝ E]
    (_hB : B.IsSymmetric) (_h : ScalarResponse B e S) (_htS : R.readout () () (t * S) = 0),
    Module.finrank ℝ (LinearMap.ker (update B e t)) =
      Module.finrank ℝ (LinearMap.ker B) + 1 ∧ HasNonzeroPairing (update B e t) e

private theorem resonantRejected : ¬ resonantArena.{u}.Law scalarZero := by
  intro law
  have response : ScalarResponse (0 : Line.{u} →ₗ[ℝ] Line.{u}) 0 0 := by
    exact ⟨⟨0, by simp⟩, fun _ _ => by simp⟩
  obtain ⟨_, ⟨z, hz⟩⟩ := law (t := 0) (by simp [LinearMap.IsSymmetric]) response rfl
  exact hz (by simp)

def resonantSource : Registration resonantArena.{u} (type_of% @update_of_resonance.{u}) where
  actual := factorActual
  bridge := Iff.rfl
  variation := ⟨@update_of_resonance.{u}, scalarZero, resonantRejected.{u}⟩
  sensitivity := sensitivity resonantArena.{u}.Law factorActual scalarZero resonantRejected.{u}
  dependence := factorDepends

/-- Observe the factor whose nonvanishing preserves the full kernel. -/
abbrev nonresonantArena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : E →ₗ[ℝ] E} {e : E} {t S : ℝ} (_hB : B.IsSymmetric)
    (_h : ScalarResponse B e S) (_htS : R.readout () () (t * S) ≠ 0),
    LinearMap.ker (update B e t) = LinearMap.ker B ∧
      ScalarResponse (update B e t) e (S / (1 + t * S))

private theorem nonresonantRejected : ¬ nonresonantArena.{u}.Law scalarOne := by
  intro law
  have symm : (LinearMap.id : Line.{u} →ₗ[ℝ] Line.{u}).IsSymmetric := by
    intro x y
    rfl
  have actual := (update_of_resonance (t := -1) symm identityResponse.{u} (by norm_num)).1
  have bad := (law (t := -1) symm identityResponse.{u} one_ne_zero).1
  rw [bad] at actual
  omega

def nonresonantSource :
    Registration nonresonantArena.{u} (type_of% @update_of_nonresonance.{u}) where
  actual := factorActual
  bridge := Iff.rfl
  variation := ⟨@update_of_nonresonance.{u}, scalarOne, nonresonantRejected.{u}⟩
  sensitivity := sensitivity nonresonantArena.{u}.Law factorActual scalarOne nonresonantRejected.{u}
  dependence := factorDepends

def flaggedAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_of_nonzero_pairing.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.flaggedUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.flaggedSource
  realizationSource := none
  generated := false
  arena := .source ⟨flaggedArena.{u}⟩
  objectArena := .source ⟨flaggedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source flaggedArena.{u} ⟨flaggedSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => 1 / x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def resonantAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_of_resonance.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.resonantUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.resonantSource
  realizationSource := none
  generated := false
  arena := .source ⟨resonantArena.{u}⟩
  objectArena := .source ⟨resonantArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resonantArena.{u} ⟨resonantSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => 1 + x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def nonresonantAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_of_nonresonance.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.nonresonantUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.nonresonantSource
  realizationSource := none
  generated := false
  arena := .source ⟨nonresonantArena.{u}⟩
  objectArena := .source ⟨nonresonantArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nonresonantArena.{u} ⟨nonresonantSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => 1 + x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev InnerMapData :=
  Σ E : Type u, Σ _g : NormedAddCommGroup E, Σ _ : InnerProductSpace ℝ E, E →ₗ[ℝ] E

abbrev applicationSignature := signature InnerMapData.{u} (fun p => p.1) (fun p => p.1)

def applicationActual : Realization applicationSignature.{u} :=
  realize applicationSignature (fun _ p y => letI := p.2.1; letI := p.2.2.1; p.2.2.2 y) (fun e => nomatch e)

def applicationRejected : Realization applicationSignature.{u} :=
  realize applicationSignature (fun _ p _ => letI := p.2.1; (0 : p.1)) (fun e => nomatch e)

abbrev applicationArena : Arena where
  signature := applicationSignature.{u}
  Law R := ∀ {E : Type u} [g : NormedAddCommGroup E] [ip : InnerProductSpace ℝ E]
    {B : E →ₗ[ℝ] E} {e : E} [FiniteDimensional ℝ E] (_hB : B.IsSymmetric),
    (∃ y, R.readout () ⟨E, g, ip, B⟩ y = e) ↔ ¬ HasNonzeroPairing B e

private theorem unitVector_ne_zero : unitVector.{u} ≠ 0 := by
  intro h
  have hp := unitPairing.{u}
  rw [h] at hp
  simp at hp

private theorem applicationRejected_law :
    ¬ applicationArena.{u}.Law applicationRejected.{u} := by
  intro law
  have symm : (LinearMap.id : Line.{u} →ₗ[ℝ] Line.{u}).IsSymmetric := fun _ _ => rfl
  have hn := (solvable_iff_no_nonzero_pairing (e := unitVector) symm).mp ⟨unitVector, rfl⟩
  obtain ⟨_, hy⟩ := (law symm).mpr hn
  exact unitVector_ne_zero.{u} hy.symm

def applicationSource :
    Registration applicationArena.{u} (type_of% @solvable_iff_no_nonzero_pairing.{u}) where
  actual := applicationActual.{u}
  bridge := Iff.rfl
  variation := ⟨@solvable_iff_no_nonzero_pairing.{u}, applicationRejected.{u},
    applicationRejected_law.{u}⟩
  sensitivity := sensitivity applicationArena.{u}.Law applicationActual.{u} applicationRejected.{u}
    applicationRejected_law.{u}
  dependence := by
    intro i
    exact ⟨⟨Line.{u}, inferInstance, inferInstance, LinearMap.id⟩, unitVector, 0, unitVector_ne_zero.{u}⟩

abbrev responseSignature := signature InnerMapData.{u} (fun p => p.1) (fun _ => ℝ → Prop)

def responseActual : Realization responseSignature.{u} :=
  realize responseSignature
    (fun _ p e => letI := p.2.1; letI := p.2.2.1; ScalarResponse p.2.2.2 e)
    (fun e => nomatch e)

def responseRejected : Realization responseSignature.{u} :=
  realize responseSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev responseArena : Arena where
  signature := responseSignature.{u}
  Law R := ∀ {E : Type u} [g : NormedAddCommGroup E] [ip : InnerProductSpace ℝ E]
    {B : E →ₗ[ℝ] E} {e : E} [FiniteDimensional ℝ E] (_hB : B.IsSymmetric),
    HasNonzeroPairing B e ∨ ∃! S, R.readout () ⟨E, g, ip, B⟩ e S

private theorem responseRejected_law : ¬ responseArena.{u}.Law responseRejected.{u} := by
  intro law
  have symm : (LinearMap.id : Line.{u} →ₗ[ℝ] Line.{u}).IsSymmetric := fun _ _ => rfl
  obtain h | ⟨S, h, _⟩ := law (e := unitVector) symm
  · exact ((solvable_iff_no_nonzero_pairing symm).mp ⟨unitVector, rfl⟩) h
  · exact h

def responseSource :
    Registration responseArena.{u} (type_of% @nonzero_pairing_or_unique_scalar.{u}) where
  actual := responseActual.{u}
  bridge := Iff.rfl
  variation := ⟨@nonzero_pairing_or_unique_scalar.{u}, responseRejected.{u}, responseRejected_law.{u}⟩
  sensitivity := sensitivity responseArena.{u}.Law responseActual.{u} responseRejected.{u}
    responseRejected_law.{u}
  dependence := by
    intro i
    refine ⟨⟨Line.{u}, inferInstance, inferInstance, LinearMap.id⟩, unitVector, 0, ?_⟩
    intro h
    have hl := congrFun h 1
    change ScalarResponse LinearMap.id unitVector.{u} 1 =
      ScalarResponse LinearMap.id (0 : Line.{u}) 1 at hl
    have hr := hl.mp identityResponse.{u}
    have bad := hr.2 0 rfl
    simp at bad

abbrev sumSignature :=
  signature (Σ ι : Type u, Fintype ι) (fun p => p.1 → ℝ) (fun _ => ℝ)

def sumActual : Realization sumSignature.{u} :=
  realize sumSignature (fun _ p g => letI := p.2; ∑ i, g i) (fun e => nomatch e)

def sumRejected : Realization sumSignature.{u} :=
  realize sumSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sumArena : Arena where
  signature := sumSignature.{u}
  Law R := ∀ {ι : Type u} {F : ι → Type v} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [index : Fintype ι] [∀ i, FiniteDimensional ℝ (F i)]
    (A : ∀ i, F i →ₗ[ℝ] F i) (_hA : ∀ i, (A i).IsSymmetric) (u : PiLp 2 F),
    (blockDiagonal A).IsSymmetric ∧
    Module.finrank ℝ (LinearMap.ker (blockDiagonal A)) =
      ∑ i, Module.finrank ℝ (LinearMap.ker (A i)) ∧
    (HasNonzeroPairing (blockDiagonal A) u ↔ ∃ i, HasNonzeroPairing (A i) (u i)) ∧
    (∀ g : ι → ℝ, (∀ i, ScalarResponse (A i) (u i) (g i)) →
      ScalarResponse (blockDiagonal A) u (R.readout () ⟨ι, index⟩ (fun i => g i)))

private theorem sumRejected_law : ¬ sumArena.{u,v}.Law sumRejected.{u} := by
  intro law
  let I := ULift.{u} Unit
  let A : I → Line.{v} →ₗ[ℝ] Line.{v} := fun _ => 0
  have child : ∀ i : I, ScalarResponse (A i) 0 0 :=
    fun _ => ⟨⟨0, by simp⟩, fun _ _ => by simp⟩
  have bad := (law A (by intro i; simp [A, LinearMap.IsSymmetric]) 0).2.2.2
    (fun _ => 0) child
  obtain ⟨y, hy⟩ := bad.1
  have h := bad.2 y hy
  change ⟪(0 : PiLp 2 (fun _ : I => Line.{v})), y⟫ = 1 at h
  simp at h

def sumSource :
    Registration sumArena.{u,v} (type_of% @blockDiagonal_states.{u,v}) where
  actual := sumActual.{u}
  bridge := Iff.rfl
  variation := ⟨@blockDiagonal_states.{u,v}, sumRejected.{u}, sumRejected_law.{u,v}⟩
  sensitivity := sensitivity sumArena.{u,v}.Law sumActual.{u} sumRejected.{u}
    sumRejected_law.{u,v}
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Unit, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change (∑ _ : ULift.{u} Unit, (0 : ℝ)) ≠ ∑ _ : ULift.{u} Unit, (1 : ℝ)
    simp

def applicationAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@solvable_iff_no_nonzero_pairing.{u}) (Realization applicationSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.applicationUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.applicationSource
  realizationSource := none
  generated := false
  arena := .source ⟨applicationArena.{u}⟩
  objectArena := .source ⟨applicationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source applicationArena.{u} ⟨applicationSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize applicationSignature.{u} (fun _ p y => letI := p.2.1; letI := p.2.2.1; p.2.2.2 y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg",
        "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def responseAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nonzero_pairing_or_unique_scalar.{u}) (Realization responseSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.responseUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.responseSource
  realizationSource := none
  generated := false
  arena := .source ⟨responseArena.{u}⟩
  objectArena := .source ⟨responseArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source responseArena.{u} ⟨responseSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize responseSignature.{u} (fun _ p e => letI := p.2.1; letI := p.2.2.1; ScalarResponse p.2.2.2 e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sumAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@blockDiagonal_states.{u,v}) (Realization sumSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.sumUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.sumSource
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena.{u,v}⟩
  objectArena := .source ⟨sumArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena.{u,v} ⟨sumSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sumSignature.{u} (fun _ p g => letI := p.2; ∑ i, g i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev symmetrySignature :=
  signature InnerMapData.{u} (fun p => p.1)
    (fun p => letI := p.2.1; letI := p.2.2.1; ℝ → (p.1 →ₗ[ℝ] p.1))

def symmetryActual : Realization symmetrySignature.{u} :=
  realize symmetrySignature
    (fun _ p e => letI := p.2.1; letI := p.2.2.1; update p.2.2.2 e)
    (fun e => nomatch e)

def symmetryRejected : Realization symmetrySignature.{u} :=
  realize symmetrySignature
    (fun _ p _ _ => by
      classical
      letI := p.2.1
      letI := p.2.2.1
      exact if h : ∃ T : p.1 →ₗ[ℝ] p.1, ¬ T.IsSymmetric then h.choose else 0)
    (fun e => nomatch e)

abbrev symmetryArena : Arena where
  signature := symmetrySignature.{u}
  Law R := ∀ {E : Type u} [g : NormedAddCommGroup E] [ip : InnerProductSpace ℝ E]
    {B : E →ₗ[ℝ] E} {e : E} {t : ℝ} (_hB : B.IsSymmetric),
    (R.readout () ⟨E, g, ip, B⟩ e t).IsSymmetric

private theorem symmetryRejected_law : ¬ symmetryArena.{u}.Law symmetryRejected.{u} := by
  classical
  intro law
  let I := ULift.{u} Bool
  let E := EuclideanSpace ℝ I
  let a : E := EuclideanSpace.single ⟨false⟩ 1
  let b : E := EuclideanSpace.single ⟨true⟩ 1
  have existsBad : ∃ T : E →ₗ[ℝ] E, ¬ T.IsSymmetric := by
    refine ⟨(InnerProductSpace.rankOne ℝ a b).toLinearMap, ?_⟩
    intro h
    have hba := h b a
    change ⟪InnerProductSpace.rankOne ℝ a b b, a⟫ =
      ⟪b, InnerProductSpace.rankOne ℝ a b a⟫ at hba
    have haa : ⟪a, a⟫ = 1 := by
      change ⟪EuclideanSpace.single (⟨false⟩ : I) 1, a⟫ = 1
      rw [EuclideanSpace.inner_single_left]
      simp [a]
    have hbb : ⟪b, b⟫ = 1 := by
      change ⟪EuclideanSpace.single (⟨true⟩ : I) 1, b⟫ = 1
      rw [EuclideanSpace.inner_single_left]
      simp [b]
    have hba0 : ⟪b, a⟫ = 0 := by
      change ⟪EuclideanSpace.single (⟨true⟩ : I) 1, a⟫ = 0
      rw [EuclideanSpace.inner_single_left]
      simp [a, PiLp.single_apply, show (⟨true⟩ : I) ≠ ⟨false⟩ by decide]
    simp only [InnerProductSpace.rankOne_apply, hbb, hba0, one_smul, zero_smul,
      inner_zero_right, haa, one_ne_zero] at hba
  have h := law (B := (0 : E →ₗ[ℝ] E)) (e := 0) (t := 0) (by simp [LinearMap.IsSymmetric])
  change (if h : ∃ T : E →ₗ[ℝ] E, ¬ T.IsSymmetric then h.choose else 0).IsSymmetric at h
  rw [dif_pos existsBad] at h
  exact existsBad.choose_spec h

def symmetrySource : Registration symmetryArena.{u} (type_of% @update_symmetric.{u}) where
  actual := symmetryActual.{u}
  bridge := Iff.rfl
  variation := ⟨@update_symmetric.{u}, symmetryRejected.{u}, symmetryRejected_law.{u}⟩
  sensitivity := sensitivity symmetryArena.{u}.Law symmetryActual.{u} symmetryRejected.{u}
    symmetryRejected_law.{u}
  dependence := by
    intro i
    refine ⟨⟨Line.{u}, inferInstance, inferInstance, 0⟩, unitVector, 0, ?_⟩
    intro h
    have he := LinearMap.congr_fun (congrFun h 1) unitVector
    change update 0 unitVector.{u} 1 unitVector = update 0 (0 : Line.{u}) 1 unitVector at he
    simp [update, InnerProductSpace.rankOne_apply, unitPairing, unitVector_ne_zero] at he

def symmetryAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@update_symmetric.{u}) (Realization symmetrySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.symmetryUnit
  realizationName := `Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel.symmetrySource
  realizationSource := none
  generated := false
  arena := .source ⟨symmetryArena.{u}⟩
  objectArena := .source ⟨symmetryArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source symmetryArena.{u} ⟨symmetrySource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize symmetrySignature.{u} (fun _ p e => letI := p.2.1; letI := p.2.2.1; update p.2.2.2 e) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.SymmetricRankOneKernel
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.QuadraticForms.SymmetricRankOneKernel
