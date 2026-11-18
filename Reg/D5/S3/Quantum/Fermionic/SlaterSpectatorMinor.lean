import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
open _root_.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix

universe u
noncomputable section

abbrev Params := Σ ι : Type u, Σ _ : LinearOrder ι, Σ _ : ℕ, Σ _ : ι, Finset ι

abbrev signature : Signature where
  Params := Params.{u}
  State θ := Matrix θ.1 (Fin θ.2.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ ⟨ι, order, k, p, S⟩ V =>
    @occupiedMinor ι order (k + 1) (@appendOrbital ι order k V p) S) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [order : LinearOrder ι] {k : ℕ}
      (V : Matrix ι (Fin k) ℂ) (p : ι) (S : Finset ι),
    R.readout () ⟨ι, order, k, p, S⟩ V =
      if p ∈ S then (-1 : ℂ) ^ (S.filter (p < ·)).card * occupiedMinor V (S.erase p) else 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h (ι := ULift.{u} Unit) (k := 0) 0 ⟨()⟩ ∅
  norm_num [rejected, realize] at hbad

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let order : LinearOrder (ULift.{u} (Fin 2)) := inferInstance
  let : DecidableEq (ULift.{u} (Fin 2)) := order.toDecidableEq
  let p : ULift.{u} (Fin 2) := ⟨0⟩
  let q : ULift.{u} (Fin 2) := ⟨1⟩
  let S : Finset (ULift.{u} (Fin 2)) := {p, q}
  have hpq : p ≠ q := by decide
  have hp : p ∈ S := by simp [S]
  have hS : S.erase p = {q} := by simp [S, hpq]
  let V₀ : Matrix (ULift.{u} (Fin 2)) (Fin 1) ℂ := 0
  let V₁ : Matrix (ULift.{u} (Fin 2)) (Fin 1) ℂ := fun _ _ => 1
  refine ⟨⟨ULift.{u} (Fin 2), inferInstance, 1, p, S⟩, V₀, V₁, ?_⟩
  change occupiedMinor (appendOrbital V₀ p) S ≠ occupiedMinor (appendOrbital V₁ p) S
  rw [occupiedMinor_append V₀, occupiedMinor_append V₁]
  simp only [hp, ite_true]
  have h₀ : occupiedMinor V₀ {q} = 0 := by simp [occupiedMinor, V₀]
  have h₁ : occupiedMinor V₁ {q} = 1 := by
    unfold occupiedMinor
    rw [dite_eq_left (Finset.card_singleton q), Matrix.det_fin_one]
    rfl
  rw [hS, h₀, h₁, mul_zero, mul_one]
  exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)).symm

def source_registration : Registration arena.{u} (type_of% (@occupiedMinor_append.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@occupiedMinor_append.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := actual_dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@occupiedMinor_append.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.occupiedMinor_append.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ⟨ι, order, k, p, S⟩ V =>
    @occupiedMinor ι order (k + 1) (@appendOrbital ι order k V p) S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
    definition := none
    coordinates := #[0, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor

namespace Reg.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.FiniteExtension

open _root_.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
universe u
noncomputable section

abbrev Parameters := Σ ι : Type u, Σ _ : LinearOrder ι, Σ _ : ℕ, Σ _ : Finset ι, Finset ι

abbrev signature : Signature where
  Params := Parameters.{u}
  State θ := Matrix θ.1 (Fin (θ.2.2.1 + θ.2.2.2.1.card)) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ ⟨ι, order, k, T, S⟩ W =>
    @occupiedMinor ι order (k + T.card) W S) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [order : LinearOrder ι] {k : ℕ} [Fintype ι]
      (V : Matrix ι (Fin k) ℂ) (_hV : V.conjTranspose * V = 1) (T : Finset ι)
      (_hT : ∀ p ∈ T, ∀ j, V p j = 0),
    ∃ W : Matrix ι (Fin (k + T.card)) ℂ, W.conjTranspose * W = 1 ∧
      (∀ q ∉ T, (∀ j, V q j = 0) → ∀ j, W q j = 0) ∧
      ∀ S : Finset ι, R.readout () ⟨ι, order, k, T, S⟩ W =
        if T ⊆ S then
          (-1 : ℂ) ^ (∑ p ∈ T, ((S \ T).filter (p < ·)).card) * occupiedMinor V (S \ T)
        else 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V : Matrix (ULift.{u} Unit) (Fin 0) ℂ := 0
  have hv : Vᴴ * V = 1 := Subsingleton.elim _ _
  obtain ⟨W, _, _, hlaw⟩ := h V hv ∅ (by simp)
  have hbad := hlaw ∅
  norm_num [rejected, realize, occupiedMinor] at hbad

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let q : ULift.{u} Unit := ⟨()⟩
  let V₀ : Matrix (ULift.{u} Unit) (Fin 1) ℂ := 0
  let V₁ : Matrix (ULift.{u} Unit) (Fin 1) ℂ := fun _ _ => 1
  refine ⟨⟨ULift.{u} Unit, inferInstance, 1, ∅, {q}⟩, V₀, V₁, ?_⟩
  change occupiedMinor V₀ {q} ≠ occupiedMinor V₁ {q}
  have h₀ : occupiedMinor V₀ {q} = 0 := by simp [occupiedMinor, V₀]
  have h₁ : occupiedMinor V₁ {q} = 1 := by
    unfold occupiedMinor
    rw [dite_eq_left (Finset.card_singleton q), Matrix.det_fin_one]
    rfl
  rw [h₀, h₁]
  exact zero_ne_one

def source_registration : Registration arena.{u} (type_of% (@extend_ordered_spectators.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@extend_ordered_spectators.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@extend_ordered_spectators.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.extend_ordered_spectators.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.FiniteExtension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ⟨ι, order, k, T, S⟩ W =>
    @occupiedMinor ι order (k + T.card) W S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.SlaterSpectatorMinor
    definition := none
    coordinates := #[0, 2, 6, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.Fermionic.SlaterSpectatorMinor.FiniteExtension
