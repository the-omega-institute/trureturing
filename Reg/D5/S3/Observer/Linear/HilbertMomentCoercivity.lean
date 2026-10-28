import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.HilbertMomentCoercivity
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

open LeanInformationAudit MeasureTheory Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.HilbertMomentCoercivity
open Reg.Support.RealScalarLift
open scoped BigOperators
open Classical
noncomputable section
universe u v
namespace Reg.D5.S3.Observer.Linear.HilbertMomentCoercivity

namespace Positive
abbrev signature : Signature where
  Params := ℕ
  State N := Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => decide A.PosDef) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, R.readout () N (hilbertMoment N) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  exact Bool.noConfusion hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 1, 0, ?_⟩
  have hz : ¬ (0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    intro h
    have hi := h.diag_pos (i := 0)
    norm_num at hi
  change decide ((1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef) ≠
    decide ((0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)
  simp [Matrix.PosDef.one, hz]

def family : Registration arena (type_of% @hilbertMoment_posDef) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by intro N; simpa [actual, realize] using hilbertMoment_posDef N, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hilbertMoment_posDef)
    (type_of% (realize signature (fun _ _ A => decide A.PosDef) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.HilbertMomentCoercivity.hilbertMoment_posDef.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.HilbertMomentCoercivity.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => decide A.PosDef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.HilbertMomentCoercivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Positive

abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Polynomial

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ t => t ^ 2) (fun e => nomatch e)
def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)
def theoremLaw (R : Realization scalarSignature) : Prop :=
  ∀ {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (N : ℕ) (v : Fin (N + 1) → W),
    0 < hilbertEigenvalue N ∧
    hilbertEigenvalue N * (∑ i, ‖v i‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..1, R.readout () () ‖∑ i : Fin (N + 1), s ^ (i : ℕ) • v i‖

def arena : Arena where
  signature := scalarSignature
  Law := theoremLaw.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (W := ULift.{u} ℝ) 0 (fun _ => 0)).2
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence scalarSignature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @hilbert_polynomial_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hilbert_polynomial_coercivity, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hilbert_polynomial_coercivity.{u})
    (type_of% (realize scalarSignature (fun _ _ t => t ^ 2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.HilbertMomentCoercivity.hilbert_polynomial_coercivity.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.HilbertMomentCoercivity.Polynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ t => t ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.HilbertMomentCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Polynomial

namespace Taylor

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ t => t ^ 2) (fun e => nomatch e)
def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)
def theoremLaw (R : Realization scalarSignature) : Prop :=
  ∀ {𝕜 : Type u} {W : Type v} [RCLike 𝕜]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (N : ℕ) (v : Fin (N + 1) → W) (T : ℝ) (_hT : 0 < T) (_hT1 : T ≤ 1),
    hilbertEigenvalue N * T ^ (2 * N + 1) / (N.factorial : ℝ) ^ 2 *
        (∑ i, ‖v i‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, R.readout () () ‖∑ i : Fin (N + 1),
        (((t ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)) : ℝ) : 𝕜) • v i‖

def arena : Arena where
  signature := scalarSignature
  Law := theoremLaw.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := h (𝕜 := ULift.{u} ℝ) (W := ULift.{v} ℝ) 0 (fun _ => 0) 1 zero_lt_one le_rfl
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence scalarSignature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @taylor_polynomial_energy_floor.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨taylor_polynomial_energy_floor, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@taylor_polynomial_energy_floor.{u,v})
    (type_of% (realize scalarSignature (fun _ _ t => t ^ 2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.HilbertMomentCoercivity.taylor_polynomial_energy_floor.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.HilbertMomentCoercivity.Taylor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ t => t ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.HilbertMomentCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Taylor
end Reg.D5.S3.Observer.Linear.HilbertMomentCoercivity
