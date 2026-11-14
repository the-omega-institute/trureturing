import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.EndpointFiniteWindow
import Reg.Support.SingleDependentReadout

noncomputable section

open Matrix Finset Complex MeasureTheory
open _root_.D5.S3.Quantum.Dynamics.EndpointFiniteWindow
open _root_.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Dynamics.EndpointFiniteWindow

namespace Actual

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature {n : ℕ // 1 ≤ n}
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature
  (fun _ p T => T⁻¹ * ∫ t in (0 : ℝ)..T,
    Complex.normSq (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      (centralDefect p.val p.property).map Complex.ofReal)
      (Fin.last (2 * p.val - 1)) 0))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n) (ε T : ℝ), 0 < ε →
    4 * (n : ℝ) / (ε * spectralGap n hn) ≤ T →
      (1 - ε) / (2 * (n : ℝ)) < R.readout () ⟨n, hn⟩ T

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by omega) (1 / 2)
    (4 / ((1 / 2) * spectralGap 1 (by omega))) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let T := 4 / ((1 / 2) * spectralGap 1 (by omega))
  have hh := actual_endpoint_average 1 (by omega) (1 / 2) T
    (by norm_num) (by dsimp [T]; norm_num)
  refine ⟨⟨1, by omega⟩, 0, T, ?_⟩
  change (0 : ℝ)⁻¹ * _ ≠ _
  simp only [inv_zero, zero_mul]
  intro he
  change (1 - 1 / 2) / (2 * (1 : ℝ)) < actual.readout i ⟨1, by omega⟩ T at hh
  rw [← he] at hh
  norm_num at hh

def family : Registration arena (type_of% @actual_endpoint_average) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_endpoint_average, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration (@actual_endpoint_average)
    (Realization signature) (Type) Unit where
  unitName := `D5.S3.Quantum.Dynamics.EndpointFiniteWindow.actual_endpoint_average.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.EndpointFiniteWindow.Actual.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T => T⁻¹ * ∫ t in (0 : ℝ)..T,
      Complex.normSq (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        (centralDefect p.val p.property).map Complex.ofReal)
        (Fin.last (2 * p.val - 1)) 0))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.EndpointFiniteWindow
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Actual


namespace Window

universe u

structure Parameters where
  index : Type u
  finite : Fintype index
  a : index → ℝ
  lam : index → ℝ
  w : index → ℝ
  delta : ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p T => by
    letI := p.finite
    exact T⁻¹ * ∫ t in (0 : ℝ)..T,
      Complex.normSq (∑ i, (p.a i : ℂ) * phase (p.lam i) t))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [f : Fintype ι] (a lam w : ι → ℝ),
    (∀ i, |a i| = w i) → (∑ i, w i) = 1 →
    ∀ {δ T : ℝ}, 0 < δ → 0 < T →
    (∀ i j, i ≠ j → δ ≤ |lam i - lam j|) →
      (∑ i, w i ^ 2) - (2 / (T * δ)) * (1 - ∑ i, w i ^ 2) ≤
        R.readout () ⟨ι, f, a, lam, w, δ⟩ T

private theorem rejected_law : ¬ arena.Law (rejected.{u}) := by
  intro h
  have hh := @h (ULift.{u} Unit) inferInstance (fun _ => 1) (fun _ => 0) (fun _ => 1)
    (by simp) (by simp) 1 1 (by norm_num) (by norm_num)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature (actual.{u}) := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ => 1, 1⟩,
    0, 1, ?_⟩
  norm_num [actual, realize, phase]

def family : Registration arena (type_of% @finite_window_lower_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_window_lower_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration (@finite_window_lower_bound.{u})
    (Realization signature) (Type) Unit where
  unitName := `D5.S3.Quantum.Dynamics.EndpointFiniteWindow.finite_window_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.EndpointFiniteWindow.Window.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p T => by
      letI := p.finite
      exact T⁻¹ * ∫ t in (0 : ℝ)..T,
        Complex.normSq (∑ i, (p.a i : ℂ) * phase (p.lam i) t))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.EndpointFiniteWindow
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Window

end Reg.D5.S3.Quantum.Dynamics.EndpointFiniteWindow
