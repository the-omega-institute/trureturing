import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber

/-! Source-bound equality observations and the normalized rank-certificate
readout. Each law preserves the complete source telescope and local fibers. -/

noncomputable section
open Set Matrix MvPolynomial LeanInformationAudit
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Word)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber

namespace MatrixEvaluation
abbrev Value := Matrix (Word 2) (Word 2) ℂ
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Value) (fun _ => Value → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (x : Coordinates), 0 ≤ sigma x →
    R.readout () () ((q2Polynomial m).map (eval (fun i => (x i : ℂ))))
      (density m (positiveRepresentative x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (le_refl 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  change ((0 : Value) = 0) = ((1 : Value) = 0) at hh
  exact one_ne_zero (Eq.mp hh rfl)

def family : Registration arena (type_of% (@q2Polynomial_eval)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@q2Polynomial_eval, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q2Polynomial_eval) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber.MatrixEvaluation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber.MatrixEvaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end MatrixEvaluation

namespace RecordEvaluation
abbrev Value := Fin 12 → ℝ
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Value) (fun _ => Value → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (x : Coordinates), 0 ≤ sigma x →
    R.readout () () (fun j => eval x (recordPolynomial m j))
      (recordEquiv (record m (positiveRepresentative x)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (le_refl 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  change ((0 : Value) = 0) = ((1 : Value) = 0) at hh
  exact one_ne_zero (Eq.mp hh rfl)

def family : Registration arena (type_of% (@recordPolynomial_eval)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recordPolynomial_eval, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@recordPolynomial_eval) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber.RecordEvaluation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber.RecordEvaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end RecordEvaluation

namespace Fibers
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Coordinates (fun _ => RealPoly) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ a p => eval a p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ,
    ∃ D : RealPoly, D ≠ 0 ∧ (∃ a₀ : Coordinates, R.readout () a₀ D = 1) ∧
      IsOpen (validityDomain k) ∧ (validityDomain k).Nonempty ∧
      IsOpen (genericLocus k D) ∧ (genericLocus k D).Nonempty ∧
      Dense {x : validityDomain k | eval (x : Coordinates) D ≠ 0} ∧
      ∀ x ∈ genericLocus k D, ∀ U : Set Coordinates, IsOpen U → x ∈ U →
        U ⊆ validityDomain k →
        ∃ (K : Submodule ℝ Coordinates) (q : Coordinates →L[ℝ] K)
          (f : K → Coordinates) (ε : ℝ),
          0 < ε ∧ 0 < Module.finrank ℝ K ∧
          Module.finrank ℝ K + Module.finrank ℝ (LinearMap.range
            (fderiv ℝ (fun y j => eval y (recordPolynomial (1 + k) j)) x).toLinearMap) = 13 ∧
          f 0 = x ∧ ContDiffOn ℝ 1 f (Metric.ball 0 ε) ∧
          (∀ z ∈ Metric.ball 0 ε,
            f z ∈ U ∩ genericLocus k D ∧
            density (1 + k) (positiveRepresentative (f z)) =
              density (1 + k) (positiveRepresentative x) ∧
            q (f z - x) = z ∧
            (z ≠ 0 → ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
              state (3 + k) (positiveRepresentative (f z)) =
                ζ • state (3 + k) (positiveRepresentative x))) ∧
          ∃ y ∈ U ∩ genericLocus k D, y ≠ x ∧
            density (1 + k) (positiveRepresentative y) =
              density (1 + k) (positiveRepresentative x) ∧
            ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ state (3 + k) (positiveRepresentative y) =
              ζ • state (3 + k) (positiveRepresentative x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨D, _, ⟨a, ha⟩, _⟩ := h 0
  exact zero_ne_one ha

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change eval (0 : Coordinates) (0 : RealPoly) ≠ eval 0 1
  simp

def family : Registration arena (type_of% (@exists_generic_fiber)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_generic_fiber, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_generic_fiber) (Realization signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber.Fibers.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber.Fibers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a p => eval a p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Fibers

end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
