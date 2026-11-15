import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Analysis.ConcreteCoefficientSeries

/-! Exact full-telescope source reconstructions for the standard-predual bridge.
The four-slot source-selection certification is unfinished under
https://github.com/the-omega-institute/trureturing/issues/29713.
Compiled source equality is not a validated escape registration. -/

open Set Filter Topology MeasureTheory LeanInformationAudit
open scoped ComplexOrder InnerProductSpace
open _root_.D5.S3.Quantum.Analysis.NormalFunctionals
open _root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
open _root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries

def series_mem_coefficientSpace_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ {φ : StrongDual ℂ M.toStarSubalgebra}
    (hφ : IsCoefficientSeries M φ),
    φ ∈ coefficientSpace M

theorem series_mem_coefficientSpace_source : series_mem_coefficientSpace_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries.series_mem_coefficientSpace

def series_order_normal_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ {φ : StrongDual ℂ M.toStarSubalgebra}
    (hφ : IsCoefficientSeries M φ),
    IsOrderNormal φ

theorem series_order_normal_source : series_order_normal_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries.series_order_normal

def dual_evaluation_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (Λ : StrongDual ℂ (coefficientSpace M)),
    ∃ a : M.toStarSubalgebra, (∀ φ : coefficientSpace M, Λ φ = φ.val a) ∧ ‖a‖ = ‖Λ‖

theorem dual_evaluation_source : dual_evaluation_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries.dual_evaluation

def closure_convex_coefficientBall_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  closure (convexHull ℝ ({φ : coefficientSpace M | ∃ ξ η : H, φ.val = coefficient M ξ η ∧ ‖ξ‖ * ‖η‖ ≤ 1})) = Metric.closedBall (0 : coefficientSpace M) 1

theorem closure_convex_coefficientBall_source : closure_convex_coefficientBall_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries.closure_convex_coefficientBall

def coefficientSpace_series_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (φ : coefficientSpace M),
    IsCoefficientSeries M φ.val

theorem coefficientSpace_series_source : coefficientSpace_series_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries.coefficientSpace_series

def mem_coefficientSpace_iff_series_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (φ : StrongDual ℂ M.toStarSubalgebra),
    φ ∈ coefficientSpace M ↔ IsCoefficientSeries M φ

theorem mem_coefficientSpace_iff_series_source : mem_coefficientSpace_iff_series_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries.mem_coefficientSpace_iff_series

end Reg.D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
