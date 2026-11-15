import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Analysis.ConcreteCoefficientPredual

/-! Exact full-telescope source reconstructions for the standard-predual bridge.
The four-slot source-selection certification is unfinished under
https://github.com/the-omega-institute/trureturing/issues/29713.
Compiled source equality is not a validated escape registration. -/

open Set Filter Topology MeasureTheory LeanInformationAudit
open scoped ComplexOrder InnerProductSpace
open _root_.D5.S3.Quantum.Analysis.NormalFunctionals
open _root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
universe v
namespace Reg.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual

def leftTranslate_mem_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (b : M.toStarSubalgebra)
    {φ : StrongDual ℂ M.toStarSubalgebra} (hφ : φ ∈ coefficientSpace M),
    leftTranslate b φ ∈ coefficientSpace M

theorem leftTranslate_mem_source : leftTranslate_mem_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.leftTranslate_mem

def positive_mem_of_domination_statement : Prop :=
  ∀ {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
  ∀ (E : Submodule ℂ (StrongDual ℂ A)) (hE : IsClosed (E : Set (StrongDual ℂ A)))
    (hstable : ∀ b : A, ∀ φ ∈ E, leftTranslate b φ ∈ E)
    (φ ψ : StrongDual ℂ A) (hφ : φ ∈ E)
    (hφpos : ∀ a : A, 0 ≤ a → 0 ≤ φ a)
    (hψ : ∀ a : A, 0 ≤ a → 0 ≤ ψ a ∧ ψ a ≤ φ a),
    ψ ∈ E

theorem positive_mem_of_domination_source : positive_mem_of_domination_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.positive_mem_of_domination

def coefficientSpace_hereditary_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (φ ψ : StrongDual ℂ M.toStarSubalgebra)
    (hφ : φ ∈ coefficientSpace M) (hφpos : ∀ a, 0 ≤ a → 0 ≤ φ a)
    (hψ : ∀ a, 0 ≤ a → 0 ≤ ψ a ∧ ψ a ≤ φ a),
    ψ ∈ coefficientSpace M

theorem coefficientSpace_hereditary_source : coefficientSpace_hereditary_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.coefficientSpace_hereditary

def posterior_L1_range_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ {ρ σ : StrongDual ℂ M.toStarSubalgebra}
    (hu : ρ + σ ∈ coefficientSpace M) (F : _root_.D5.S3.Quantum.Analysis.NormalMomentFamily.Family ρ σ)
    (Γ : (_root_.D5.S3.Quantum.Analysis.NormalMomentFamily.Interval →₁[_root_.D5.S3.Quantum.Analysis.NormalMomentFamily.scalarMeasure F] ℂ) →L[ℂ]
      StrongDual ℂ M.toStarSubalgebra)
    (hagree : ∀ g : C(_root_.D5.S3.Quantum.Analysis.NormalMomentFamily.Interval, ℂ),
      Γ (ContinuousMap.toLp 1 (_root_.D5.S3.Quantum.Analysis.NormalMomentFamily.scalarMeasure F) ℂ g) =
        _root_.D5.S3.Quantum.Analysis.NormalMomentFamily.linearMap F g),
    ∀ h, Γ h ∈ coefficientSpace M

theorem posterior_L1_range_source : posterior_L1_range_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.posterior_L1_range

def internal_lub_strong_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (s : Set M.toStarSubalgebra) (a : M.toStarSubalgebra)
    (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ x ∈ s, 0 ≤ x) (ha : IsLUB s a),
    letI : Nonempty s := hs.to_subtype
    letI : IsDirectedOrder s := ⟨fun i j => by
      obtain ⟨k, hk, hik, hjk⟩ := hd i i.property j j.property
      exact ⟨⟨k, hk⟩, hik, hjk⟩⟩
    ∀ v : H, Tendsto (fun x : s => (x.val : H →L[ℂ] H) v) atTop
      (𝓝 ((a : H →L[ℂ] H) v))

theorem internal_lub_strong_source : internal_lub_strong_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.internal_lub_strong

def coefficient_order_normal_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  ∀ (ξ η : H),
    IsOrderNormal (coefficient M ξ η)

theorem coefficient_order_normal_source : coefficient_order_normal_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.coefficient_order_normal

def coefficientSpace_le_normalDual_statement : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H),
  coefficientSpace M ≤ normalDual

theorem coefficientSpace_le_normalDual_source : coefficientSpace_le_normalDual_statement.{v} :=
  @_root_.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual.coefficientSpace_le_normalDual

end Reg.D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
