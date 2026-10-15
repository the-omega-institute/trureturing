import Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness

open scoped ComplexOrder ENNReal
open TraceClassCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness (HilbertInput)
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteCompression

abbrev rangeSignature : Signature where
  Params := HilbertInput.{u}
  State p := Submodule ℂ (TraceClass p.H)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ (TraceClass p.H)
  Anchor := Empty
  finiteAnchor := inferInstance

def rangeActual := realize rangeSignature.{u} (fun _ _ V => V) (fun a => nomatch a)

def rangeLaw (R : Realization rangeSignature.{u}) : Prop :=
  ∀ (p : HilbertInput.{u}) (U : Submodule ℂ p.H) [FiniteDimensional ℂ U],
    FiniteDimensional ℂ (R.readout () p (LinearMap.range (compress U.starProjection).toLinearMap))

theorem range_actual : rangeLaw rangeActual.{u} := by
  intro p U _
  exact finiteDimensional_range U

theorem range_bridge :
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (U : Submodule ℂ H) [FiniteDimensional ℂ U],
      FiniteDimensional ℂ (LinearMap.range (compress U.starProjection).toLinearMap)) ↔
      rangeLaw rangeActual.{u} := by
  constructor
  · intro h p; exact h
  · intro h H _ _ _; exact h ⟨H⟩

abbrev setSignature : Signature where
  Params := HilbertInput.{u}
  State p := Set (TraceClass p.H)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set (TraceClass p.H)
  Anchor := Empty
  finiteAnchor := inferInstance

def setActual := realize setSignature.{u} (fun _ _ K => K) (fun a => nomatch a)

def compactImageLaw (R : Realization setSignature.{u}) : Prop :=
  ∀ (p : HilbertInput.{u}) (U : Submodule ℂ p.H) [FiniteDimensional ℂ U],
    ∃ K : Set (TraceClass p.H), IsCompact (R.readout () p K) ∧
      ∀ rho : TraceClass p.H, ‖rho‖ ≤ 1 → compress U.starProjection rho ∈ R.readout () p K

theorem compactImage_actual : compactImageLaw setActual.{u} := by
  intro p U _
  exact exists_compact_compressions U

theorem compactImage_bridge :
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (U : Submodule ℂ H) [FiniteDimensional ℂ U],
      ∃ K : Set (TraceClass H), IsCompact K ∧
        ∀ rho : TraceClass H, ‖rho‖ ≤ 1 → compress U.starProjection rho ∈ K) ↔
      compactImageLaw setActual.{u} := by
  constructor
  · intro h p; exact h
  · intro h H _ _ _; exact h ⟨H⟩

abbrev errorSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def errorActual := realize errorSignature (fun _ _ z => z) (fun a => nomatch a)

def errorLaw (R : Realization errorSignature) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (F : Finset w) (rho : TraceClass H),
    0 ≤ rho.1 → (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1 →
    R.readout () () ‖rho - compress (finiteSpan b F).starProjection rho‖ ≤
      2 * Real.sqrt (tailMass b F rho)

theorem error_actual : errorLaw.{u} errorActual := by
  intro H _ _ _ w b F rho hrho htrace
  exact norm_sub_compress_le b F rho hrho htrace

theorem error_bridge :
    (∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      {w : Set H} (b : HilbertBasis w ℂ H) (F : Finset w) (rho : TraceClass H),
      0 ≤ rho.1 → (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1 →
      ‖rho - compress (finiteSpan b F).starProjection rho‖ ≤
        2 * Real.sqrt (tailMass b F rho)) ↔ errorLaw.{u} errorActual := Iff.rfl

end Reg.D5.S3.Quantum.Analysis.TraceClass.FiniteCompression
