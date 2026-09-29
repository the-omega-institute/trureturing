import D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
import Reg.Support.DependentFamily

noncomputable section
set_option trace.InformationRegistration.check true

namespace Reg.D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
open MeasureTheory Matrix
open scoped ComplexOrder ComplexConjugate ENNReal
open _root_.D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean Meta LeanInformationAudit

universe u v

attribute [local instance] Matrix.normedAddCommGroup
attribute [local instance] Matrix.seminormedAddCommGroup

local instance matrixMeasurableSpace (I : Type*) : MeasurableSpace (Matrix I I ℂ) :=
  inferInstanceAs (MeasurableSpace (I → I → ℂ))

local instance matrixContinuousENorm (I : Type*) [Fintype I] :
    ContinuousENorm (Matrix I I ℂ) :=
  inferInstanceAs (ContinuousENorm (I → I → ℂ))

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ ρ => ρ) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

def specifiedArena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {H : Type u} {I : Type v} [MeasurableSpace H] [Fintype I]
    (M : PositiveHistoryMeasure H I) (base : Matrix I I ℂ)
    (hbase : Matrix.PosSemidef base) (hbase_trace : Matrix.trace base = 1),
    ∃ ρ : H → Matrix I I ℂ,
      Measurable ρ ∧ Integrable ρ M.traceMeasure ∧
      (∀ h, Matrix.PosSemidef (ρ h) ∧
        Matrix.trace (r.readout () ⟨H, I⟩ ρ h) = 1) ∧
      (∀ s, MeasurableSet s →
        ∀ i j, (∫ h in s, ρ h i j ∂M.traceMeasure) = M.coordinate i j s) ∧
      (∀ f : H → Matrix I I ℂ, Integrable f M.traceMeasure →
        (∀ s, MeasurableSet s →
          ∀ i j, (∫ h in s, f h i j ∂M.traceMeasure) = M.coordinate i j s) →
        f =ᵐ[M.traceMeasure] ρ)

def derivedArena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {H : Type u} {I : Type v} [MeasurableSpace H] [Fintype I]
    (coordinate : I → I → ComplexMeasure H)
    (hpositive : ∀ s, MeasurableSet s →
      Matrix.PosSemidef (fun i j => coordinate i j s : Matrix I I ℂ))
    (base : Matrix I I ℂ) (hbase : Matrix.PosSemidef base)
    (hbase_trace : Matrix.trace base = 1),
    ∃ μ : Measure H, IsFiniteMeasure μ ∧
      (∀ s, MeasurableSet s →
        Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ) =
          ((μ s).toReal : ℂ)) ∧
      ∃ ρ : H → Matrix I I ℂ,
        Measurable ρ ∧ Integrable ρ μ ∧
        (∀ h, Matrix.PosSemidef (ρ h) ∧
          Matrix.trace (r.readout () ⟨H, I⟩ ρ h) = 1) ∧
        (∀ s, MeasurableSet s →
          ∀ i j, (∫ h in s, ρ h i j ∂μ) = coordinate i j s) ∧
        (∀ f : H → Matrix I I ℂ, Integrable f μ →
          (∀ s, MeasurableSet s →
            ∀ i j, (∫ h in s, f h i j ∂μ) = coordinate i j s) →
          f =ᵐ[μ] ρ)

private def zeroHistory : PositiveHistoryMeasure (ULift.{u} Unit) (ULift.{v} (Fin 1)) where
  coordinate := fun _ _ => 0
  traceMeasure := 0
  finite_trace := inferInstance
  positive := by
    intro s hs
    change Matrix.PosSemidef (fun _ _ => (0 : ℂ))
    have hz : (fun _ _ => (0 : ℂ) : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) = 0 := by
      ext i j
      simp
    rw [hz]
    exact Matrix.PosSemidef.zero
  trace_eq := by
    intro s hs
    simp [Matrix.trace, Matrix.diag]

private theorem base_positive : Matrix.PosSemidef
    (1 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) := by
  exact Matrix.PosSemidef.one

private theorem base_trace : Matrix.trace
    (1 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) = 1 := by
  simp

theorem specified_actual_law : specifiedArena.{u,v}.Law actual := by
  intro H I _ _ M base hbase hbase_trace
  exact positive_history_density M base hbase hbase_trace

theorem derived_actual_law : derivedArena.{u,v}.Law actual := by
  intro H I _ _ coordinate hpositive base hbase hbase_trace
  exact positive_history_density_from_coordinates coordinate hpositive base hbase hbase_trace

theorem specified_rejected_law : ¬ specifiedArena.{u,v}.Law rejected := by
  intro h
  obtain ⟨ρ, _, _, hgood, _, _⟩ :=
    h zeroHistory (1 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ)
      base_positive base_trace
  have htrace := (hgood (ULift.up ())).2
  norm_num [rejected, realize, signature] at htrace

theorem derived_rejected_law : ¬ derivedArena.{u,v}.Law rejected := by
  intro h
  have hpositive : ∀ s : Set (ULift.{u} Unit), MeasurableSet s →
      Matrix.PosSemidef (fun _ _ => (0 : ComplexMeasure (ULift.{u} Unit)) s :
        Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) := by
    intro s hs
    change Matrix.PosSemidef (fun _ _ => (0 : ℂ))
    have hz : (fun _ _ => (0 : ℂ) : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) = 0 := by
      ext i j
      simp
    rw [hz]
    exact Matrix.PosSemidef.zero
  obtain ⟨μ, _, _, ρ, _, _, hgood, _, _⟩ :=
    h (fun _ _ => 0) hpositive
      (1 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ)
      base_positive base_trace
  have htrace := (hgood (ULift.up ())).2
  norm_num [rejected, realize, signature] at htrace

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} Unit, ULift.{v} (Fin 1)⟩,
    (fun _ _ _ => (0 : ℂ)), (fun _ _ _ => (1 : ℂ)), ?_⟩
  intro h
  have hentry := congrFun (congrFun (congrFun h (ULift.up ())) (ULift.up 0)) (ULift.up 0)
  exact zero_ne_one hentry

def specifiedRegistration : Registration specifiedArena.{u,v} (specifiedArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨specified_actual_law, rejected, specified_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, specified_rejected_law⟩
      intro j hji
      exact False.elim (hji (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := dependence

def derivedRegistration : Registration derivedArena.{u,v} (derivedArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨derived_actual_law, rejected, derived_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, derived_rejected_law⟩
      intro j hji
      exact False.elim (hji (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
    _root_.D5.S3.Quantum.Measurement.MeasurableInstrumentHistory.positive_history_density_from_coordinates in
    derivedArena
  readout via (realize signature.{u,v} (fun _ _ ρ => ρ) (fun e => nomatch e))
  realizes derivedRegistration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "arg", "fn",
        "arg", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 10 }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Measurement.MeasurableInstrumentHistory
