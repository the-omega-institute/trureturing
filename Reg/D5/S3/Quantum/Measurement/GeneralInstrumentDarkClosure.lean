import D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
import Reg.Support.DependentFamily
import Reg.Support.GeneralInstrumentModels

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open Reg.Support.GeneralInstrumentModels
open LeanInformationAudit Matrix Filter Topology
open scoped ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d X => (1 : Matrix (Fin d) (Fin d) ℂ) - X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (Q : α → Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1),
    (∀ n, darkLayer Q L n = LinearMap.ker (R.readout () d (survival Q n)).mulVecLin) ∧
      (∀ n, d ≤ n → darkLayer Q L n = darkLayer Q L d) ∧
      (∀ i, ∀ v ∈ darkLayer Q L d, (L i).mulVec v = 0) ∧
      (∀ a, ∀ v ∈ darkLayer Q L d, (Q a).mulVec v ∈ darkLayer Q L d) ∧
      ∀ V : Submodule ℂ (Fin d → ℂ), (∀ i, ∀ v ∈ V, (L i).mulVec v = 0) →
        (∀ a, ∀ v ∈ V, (Q a).mulVec v ∈ V) → V ≤ darkLayer Q L d

theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp
  exact darkLayer_closure Q L hcomp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (d := 1) (α := Unit) (ι := Unit)
    (fun _ => 0) (fun _ => 1) (complete 1)).1 1
  have he : (⊥ : Submodule ℂ (Fin 1 → ℂ)) = ⊤ := by
    simpa [rejected, realize, dark_layer_one, Matrix.mulVecLin_zero] using hb
  exact bot_ne_top he

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [actual, realize] at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem darkLayer_closure in arena
  readout via (realize signature (fun _ d X => (1 : Matrix (Fin d) (Fin d) ℂ) - X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
