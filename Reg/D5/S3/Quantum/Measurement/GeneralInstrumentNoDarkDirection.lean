import D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
import Reg.Support.DependentFamily
import Reg.Support.GeneralInstrumentModels

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open Reg.Support.GeneralInstrumentModels
open LeanInformationAudit Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection

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
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : Tendsto (survival Q) atTop (𝓝 F)),
    List.TFAE [darkLayer Q L d = ⊥, F = 0, (R.readout () d (survival Q d)).PosDef,
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 → (ρ * F).trace = 0]

theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp F hF
  exact no_dark_direction_tfae Q L hcomp F hF

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hF : Tendsto (survival (fun _ : Unit => (0 : Matrix (Fin 1) (Fin 1) ℂ)))
      atTop (𝓝 0) := by
    apply (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with n hn
    cases n with
    | zero => omega
    | succ n => exact survival_zero_succ 1 n
  have ht := h (d := 1) (α := Unit) (ι := Unit)
    (fun _ => 0) (fun _ => 1) (complete 1) 0 hF
  have hp : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosDef :=
    (ht.out 0 2).mp (dark_layer_one 1)
  have hq := hp.dotProduct_mulVec_pos (show (1 : Fin 1 → ℂ) ≠ 0 from one_ne_zero)
  simpa using hq

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

register_information_theorem no_dark_direction_tfae in arena
  readout via (realize signature (fun _ d X => (1 : Matrix (Fin d) (Fin d) ℂ) - X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
