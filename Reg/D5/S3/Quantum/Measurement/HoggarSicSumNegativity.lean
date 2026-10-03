import D5.S3.Quantum.Measurement.HoggarSicSumNegativity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity
open _root_.D5.S3.Quantum.Measurement.HoggarSicSumNegativity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 8) (Fin 8) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ρ => sumNegativity ρ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := IsGreatest {r : ℝ | ∃ ρ : Matrix (Fin 8) (Fin 8) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ R.readout () () ρ = r} (7/8)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  rcases h.1 with ⟨ρ, _hρ, _ht, he⟩
  change (0 : ℝ) = 7/8 at he
  norm_num at he

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    rcases result.1 with ⟨ρ, _hρ, _ht, he⟩
    refine ⟨(), 0, ρ, ?_⟩
    change sumNegativity 0 ≠ sumNegativity ρ
    have hzero : sumNegativity (0 : Matrix (Fin 8) (Fin 8) ℂ) = 0 := by
      simp [sumNegativity, negativePart, quasiprobability]
    rw [hzero, he]
    norm_num

register_information_theorem result in arena
  readout via (realize signature (fun _ _ ρ => sumNegativity ρ) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity
    «definition» := some {
      owner := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity
      name := `D5.S3.Quantum.Measurement.HoggarSicSumNegativity.claim }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Quantum.Measurement.HoggarSicSumNegativity
