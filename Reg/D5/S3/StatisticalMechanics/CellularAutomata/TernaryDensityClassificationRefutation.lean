import D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State L := ZMod L → Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ L := ZMod L → Fin 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

/-- The complete negated claim; only the configuration in the hypothesis `∃ i, x i = 0` is
replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ ∀ (L : ℕ) [NeZero L] (x : ZMod L → Fin 3), (∃ i, O.readout () L x i = 0) →
    (rho x ∈ Set.Ico (0 : ℚ) (2 / 3) → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 0) ∧
    (rho x ∈ Set.Ioo (2 / 3 : ℚ) (3 / 4) → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 1) ∧
    (rho x ∈ Set.Ioo (3 / 4 : ℚ) 1 → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro L _ x hx
  obtain ⟨i, hi⟩ := hx
  change (1 : Fin 3) = 0 at hi
  exact absurd hi (by decide)

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, fun _ => 0, fun _ => 1, fun h => ?_⟩
  have := congrFun h 0
  change (0 : Fin 3) = 1 at this
  exact absurd this (by decide)

def registration : Registration arena (¬ claim) where
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
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.result
    in arena
  readout via (realize signature (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
    «definition» := some {
      owner := `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
      name :=
        `D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation.claim
      path := #["arg"] }
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "body", "domain", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
