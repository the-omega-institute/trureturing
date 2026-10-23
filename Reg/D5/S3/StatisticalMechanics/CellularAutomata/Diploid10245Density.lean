import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The affine density observes the real diploid parameter. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ lam => lam) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete claim, replacing only the numerator λ in its exact-density clause. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ lam ∈ Set.Icc (0 : ℝ) 1,
    CylinderLaw lam ∧
    (∀ t : ℕ, 1 ≤ t →
      d lam t = 1 / ((4 : ℕ) : ℝ) + R.readout () () lam / ((2 : ℕ) : ℝ)) ∧
    Tendsto (fun t : ℕ => d lam t) atTop
      (𝓝 (1 / ((4 : ℕ) : ℝ) + lam / ((2 : ℕ) : ℝ)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 0 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).2.1 1 (by norm_num)
  have hactual := (result 0 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)).2.1 1
    (by norm_num)
  change d 0 1 = 1 / ((4 : ℕ) : ℝ) + 1 / ((2 : ℕ) : ℝ) at hbad
  norm_num at hactual hbad
  linarith

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, zero_ne_one⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.result)
      (type_of% (realize signature (fun _ _ lam => lam) (fun e => nomatch e)))
      Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.result
    "Reg.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density/\
    Reg.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.arena/[anonymous]")
    "__information_unit",
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ lam => lam) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density,
    definition := some {
      owner := `D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density,
      name := `D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "body", "body", "arg",
        "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.CellularAutomata.Diploid10245Density
