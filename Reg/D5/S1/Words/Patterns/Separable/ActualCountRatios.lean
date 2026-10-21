import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.ActualCountRatios
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios
open _root_.D5.S1.Words.Patterns.Separable.ActualCountRatios
open _root_.D5.S1.Words.Patterns.Separable.CutFactorization
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => nhds z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ shift : ℕ, Tendsto (fun n : ℕ =>
    (Nat.card (Avoider (n - shift)) : ℝ) / Nat.card (Avoider n))
      atTop (R.readout () () (rho ^ shift))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  exact Filter.atTop_neBot.ne (Filter.tendsto_bot_right_iff.mp (law 0))

def family : Registration arena (type_of% @actual_fixed_shift_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_fixed_shift_ratio, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    exact nhds_injective.ne (by norm_num)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_fixed_shift_ratio) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => nhds z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.ActualCountRatios
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios

namespace Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios.CriticalMass
open _root_.D5.S1.Words.Patterns.Separable.CutFactorization
open _root_.D5.S1.Words.Patterns.Separable.MinimumCutKernel
open _root_.D5.S1.Words.Patterns.Separable.OccupiedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ∑' n, z n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ z => (∑' n, z n) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Summable shapeWeight ∧
    R.readout () () (fun n => shapeWeight n) = b ∧ Summable kernelWeight ∧
    (∑' n, kernelWeight n) = (1 / 2 : ℝ) ∧
    Summable (fun n : ℕ => rho ^ (n + 1) *
      (Nat.card (Indecomposable false (n + 1)) : ℝ)) ∧
    (∑' n : ℕ, rho ^ (n + 1) *
      (Nat.card (Indecomposable false (n + 1)) : ℝ)) = ceiling ∧
    (∀ n : ℕ, rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ) =
      (kernelWeight n + (if n = 0 then rho / 2 else 0)) / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have same := law.2.1
  change (∑' n, shapeWeight n) + 1 = b at same
  have original := critical_shape_masses.2.1
  linarith

def family : Registration arena (type_of% @critical_shape_masses) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨critical_shape_masses, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℕ => (0 : ℝ)),
      (fun n : ℕ => if n = 0 then (1 : ℝ) else 0), ?_⟩
    change (∑' _ : ℕ, (0 : ℝ)) ≠ ∑' n : ℕ, if n = 0 then (1 : ℝ) else 0
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@critical_shape_masses) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios.CriticalMass.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios.CriticalMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ∑' n, z n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.ActualCountRatios
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S1.Words.Patterns.Separable.ActualCountRatios.CriticalMass
