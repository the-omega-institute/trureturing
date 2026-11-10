import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.BalancedStarRigidity
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.BalancedStarRigidity

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.BalancedStarRigidity

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have he' := congrFun he 0
  have hh : (1 : ℝ) = 0 := Eq.mp he' rfl
  norm_num at hh

abbrev zeroArena : Arena where
  signature := signature
  Law R := ∀ (σ ρ : ℝ) (_hs : σ = 1 ∨ σ = -1)
    (_hb : ZeroBudget σ ρ), R.readout () () ρ 0

private theorem rejected_zero : ¬ zeroArena.Law rejected := by
  intro hh
  have hb := (full_equivalence 1 0 (Or.inl rfl)).1.mp rfl
  have hz : CornerSA (0 : A) := ⟨by simp, by simp⟩
  exact hh 1 0 (Or.inl rfl) (hb.2 0 hz)

def zeroFamily : Registration zeroArena (type_of% @zero_probe_forces_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zero_probe_forces_zero, rejected, rejected_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_zero⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

abbrev equivalenceArena : Arena where
  signature := signature
  Law R := ∀ (σ ρ : ℝ) (_hs : σ = 1 ∨ σ = -1),
    (R.readout () () ρ 0 ↔ AllBudgets σ ρ) ∧ (AllBudgets σ ρ ↔ ZeroBudget σ ρ)

private theorem rejected_equivalence : ¬ equivalenceArena.Law rejected := by
  intro hh
  have hb := (full_equivalence 1 0 (Or.inl rfl)).1.mp rfl
  exact (hh 1 0 (Or.inl rfl)).1.mpr hb

def equivalenceFamily : Registration equivalenceArena (type_of% @full_equivalence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_equivalence, rejected, rejected_equivalence⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_equivalence⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def zeroRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zero_probe_forces_zero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.BalancedStarRigidity.zero_probe_forces_zero.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.BalancedStarRigidity.zeroFamily
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena⟩
  objectArena := .source ⟨zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena ⟨zeroFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.BalancedStarRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def equivalenceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@full_equivalence) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.BalancedStarRigidity.full_equivalence.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.BalancedStarRigidity.equivalenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨equivalenceArena⟩
  objectArena := .source ⟨equivalenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equivalenceArena ⟨equivalenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.BalancedStarRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end Reg.D5.S3.Quantum.Algebra.BalancedStarRigidity
