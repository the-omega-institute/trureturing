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

abbrev finiteSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ _ ρ => delta ρ) (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev finiteArena : Arena where
  signature := finiteSignature
  Law R := ∀ (σ ρ : ℝ) (_hs : σ=1 ∨ σ= -1) (_hρ : ρ≠0),
    FrameOrthonormal ∧ 0 < R.readout () () ρ ∧ 0 < epsilon ρ ∧
    vectorPhi (xi σ ρ (epsilon ρ)) 1 =
      ((1+epsilon ρ^2*(1+theta ρ^2) : ℝ) : ℂ) ∧
    0 < delta ρ^2/(4*bigM ρ) ∧
    delta ρ^2/(4*bigM ρ) ≤
      |read (vectorPhi (xi σ ρ (epsilon ρ))) (L σ ρ 0)| -
        Real.sqrt (B (vectorPhi (xi σ ρ (epsilon ρ))) (Rp σ 0) (Sp σ ρ 0)) -
        Real.sqrt (B (vectorPhi (xi σ ρ (epsilon ρ))) (Rm σ 0) (Sm σ ρ 0))

private theorem finite_rejected_law : ¬ finiteArena.Law finiteRejected := by
  intro hh
  have bad := (hh 1 1 (Or.inl rfl) (by norm_num)).2.1
  exact (lt_irrefl (0 : ℝ)) bad

private theorem finite_dependence : ObservationalDependence finiteSignature finiteActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hz : delta 0 = 0 := by norm_num [delta,lam,amp,dd,ee,theta,Real.sqrt_div]
  have hp := (exact_finite_witness 1 1 (Or.inl rfl) (by norm_num)).2.1
  change delta 0 ≠ delta 1
  rw [hz]
  exact ne_of_lt hp

def finiteFamily : Registration finiteArena (type_of% @exact_finite_witness) where
  actual := finiteActual
  bridge := Iff.rfl
  variation := ⟨exact_finite_witness, finiteRejected, finite_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, finite_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := finite_dependence

def finiteRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exact_finite_witness) (Realization finiteSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.BalancedStarRigidity.exact_finite_witness.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.BalancedStarRigidity.finiteFamily
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature (fun _ _ ρ => delta ρ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.BalancedStarRigidity
    definition := some {
      owner := `D5.S3.Quantum.Algebra.BalancedStarRigidity
      name := `D5.S3.Quantum.Algebra.BalancedStarRigidity.ExactFiniteWitness
      path := #["body", "body", "body", "body"] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Algebra.BalancedStarRigidity
