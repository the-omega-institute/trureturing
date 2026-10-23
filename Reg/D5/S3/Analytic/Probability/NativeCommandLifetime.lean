
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Analytic.Probability.NativeCommandLifetime

/-! Source-bound audit of the complete native lifetime theorem. -/

noncomputable section
open Set MeasureTheory LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.Analytic.Probability.NativeCommandLifetime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Probability.NativeCommandLifetime

def witnessModel : Model where
  r := 1/2
  l := 1/16
  u := 3/16
  r_pos := by norm_num
  lower_pos := by norm_num
  interval_nonempty := by norm_num
  upper_lt := by norm_num
  source := ![1/8,0,0]
  source_height := by norm_num
  rho := fun _ => 1
  A := fun _ => 1
  neighbourhood := univ
  open_neighbourhood := isOpen_univ
  contains_cylinder := by intros; trivial
  smooth_rho := contDiffOn_const
  smooth_A := by intros; exact contDiffOn_const
  positive_rho := by intros; norm_num
  positive_A := by intros; exact Matrix.PosDef.one
  periodic_rho := by intros; rfl
  periodic_A := by intros; rfl

example : _root_.D5.S3.Quantum.Fibers.FiniteRectangleTransport.ValidBase
    (nativeBase witnessModel) := by
  norm_num [nativeBase,witnessModel,
    _root_.D5.S3.Quantum.Fibers.FiniteRectangleTransport.ValidBase]

@[reducible] def signature : Signature where
  Params := Σ _ : Model, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => tailProbability p.1 p.2 t) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ B : Model,
    ∃ h M : ℝ, ∃ n₀ : ℕ, 0 < h ∧ 0 < M ∧ 1 ≤ n₀ ∧
      ∀ n ≥ n₀,
        (∀ t : ℝ, 0 ≤ t →
          R.readout () ⟨B,n⟩ t ≤ (1/2:ℝ)^⌊max (t-1) 0/h⌋₊) ∧
        (∀ R : ℝ, 1 ≤ R →
          excessExpectation B n R ≤ 2*h*(1/2:ℝ)^⌊(R-1)/h⌋₊) ∧
        (∀ w : Fin (n^3) → SignPair,
          0 < zeta B n w ∧ zeta B n w ≤ ((n^3:ℕ)+1:ℝ)*mesh n ∧
          ∀ T : ℝ, 0 ≤ T →
            D5.S3.Quantum.Fibers.OriginalControlComposition.OriginalControl (nativeBase B) T
              (fun t => (heldState B n w t).1)
              (fun t => command B n w t 1) ∧
            commandArea B n w T = command B n w T 2 ∧
            heldState B n w T = physicalState B (command B n w T))

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨h,M,n₀,hh,hM,hn₀,he⟩ := h witnessModel
  have hb := (he n₀ le_rfl).1 0 (by norm_num)
  norm_num [rejected,realize] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨h,M,n₀,hh,hM,hn₀,he⟩ := actual_lifetime_estimates witnessModel
  have hw := (he n₀ le_rfl).2.2
  let T : ℝ := ((n₀^3:ℕ)+1:ℝ)*mesh n₀
  have hzero : tailProbability witnessModel n₀ 0 = 1 := by
    have hind : (fun w : Fin (n₀^3) → SignPair =>
        if (0:ℝ) < zeta witnessModel n₀ w then (1:ℝ) else 0) = fun _ => 1 := by
      funext w
      exact if_pos (hw w).1
    unfold tailProbability
    rw [hind]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool]
    simp only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
    rw [←mul_pow]
    norm_num
  have hT : tailProbability witnessModel n₀ T = 0 := by
    unfold tailProbability
    suffices (∑ w : Fin (n₀^3) → SignPair, if T < zeta witnessModel n₀ w then
        (1:ℝ) else 0) = 0 by rw [this,mul_zero]
    apply Finset.sum_eq_zero
    intro w _
    exact if_neg (not_lt.mpr (hw w).2.1)
  refine ⟨⟨witnessModel,n₀⟩,0,T,?_⟩
  change tailProbability witnessModel n₀ 0 ≠ tailProbability witnessModel n₀ T
  rw [hzero,hT]
  norm_num

def family : Registration arena (type_of% (@actual_lifetime_estimates)) where
  actual := realize signature (fun _ p t => tailProbability p.1 p.2 t) Empty.elim
  bridge := Iff.rfl
  variation := ⟨actual_lifetime_estimates,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_lifetime_estimates) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Probability.NativeCommandLifetime.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.NativeCommandLifetime.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => tailProbability p.1 p.2 t) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.NativeCommandLifetime
    definition := none
    coordinates := #[0,4]
    readouts := #[{
      path := #["body","arg","body","arg","body","arg","body","arg","arg","arg",
        "body","body","fn","arg","body","body","fn","arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

#print axioms _root_.D5.S3.Analytic.Probability.NativeCommandLifetime.actual_lifetime_estimates

end Reg.D5.S3.Analytic.Probability.NativeCommandLifetime
