import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fibers.MeasurableRankOneControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix ComplexOrder ENNReal ProbabilityTheory
namespace Reg.D5.S3.Quantum.Fibers.MeasurableRankOneControl

open MeasureTheory ProbabilityTheory
open _root_.D5.S3.Quantum.Fibers.RankOneFeedbackProtocol
open _root_.D5.S3.Quantum.Fibers.MeasurableRankOneControl
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u v

structure Parameters where
  index : Type u
  finite : Fintype index
  decidable : DecidableEq index
  U : NNReal → Matrix index index ℂ
  zero : letI := finite; letI := decidable; U 0 = 1
  add : letI := finite; letI := decidable; ∀ t w, U (t + w) = U w * U t
  unitary : letI := finite; letI := decidable; ∀ t, (U t)ᴴ * U t = 1

abbrev Parameters.menu (p : Parameters.{u}) :=
  letI := p.finite
  letI := p.decidable
  unitaryMenu p.U p.zero p.add p.unitary

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := by
    letI := p.finite
    letI := p.decidable
    exact Density p.index
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI := p.finite
    letI := p.decidable
    exact (R : Control.{u, v} p.menu) → Measure (R.Seed × List p.index)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization (signature.{u, v}) := realize signature
  (fun _ p X => by
    letI := p.finite
    letI := p.decidable
    exact fun R => jointLaw p.menu R X) (fun e => nomatch e)

def rejected : Realization (signature.{u, v}) := realize signature
  (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ p : Parameters.{u},
    letI := p.finite
    letI := p.decidable
    ∀ X Y : Density p.index,
      (⨆ C : Control.{u, v} p.menu,
        measurableTotalVariation (R.readout () p X C) (R.readout () p Y C)) =
        ENNReal.ofReal (firstSup p.menu X.val Y.val)

private theorem bridge :
    (type_of% (@arbitrary_protocol_tv_supremum.{u, v})) ↔ (arena.{u, v}).Law actual := by
  constructor
  · intro h p
    letI := p.finite
    letI := p.decidable
    exact h p.U p.zero p.add p.unitary
  · intro h n finite decidable U hzero hadd hunitary X Y
    exact h ⟨n,finite,decidable,U,hzero,hadd,hunitary⟩ X Y

private abbrev testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 2), inferInstance, inferInstance, fun _ => 1,
    rfl, by intros; simp, by intros; simp⟩

private def testDensity (b : Fin 2) : Density (ULift.{u} (Fin 2)) :=
  ⟨Matrix.diagonal (fun i => if i.down = b then 1 else 0), by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ if i.down = b then 1 else 0
    split_ifs <;> simp, by
    simp only [Matrix.trace_diagonal]
    rw [← Equiv.ulift.symm.sum_comp]
    fin_cases b <;> norm_num [Fin.sum_univ_two]⟩

private theorem test_first_sup :
    ENNReal.ofReal (firstSup testParameters.menu
      (testDensity.{u} 0).val (testDensity.{u} 1).val) = 1 := by
  simp only [firstSup, testParameters, Parameters.menu, unitaryMenu,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one, Set.range_const, csSup_singleton]
  unfold totalVariation testDensity
  simp only [Matrix.diagonal_apply_eq]
  rw [← Equiv.ulift.symm.sum_comp]
  norm_num [Fin.sum_univ_two]

private theorem rejected_law : ¬ (arena.{u, v}).Law rejected := by
  intro h
  have he := h testParameters (testDensity 0) (testDensity 1)
  simp only [rejected, realize, measurableTotalVariation, zero_apply,
    tsub_self, max_self, ENNReal.iSup_zero] at he
  rw [test_first_sup] at he
  exact zero_ne_one he

private theorem dependence : ObservationalDependence (signature.{u, v}) actual := by
  intro i
  refine ⟨testParameters, testDensity 0, testDensity 1, ?_⟩
  intro he
  have hh := bridge.mp (@arbitrary_protocol_tv_supremum.{u, v})
    testParameters (testDensity 0) (testDensity 1)
  have equal (C : Control.{u, v} testParameters.menu) :
      actual.readout () testParameters (testDensity 0) C =
        actual.readout () testParameters (testDensity 1) C := by
    exact congrFun (by simpa only [Subsingleton.elim i ()] using he) C
  change (⨆ C : Control.{u, v} testParameters.menu,
    measurableTotalVariation
      (actual.readout () testParameters (testDensity 0) C)
      (actual.readout () testParameters (testDensity 1) C)) = _ at hh
  simp_rw [equal] at hh
  simp only [measurableTotalVariation, tsub_self, max_self, ENNReal.iSup_zero] at hh
  rw [test_first_sup] at hh
  exact zero_ne_one hh

def family : Registration (arena.{u, v})
    (type_of% (@arbitrary_protocol_tv_supremum.{u, v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@arbitrary_protocol_tv_supremum.{u, v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@arbitrary_protocol_tv_supremum.{u, v})
    (Realization (signature.{u, v})) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.MeasurableRankOneControl.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.MeasurableRankOneControl.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p X => by
      letI := p.finite
      letI := p.decidable
      exact fun R => jointLaw p.menu R X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Fibers.MeasurableRankOneControl
