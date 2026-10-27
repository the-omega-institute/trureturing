import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalControlMarkedJump
import Reg.Support.DependentFamily

/-! Source-bound audit of the original continuous affine-leg marked law. -/

open D5.S3.Quantum.Fibers
open D5.S3.Quantum.Fibers.OriginalControlMarkedJump
open D5.S3.Quantum.Fibers.OriginalControlMarkedJump.Leg
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory
namespace Reg.D5.S3.Quantum.Fibers.OriginalControlMarkedJump
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Leg
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Measure Record
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ L => L.markedLaw) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : Leg) (chi beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ),
    OriginalControlComposition.OriginalControl (L.c,L.c,1-2*L.c)
      L.duration L.height (fun _ => chi) ∧
    AbsolutelyContinuousOnInterval L.height 0 L.duration ∧
    OriginalControlComposition.FiniteC1Control L.duration L.height (fun _ => chi) ∧
    (∀ t : ℝ, ∀ i : Fin 5,
      (∫ u in (0:ℝ)..t,FiniteRectangleTransport.phaseWeight (L.c,L.c,1-2*L.c)
        (L.height u) i * deriv (fun _ : ℝ => chi) u)=0) ∧
    (∀ i : Fin 5, ∀ t : ℝ, L.modeMeasure i {t}=0) ∧
    (∀ i : Fin 5,L.modeMeasure i (Ioc 0 L.duration)ᶜ=0) ∧
    (∀ t ∈ Icc 0 L.duration,L.survival t = if L.x ≤ L.y then L.x/L.height t
      else (L.c-L.x)/(L.c-L.height t)) ∧
    IsProbabilityMeasure (R.readout () () L) ∧
    ∀ E : Set Record, MeasurableSet E →
      (R.readout () () L) E =
        (if Sum.inl () ∈ E then ENNReal.ofReal
          (∑ i, Complex.normSq ((successfulKraus L.c L.x L.y (L.survival L.duration) *ᵥ 
            source L.c L.x beta m theta) i)) else 0) +
        ∑ i : Fin 5, ∫⁻ t in (Ioc 0 L.duration) ∩ {t | Sum.inr (i,t) ∈ E},
          ENNReal.ofReal (Complex.normSq
            ((jumpKraus L.c L.x (L.height t) (L.survival t) (L.jumpRate t) i *ᵥ 
              source L.c L.x beta m theta) 0))

private def wait : Leg where
  c := 2/5
  x := 1/5
  y := 1/5
  duration := 1
  c_lt := by norm_num
  x_pos := by norm_num
  x_lt := by norm_num
  y_pos := by norm_num
  y_lt := by norm_num
  duration_pos := by norm_num

private def move : Leg where
  c := 2/5
  x := 1/5
  y := 3/10
  duration := 1
  c_lt := by norm_num
  x_pos := by norm_num
  x_lt := by norm_num
  y_pos := by norm_num
  y_lt := by norm_num
  duration_pos := by norm_num

private theorem actual_law : arena.Law actual := by
  intro L chi beta m theta
  exact L.affine_marked_probability chi beta m theta

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,hp,_⟩ := h wait 0 0 0 (fun _ => 0)
  change IsProbabilityMeasure (0 : Measure Record) at hp
  have hh := isProbabilityMeasure_iff.mp hp
  simpa using hh

private theorem success_mass (L : Leg) :
    L.markedLaw {Sum.inl ()}=ENNReal.ofReal (L.survival L.duration) := by
  have hset : MeasurableSet ({Sum.inl ()} : Set Record) := by
    simpa only [Set.image_singleton] using
      (show MeasurableSet ({()} : Set Unit) from measurableSet_singleton ()).inl_image
  have hm (i : Fin 5) : Measurable (fun t : ℝ => (Sum.inr (i,t) : Record)) :=
    measurable_inr.comp (measurable_const.prodMk measurable_id)
  simp only [Leg.markedLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (by simp : Sum.inl () ∈ ({Sum.inl ()} : Set Record)),
    mul_one,Measure.finsetSum_apply]
  have he (i : Fin 5) : (L.modeMeasure i).map (fun t => (Sum.inr (i,t) : Record))
      {Sum.inl ()}=0 := by
    rw [Measure.map_apply (hm i) hset]
    have hz : (fun t : ℝ => (Sum.inr (i,t) : Record)) ⁻¹' {Sum.inl ()}=∅ := by
      ext t
      simp
    rw [hz,measure_empty]
  simp only [he,Finset.sum_const_zero,add_zero]

private theorem survival_wait : wait.survival wait.duration=1 := by
  obtain ⟨_,_,_,_,_,_,hs,_,_⟩ := wait.affine_marked_probability 0 0 0 (fun _ => 0)
  have he := hs wait.duration ⟨wait.duration_pos.le,le_rfl⟩
  norm_num [wait,Leg.height,Leg.speed] at he ⊢
  exact he

private theorem survival_move : move.survival move.duration=2/3 := by
  obtain ⟨_,_,_,_,_,_,hs,_,_⟩ := move.affine_marked_probability 0 0 0 (fun _ => 0)
  have he := hs move.duration ⟨move.duration_pos.le,le_rfl⟩
  norm_num [move,Leg.height,Leg.speed] at he ⊢
  exact he

def registration : Registration arena (type_of% (@Leg.affine_marked_probability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),wait,move,?_⟩
    intro he
    change wait.markedLaw=move.markedLaw at he
    have hm := congrArg (fun mu : Measure Record => mu {Sum.inl ()}) he
    rw [success_mass,success_mass,survival_wait,survival_move] at hm
    have hr := congrArg ENNReal.toReal hm
    norm_num at hr

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Leg.affine_marked_probability)
    (type_of% (realize signature (fun _ _ L => L.markedLaw) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Fibers.OriginalControlMarkedJump.Leg.affine_marked_probability.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalControlMarkedJump.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ L => L.markedLaw) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.OriginalControlMarkedJump
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","arg","arg","arg","arg","arg",
        "arg","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },{
      path := #["body","body","body","body","body","arg","arg","arg","arg","arg",
        "arg","arg","arg","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Fibers.OriginalControlMarkedJump
