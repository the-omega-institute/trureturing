import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.PhaseConditioningVariation
import Reg.Support.DependentFamily

open D5.S3.Quantum.Fibers.FiniteRectangleTransport
open D5.S3.Quantum.Fibers.PhaseConditioningVariation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory

namespace Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation
noncomputable section

namespace Denominator

abbrev signature : Signature where
  Params := Base
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p k => Q p k) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (_hb : ValidBase b) (k ε : ℝ)
    (_hk : k ∈ Ioo (lower b) (upper b)) (_hε : 0 < ε)
    (_hm : ∀ i, ε ≤ mass b k i),
    R.readout () b k = information b k * ∏ i, mass b k i ∧
      4*ε^3 ≤ Q b k ∧ 0 < Q b k

private lemma bad_fails : ¬ arena.Law bad := by
  intro h
  have he := h (1/5,2/5,1/5) (by norm_num [ValidBase]) (1/20) (1/100)
    (by norm_num [lower,upper]) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [mass,bottom,probability,Matrix.cons_val_three,Matrix.cons_val_four])
  norm_num [bad,realize,information,mass,bottom,probability,Q,Fin.prod_univ_succ,
    Matrix.cons_val_three,Matrix.cons_val_four] at he

def registration : Registration arena (type_of% denominator_margin) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨denominator_margin,bad,bad_fails⟩
  sensitivity := by
    constructor
    · intro i; refine ⟨bad,?_,rfl,bad_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1/5,2/5,1/5),1/20,1/10,?_⟩
    norm_num [actual,realize,Q]
end Denominator

namespace Pointwise

abbrev signature : Signature where
  Params := Σ _ : Base, Fin 2
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p k => phaseDifference (phaseWeight p.1 k) p.2) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (_hb : ValidBase b) (k ε : ℝ)
    (_hk : k ∈ Ioo (lower b) (upper b)) (_hε : 0 < ε)
    (_hm : ∀ i, ε ≤ mass b k i) (i : Fin 2),
    |R.readout () ⟨b,i⟩ k| ≤ |gap b i| * (1-b.2.2)/(16*ε^2)

private lemma bad_fails : ¬ arena.Law bad := by
  intro h
  have he := h (2/5,2/5,1/5) (by norm_num [ValidBase]) (1/5) (1/100)
    (by norm_num [lower,upper]) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [mass,bottom,probability,Matrix.cons_val_three,Matrix.cons_val_four]) 0
  norm_num [bad,realize,gap] at he

def registration : Registration arena (type_of% pointwise_gap_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pointwise_gap_bound,bad,bad_fails⟩
  sensitivity := by
    constructor
    · intro i; refine ⟨bad,?_,rfl,bad_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(1/5,2/5,1/5),0⟩,1/20,1/10,?_⟩
    norm_num [actual,realize,phaseDifference,phaseWeight,leftMode,rightMode,direction,information,probability,Matrix.cons_val_three,Matrix.cons_val_four]
end Pointwise

namespace Integral

abbrev signature : Signature where
  Params := Fin 2
  State := fun _ => Vec
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p s => phaseDifference s p) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : Base) (_hb : ValidBase b) (T ε : ℝ) (_hT : 0 ≤ T)
    (_hε : 0 < ε) (k α : ℝ → ℝ) (_ha : IntervalIntegrable α volume 0 T)
    (_hw : ∀ j, IntervalIntegrable (fun t => phaseWeight b (k t) j*α t) volume 0 T)
    (_hk : ∀ t ∈ Icc (0:ℝ) T, k t ∈ Ioo (lower b) (upper b))
    (_hm : ∀ t ∈ Icc (0:ℝ) T, ∀ j, ε ≤ mass b (k t) j) (i : Fin 2),
    |R.readout () i (fun j => ∫ t in (0:ℝ)..T, phaseWeight b (k t) j*α t)| ≤ |gap b i| * (1-b.2.2)/(16*ε^2)*
      (∫ t in (0:ℝ)..T, |α t|)

private lemma bad_fails : ¬ arena.Law bad := by
  intro h
  have he := h (1/5,2/5,1/5) (by norm_num [ValidBase]) 1 (1/100) (by norm_num)
    (by norm_num) (fun _ => 1/20) (fun _ => 0) (by simp)
    (by intro j; simp) (by intros; norm_num [lower,upper])
    (by intro t ht i; fin_cases i <;> norm_num [mass,bottom,probability,Matrix.cons_val_three,Matrix.cons_val_four]) 0
  norm_num [bad,realize] at he

def registration : Registration arena (type_of% integral_variation_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨integral_variation_bound,bad,bad_fails⟩
  sensitivity := by
    constructor
    · intro i; refine ⟨bad,?_,rfl,bad_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨0,(fun _ => 0),![0,1,0,0,0],?_⟩
    norm_num [actual,realize,phaseDifference,leftMode,rightMode,Matrix.cons_val_three]
end Integral

noncomputable def denominator_margin_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Quantum.Fibers.PhaseConditioningVariation.denominator_margin)
    (type_of% (realize Denominator.signature (fun _ p k => Q p k) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation.Denominator.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation.Denominator.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Denominator.arena⟩,
  objectArena := .source ⟨Denominator.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Denominator.arena ⟨Denominator.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Denominator.signature (fun _ p k => Q p k) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.PhaseConditioningVariation,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms Denominator.registration

noncomputable def pointwise_gap_bound_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Quantum.Fibers.PhaseConditioningVariation.pointwise_gap_bound)
    (type_of% (realize Pointwise.signature (fun _ p k => phaseDifference (phaseWeight p.1 k) p.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation.Pointwise.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation.Pointwise.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Pointwise.arena⟩,
  objectArena := .source ⟨Pointwise.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Pointwise.arena ⟨Pointwise.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Pointwise.signature (fun _ p k => phaseDifference (phaseWeight p.1 k) p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.PhaseConditioningVariation,
    definition := none,
    coordinates := #[0,7],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn","arg","arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms Pointwise.registration

noncomputable def integral_variation_bound_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Quantum.Fibers.PhaseConditioningVariation.integral_variation_bound)
    (type_of% (realize Integral.signature (fun _ p s => phaseDifference s p) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation.Integral.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation.Integral.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨Integral.arena⟩,
  objectArena := .source ⟨Integral.arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source Integral.arena ⟨Integral.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Integral.signature (fun _ p s => phaseDifference s p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.PhaseConditioningVariation,
    definition := none,
    coordinates := #[12],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn","arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms Integral.registration

end
end Reg.D5.S3.Quantum.Fibers.PhaseConditioningVariation
