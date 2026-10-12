import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Phase.MultivariateWeylRectangles
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Phase.MultivariateWeylRectangles
open LeanInformationAudit Filter Finset MeasureTheory
open scoped Topology BigOperators

noncomputable section
namespace Reg.D5.S1.Phase.MultivariateWeylRectangles

abbrev normSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ x => ‖x‖) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ => 1) (fun e => nomatch e)

def normArena : Arena where
  signature := normSignature
  Law R := ∀ {d : ℕ} (α : ℝ) (_hα : Irrational α)
    (Q : MvPolynomial (Fin d) ℤ) (_hQ : 0 < Q.totalDegree),
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 1 ≤ T ∧ ∀ N : Fin d → ℕ,
      (∀ i, T ≤ N i) →
      R.readout () () (𝔼 n ∈ Fintype.piFinset (fun i => range (N i)), polynomialPhase α Q n) < ε

private theorem norm_rejected_law : ¬ normArena.Law normRejected := by
  intro h
  obtain ⟨T, _, hT⟩ := h (d := 1) (Real.sqrt 2) irrational_sqrt_two
    (MvPolynomial.X 0) (by simp) (1/2) (by norm_num)
  have hh := hT (fun _ => T) (fun _ => le_rfl)
  change (1 : ℝ) < 1/2 at hh
  norm_num at hh

def normRegistration : Registration normArena (normArena.Law normActual) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨polynomial_rectangular_cancellation, normRejected, norm_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    normArena.Law normActual normRejected norm_rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
    norm_num

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Phase.MultivariateWeylRectangles.polynomial_rectangular_cancellation)
    (type_of% (realize normSignature (fun _ _ x => ‖x‖) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.norm_information_unit
  realizationName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.normRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨normArena⟩
  objectArena := .source ⟨normArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normArena ⟨normRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Phase.MultivariateWeylRectangles
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

universe u

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev integralSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def integralActual : Realization integralSignature :=
  realize integralSignature (fun _ _ x => x) (fun e => nomatch e)

def integralRejected : Realization integralSignature :=
  realize integralSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem integral_dependence : ObservationalDependence integralSignature integralActual := by
  intro i
  exact ⟨(), (0 : ℂ), (1 : ℂ), zero_ne_one⟩

def rectangleArena : Arena where
  signature := integralSignature
  Law R := ∀ {κ : Type u} [Fintype κ] {d : ℕ} (α : ℝ) (_hα : Irrational α)
    (e : κ → (Fin d →₀ ℕ)) (_he : Function.Injective e) (_hzero : ∀ j, e j ≠ 0)
    (a : Fin d → ℕ) (F : C(UnitAddTorus κ, ℂ)),
    Tendsto (fun N : Fin d → ℕ =>
      𝔼 n ∈ Fintype.piFinset (fun i => range (N i)), F (monomialOrbit α e a n))
      atTop (𝓝 (R.readout () () (∫ z, F z)))

private theorem rectangle_rejected_law : ¬ rectangleArena.{u}.Law integralRejected := by
  intro h
  let e : ULift.{u} Unit → (Fin 1 →₀ ℕ) := fun _ => Finsupp.single 0 1
  have he : Function.Injective e := fun _ _ _ => Subsingleton.elim _ _
  have hz : ∀ j, e j ≠ 0 := fun _ => Finsupp.single_ne_zero.mpr one_ne_zero
  have hbad := h (Real.sqrt 2) irrational_sqrt_two e he hz 0 1
  have hgood := monomial_rectangular_equidistribution
    (Real.sqrt 2) irrational_sqrt_two e he hz 0 1
  have heq := tendsto_nhds_unique hgood hbad
  simpa [integralRejected, realize] using heq

def rectangleRegistration : Registration rectangleArena.{u}
    (rectangleArena.{u}.Law integralActual) where
  actual := integralActual
  bridge := Iff.rfl
  variation := ⟨@monomial_rectangular_equidistribution, integralRejected, rectangle_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    rectangleArena.Law integralActual integralRejected rectangle_rejected_law
  dependence := integral_dependence

def curveArena : Arena where
  signature := integralSignature
  Law R := ∀ {κ : Type u} [Fintype κ] {d : ℕ} (α : ℝ) (_hα : Irrational α)
    (e : κ → (Fin d →₀ ℕ)) (_he : Function.Injective e) (_hzero : ∀ j, e j ≠ 0)
    (B : ℕ) (_hB : 2 ≤ B) (_hdigit : ∀ j i, e j i < B) (F : C(UnitAddTorus κ, ℂ)),
    Tendsto (fun L : ℕ => 𝔼 t ∈ range L,
      F (monomialOrbit α e 0 (fun i => (t + 1) ^ (B ^ i.val))))
      atTop (𝓝 (R.readout () () (∫ z, F z)))

private theorem curve_rejected_law : ¬ curveArena.{u}.Law integralRejected := by
  intro h
  let e : ULift.{u} Unit → (Fin 1 →₀ ℕ) := fun _ => Finsupp.single 0 1
  have he : Function.Injective e := fun _ _ _ => Subsingleton.elim _ _
  have hz : ∀ j, e j ≠ 0 := fun _ => Finsupp.single_ne_zero.mpr one_ne_zero
  have hdigit : ∀ j i, e j i < 2 := by intro j i; fin_cases i; simp [e]
  have hbad := h (Real.sqrt 2) irrational_sqrt_two e he hz 2 (by decide) hdigit 1
  have hgood := monomial_curve_equidistribution
    (Real.sqrt 2) irrational_sqrt_two e he hz 2 (by decide) hdigit 1
  have heq := tendsto_nhds_unique hgood hbad
  simpa [integralRejected, realize] using heq

def curveRegistration : Registration curveArena.{u} (curveArena.{u}.Law integralActual) where
  actual := integralActual
  bridge := Iff.rfl
  variation := ⟨@monomial_curve_equidistribution, integralRejected, curve_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    curveArena.Law integralActual integralRejected curve_rejected_law
  dependence := integral_dependence

noncomputable def registration_2 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Phase.MultivariateWeylRectangles.monomial_rectangular_equidistribution.{u})
    (type_of% (realize integralSignature (fun _ _ x => x) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.rectangle_integral_unit
  realizationName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.rectangleRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rectangleArena⟩
  objectArena := .source ⟨rectangleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rectangleArena ⟨rectangleRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integralSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Phase.MultivariateWeylRectangles
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_3 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Phase.MultivariateWeylRectangles.monomial_curve_equidistribution.{u})
    (type_of% (realize integralSignature (fun _ _ x => x) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.curve_integral_unit
  realizationName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.curveRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨curveArena⟩
  objectArena := .source ⟨curveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source curveArena ⟨curveRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integralSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Phase.MultivariateWeylRectangles
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def visitSignature : Signature where
  Params := Σ κ : Type u, Set (UnitAddTorus κ)
  State p := UnitAddTorus p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def visitActual : Realization visitSignature.{u} :=
  realize visitSignature
    (fun _ p x => @decide (x ∈ p.2) (Classical.propDecidable _)) (fun e => nomatch e)

def visitRejected : Realization visitSignature.{u} :=
  realize visitSignature (fun _ _ _ => false) (fun e => nomatch e)

def visitArena : Arena where
  signature := visitSignature.{u}
  Law R := ∀ {κ : Type u} [Fintype κ] {d : ℕ} (_hd : 0 < d) (α : ℝ) (_hα : Irrational α)
    (e : κ → (Fin d →₀ ℕ)) (_he : Function.Injective e) (_hzero : ∀ j, e j ≠ 0)
    (_hinput : ∀ i : Fin d, ∃ j, e j = Finsupp.single i 1)
    (B : ℕ) (_hdigit : ∀ j i, e j i < B)
    (U : Set (UnitAddTorus κ)) (_hU : IsOpen U) (_hUne : U.Nonempty) (T : ℕ),
    ∃ t : ℕ, max T 1 ≤ t ∧
      R.readout () ⟨κ, U⟩ (monomialOrbit α e 0 (fun i => t ^ (B ^ i.val))) = true ∧
      ∀ i : Fin d, T ≤ t ^ (B ^ i.val)

private theorem visit_rejected_law : ¬ visitArena.{u}.Law visitRejected := by
  intro h
  let e : ULift.{u} Unit → (Fin 1 →₀ ℕ) := fun _ => Finsupp.single 0 1
  have he : Function.Injective e := fun _ _ _ => Subsingleton.elim _ _
  have hz : ∀ j, e j ≠ 0 := fun _ => Finsupp.single_ne_zero.mpr one_ne_zero
  have hdigit : ∀ j i, e j i < 2 := by intro j i; fin_cases i; simp [e]
  have hinput : ∀ i : Fin 1, ∃ j, e j = Finsupp.single i 1 := by
    intro i
    refine ⟨⟨()⟩, ?_⟩
    change Finsupp.single (0 : Fin 1) 1 = Finsupp.single i 1
    rw [Subsingleton.elim i 0]
  obtain ⟨t, _, hbad, _⟩ := h (by decide) (Real.sqrt 2) irrational_sqrt_two
    e he hz hinput 2 hdigit Set.univ isOpen_univ (Set.univ_nonempty) 0
  cases hbad

private theorem visit_bridge :
    (type_of% (@monomial_curve_visits.{u})) ↔ visitArena.{u}.Law visitActual := by
  classical
  constructor
  · intro h κ inst d hd α hα e he hz hi B hb U hU hUne T
    obtain ⟨t, ht, hu, hall⟩ := @h κ inst d hd α hα e he hz hi B hb U hU hUne T
    exact ⟨t, ht, decide_eq_true hu, hall⟩
  · intro h κ inst d hd α hα e he hz hi B hb U hU hUne T
    obtain ⟨t, ht, hu, hall⟩ := @h κ inst d hd α hα e he hz hi B hb U hU hUne T
    exact ⟨t, ht, of_decide_eq_true hu, hall⟩

def visitRegistration : Registration visitArena.{u}
    (type_of% (@monomial_curve_visits.{u})) where
  actual := visitActual
  bridge := visit_bridge
  variation := ⟨visit_bridge.mp @monomial_curve_visits.{u}, visitRejected, visit_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨visitRejected, ?_, rfl, visit_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro i; exact nomatch i
  dependence := by
    classical
    intro i
    have hh : ((1/2 : ℝ) : UnitAddCircle) ≠ 0 := by
      intro h
      have hzero := (AddCircle.coe_eq_zero_iff_of_mem_Ico
        (p := (1 : ℝ)) (a := (1/2 : ℝ)) (by constructor <;> norm_num)).mp h
      norm_num at hzero
    let y : UnitAddTorus (ULift.{u} Unit) := fun _ => ((1/2 : ℝ) : UnitAddCircle)
    have hy : y ≠ 0 := fun h => hh (congrFun h ⟨()⟩)
    refine ⟨⟨ULift.{u} Unit, {(0 : UnitAddTorus (ULift.{u} Unit))}⟩, (0 : UnitAddTorus (ULift.{u} Unit)), y, ?_⟩
    intro h
    have ht : visitActual.readout i
        ⟨ULift.{u} Unit, {(0 : UnitAddTorus (ULift.{u} Unit))}⟩
        (0 : UnitAddTorus (ULift.{u} Unit)) = true :=
      @decide_eq_true ((0 : UnitAddTorus (ULift.{u} Unit)) ∈ {0})
        (Classical.propDecidable _) rfl
    have hy0 : y ∈ ({0} : Set (UnitAddTorus (ULift.{u} Unit))) :=
      @of_decide_eq_true (y ∈ ({0} : Set (UnitAddTorus (ULift.{u} Unit))))
        (Classical.propDecidable _) (h.symm.trans ht)
    exact hy hy0

noncomputable def registration_4 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Phase.MultivariateWeylRectangles.monomial_curve_visits.{u})
    (type_of% (realize visitSignature.{u}
      (fun _ p x => @decide (x ∈ p.2) (Classical.propDecidable _))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.visit_information_unit
  realizationName := `Reg.D5.S1.Phase.MultivariateWeylRectangles.visitRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨visitArena⟩
  objectArena := .source ⟨visitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source visitArena ⟨visitRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize visitSignature.{u}
    (fun _ p x => @decide (x ∈ p.2) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Phase.MultivariateWeylRectangles
    definition := none
    coordinates := #[0, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S1.Phase.MultivariateWeylRectangles
