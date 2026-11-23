import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuQuarticGraph

/-! Readouts of the objective comparison and the exact attained minimum. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuQuarticGraph

namespace Reg.D5.S3.Quantum.Semigroups.WuQuarticGraph

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def comparison (rel : ℝ → ℝ → Prop) : Realization signature :=
  realize signature (fun _ _ x y => rel x y) (fun e => nomatch e)

private def rejected : Realization signature := comparison fun _ _ => False

private theorem dependence (rel : ℝ → ℝ → Prop) {x y z : ℝ}
    (hx : rel x z) (hy : ¬ rel y z) : ObservationalDependence signature (comparison rel) := by
  intro role
  refine ⟨(), x, y, fun h => ?_⟩
  have he : rel x z = rel y z := congrFun h z
  exact hy (Eq.mp he hx)

namespace IndependentSupport

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V) (η : V → ℝ) (κ : ℝ),
    (∀ w ∈ simplex V, ∃ v ∈ simplex V, G.IsIndepSet (positiveSupport v : Set V) ∧
      positiveSupport v ⊆ positiveSupport w ∧
      R.readout () () (objective G η κ v) (objective G η κ w)) ∧
    ∃ v ∈ simplex V, G.IsIndepSet (positiveSupport v : Set V) ∧
      ∀ w ∈ simplex V, objective G η κ v ≤ objective G η κ w

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let j : ULift.{u} Unit := ⟨()⟩
  let w := Convexity.StdSimplex.single (R := ℝ) j
  have hj : (w.weights : ULift.{u} Unit → ℝ) ∈ simplex (ULift.{u} Unit) :=
    ⟨w.weights_nonneg, w.total_of_fintype⟩
  obtain ⟨_, _, _, _, hfalse⟩ := (h (⊥ : SimpleGraph (ULift.{u} Unit)) 0 1).1 _ hj
  exact hfalse

def family : Registration arena.{u} (type_of% @independent_support_minimum.{u}) where
  actual := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@independent_support_minimum.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law _ rejected rejected_law
  dependence := dependence (· ≤ ·) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : ¬ (1 : ℝ) ≤ 0)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@independent_support_minimum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuQuarticGraph.independent_support_minimum.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuQuarticGraph.IndependentSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuQuarticGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "arg", "body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IndependentSupport

namespace Unpenalized

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V) {κ : ℝ},
    0 < κ → ∃ s : Finset V, G.IsNIndepSet G.indepNum s ∧ uniform s ∈ simplex V ∧
      R.readout () () (objective G 0 κ (uniform s)) (κ / (G.indepNum : ℝ)) ∧
      IsLeast (objective G 0 κ '' simplex V) (κ / (G.indepNum : ℝ))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨_, _, _, hfalse, _⟩ := h (⊥ : SimpleGraph (ULift.{u} Unit)) (κ := 1) (by norm_num)
  exact hfalse

def family : Registration arena.{u} (type_of% @unpenalized_minimum.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@unpenalized_minimum.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law _ rejected rejected_law
  dependence := dependence Eq (rfl : (0 : ℝ) = 0) (by norm_num : (1 : ℝ) ≠ 0)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@unpenalized_minimum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuQuarticGraph.unpenalized_minimum.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuQuarticGraph.Unpenalized.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuQuarticGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Unpenalized

namespace Sharp

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V) {β p r : ℝ},
    0 < β → 1 < p → p < r →
    let κ := wuCoefficient β p r
    ∃ s : Finset V, G.IsNIndepSet G.indepNum s ∧ uniform s ∈ simplex V ∧
      objective G 0 κ (uniform s) = κ / (G.indepNum : ℝ) ∧
      ∀ m : ℝ, IsLeast (objective G 0 κ '' simplex V) m ↔
        R.readout () () m (κ / (G.indepNum : ℝ)) ∧ 0 < m ∧ (G.indepNum : ℝ) = κ / m

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let G : SimpleGraph (ULift.{u} Unit) := ⊥
  let κ := wuCoefficient 1 2 3
  obtain ⟨v, hv, _, hmin⟩ := (independent_support_minimum G 0 κ).2
  have hleast : IsLeast (objective G 0 κ '' simplex (ULift.{u} Unit)) (objective G 0 κ v) :=
    ⟨⟨v, hv, rfl⟩, fun _ ⟨w, hw, he⟩ => he ▸ hmin w hw⟩
  obtain ⟨_, _, _, _, hall⟩ := h G (β := 1) (p := 2) (r := 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact ((hall _).mp hleast).1

def family : Registration arena.{u} (type_of% @wu_unpenalized_minimum.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@wu_unpenalized_minimum.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law _ rejected rejected_law
  dependence := dependence Eq (rfl : (0 : ℝ) = 0) (by norm_num : (1 : ℝ) ≠ 0)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@wu_unpenalized_minimum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuQuarticGraph.wu_unpenalized_minimum.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuQuarticGraph.Sharp.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuQuarticGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Sharp

end Reg.D5.S3.Quantum.Semigroups.WuQuarticGraph
