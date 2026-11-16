import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
import Reg.Support.DependentFamily

/-! Exact source-bound weighted-essential-sup comparison registration. -/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
open D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ (
    ∀ (B : H →L[ℂ] H) (S : ℂ → H →L[ℂ] H),
        IsSelfAdjoint B →
        (∀ u, 0 ≤ (form B u u).re ∧ (form B u u).im = 0) →
        (∀ u w, (∀ v, form B u v = ⟪v, w⟫_ℂ) ↔ w = B u) →
        (∀ u v w c, form B (u+v) w = form B u w + form B v w ∧
          form B (c • u) v = c * form B u v ∧
          form B u (v+w) = form B u v + form B u w ∧
          form B u (c • v) = star c * form B u v) →
        Continuous (fun p : H × H => form B p.1 p.2) →
        Dense (univ : Set H) →
        (∀ s : ℕ → H,
          (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
            formNorm B (s m - s n) < ε) →
          ∃ u : H, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
            formNorm B (s n - u) < ε) →
        (∀ z, S z = NormedSpace.exp ((-z) • B)) →
        S 0 = 1 → (∀ z w, S (z+w) = S z * S w) →
        (∀ z, AnalyticAt ℂ S z) → HasDerivAt S (-B) 0 →
        (∀ z, 0 ≤ z.re → ‖S z‖ ≤ 1) →
        (∀ t : ℝ, 0 ≤ t → ∀ f : H,
          (∀ᵐ x ∂μ, 0 ≤ (f x).re ∧ (f x).im = 0) →
          ∀ᵐ x ∂μ, 0 ≤ (S (t:ℂ) f x).re ∧ (S (t:ℂ) f x).im = 0) →
        (∀ t : ℝ, 0 ≤ t → ∀ f : H, MemLp f ∞ μ →
          eLpNorm (S (t:ℂ) f) ∞ μ ≤ ENNReal.ofReal (3/2 : ℝ) * eLpNorm f ∞ μ) →
        ∃ g : ℝ → ℝ, Measurable g ∧ MemLp g ∞ μ ∧
          MemLp (fun x => (g x)⁻¹) ∞ μ ∧ (∀ᵐ x ∂μ, 0 < g x) ∧
          ∀ t : ℝ, 0 ≤ t → ∀ f : H, MemLp f ∞ μ →
            R.readout () () (eLpNorm (fun x => (g x:ℂ) * S (t:ℂ) f x) ∞ μ)
              (eLpNorm (fun x => (g x:ℂ) * f x) ∞ μ)
  )

private theorem actual_law : arena.Law actual := result

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro B S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hb : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ μ := memLp_const 1
  refine ⟨fun _ => 1, measurable_const, hb, ?_, ?_, ?_⟩
  · simpa using hb
  · simp
  · intro t ht f hf
    trivial

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh : (1 : ℝ≥0∞) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    result (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
    definition := some {
      owner := `D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
      name := `D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","arg","arg","arg","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

namespace Conditioned
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x=y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ t : ℝ} (hk : 1 ≤ κ) (ht : 0 ≤ t),
    let g := fun x : ℝ => (max 1 (κ*x))⁻¹
    _root_.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Weight μ g ∧
    R.readout () () (_root_.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.condition μ g) κ ∧
    WeightedSharp t g (1+(1-Real.exp (-t))/(2*κ^3)) ∧
    ∀ w : ℝ → ℝ, _root_.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.Weight μ w →
      _root_.D5.S3.Quantum.Semigroups.ConditionedRankOneNorm.condition μ w ≤ κ →
      ∀ C : ℝ, 0 ≤ C →
        (∀ f : H, MemLp f ∞ μ →
          eLpNorm (fun x => (w x:ℂ)*T (t:ℂ) f x) ∞ μ ≤
            ENNReal.ofReal C * eLpNorm (fun x => (w x:ℂ)*f x) ∞ μ) →
        1+(1-Real.exp (-t))/(2*κ^3) ≤ C

private theorem actual_law : arena.Law actual := @conditioned_weight_optimum
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact (hh (κ := 1) (t := 0) le_rfl le_rfl).2.1

def family : Registration arena (type_of% (@conditioned_weight_optimum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh : (1:ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conditioned_weight_optimum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction.Conditioned.unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction.Conditioned.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","arg","fn","arg","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Conditioned
end Reg.D5.S3.Quantum.Semigroups.PositiveRankOneWeightObstruction
