import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.PersistentLaplacianHeatStability
import Reg.Support.DependentFamily

/-! The real comparison in the degree-zero persistent heat bound. -/

open AlgebraicTopology LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteSimplicialSingularHomology
open _root_.D5.S3.Geometry.PersistentLaplacianHeatStability

noncomputable section

namespace Reg.D5.S3.Geometry.PersistentLaplacianHeatStability

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
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {V : Type} [Fintype V] [LinearOrder V] {K L : PreAbstractSimplicialComplex V}
    (hKL : K ≤ L) (v : Face K 0 → ℝ) (_hv : ∀ i, 0 < v i)
    {hidden hidden' : HiddenVertex K L → ℝ}
    (_hh : ∀ i, 0 < hidden i) (_hh' : ∀ i, 0 < hidden' i)
    {w w' : Face L 1 → ℝ} (_hw : ∀ i, 0 < w i) (_hw' : ∀ i, 0 < w' i)
    {M t u : ℝ} (_hM : 1 ≤ M) (_ht : 0 < t) (_hu : 0 < u)
    (_hlo : ∀ i, M⁻¹ * (t * w i) ≤ u * w' i) (_hhi : ∀ i, u * w' i ≤ M * (t * w i)),
    R.readout () () ‖NormedSpace.exp (-(u • persistentLaplacian hKL v hidden' w')) -
      NormedSpace.exp (-(t • persistentLaplacian hKL v hidden w))‖ ((M - 1) / (M + 1))

private theorem actual_law : arena.Law actual := @weighted_persistent_heat_stability

private def emptyComplex : PreAbstractSimplicialComplex (Fin 0) where
  faces := ∅
  isRelLowerSet_faces := by simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (V := Fin 0) (K := emptyComplex) (L := emptyComplex) le_rfl
    (fun _ => 1) (fun _ => zero_lt_one)
    (hidden := fun _ => 1) (hidden' := fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    (w := fun _ => 1) (w' := fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    (M := 1) (t := 1) (u := 1) le_rfl zero_lt_one zero_lt_one
    (fun _ => by norm_num) (fun _ => by norm_num)

def family : Registration arena (type_of% (@weighted_persistent_heat_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_persistent_heat_stability) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.PersistentLaplacianHeatStability.heatBound.unit
  realizationName := `Reg.D5.S3.Geometry.PersistentLaplacianHeatStability.family
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
    owner := `D5.S3.Geometry.PersistentLaplacianHeatStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.PersistentLaplacianHeatStability
