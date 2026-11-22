import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Diversity.SimplexQuadraticOptimality
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Geometry.Diversity.SimplexQuadraticOptimality

open _root_.D5.S3.Geometry.Diversity.SimplexQuadraticOptimality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix

set_option autoImplicit false
noncomputable section
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the lower condition derived from
minimality. -/
abbrev arena : Arena where
  signature := signature
  Law Q := ∀ {ι : Type u} [Fintype ι] (Z : Matrix ι ι ℝ), Z.IsSymm →
    ∀ {p : ι → ℝ}, Prob p →
    ((∀ q, Prob q → energy Z p ≤ energy Z q) →
      (∀ i, 0 < p i → (Z *ᵥ p) i = energy Z p) ∧ ∀ j, Q.readout () () (energy Z p) ((Z *ᵥ p) j)) ∧
    ((∀ v : ι → ℝ, ∑ i, v i = 0 → 0 ≤ energy Z v) →
      ((∀ q, Prob q → energy Z p ≤ energy Z q) ↔
        (∀ i, 0 < p i → (Z *ᵥ p) i = energy Z p) ∧ ∀ j, energy Z p ≤ (Z *ᵥ p) j))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp : Prob (fun _ : ULift.{u} (Fin 1) => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, by simp⟩
  have hmin : ∀ q : ULift.{u} (Fin 1) → ℝ, Prob q →
      energy (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℝ) (fun _ => 1) ≤
        energy (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℝ) q :=
    fun q _ => by simp [energy]
  exact ((h (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℝ) Matrix.isSymm_zero hp).1
    hmin).2 ⟨0⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℝ)
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% (@result.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Diversity.SimplexQuadraticOptimality.result.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Diversity.SimplexQuadraticOptimality.family
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
    owner := `D5.S3.Geometry.Diversity.SimplexQuadraticOptimality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body",
        "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Geometry.Diversity.SimplexQuadraticOptimality
