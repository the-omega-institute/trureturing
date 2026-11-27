import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Probability.UniformFiberCoupling
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.PUnit

/-! The right side recovers the prescribed displacement law at every point of the fiber. -/

namespace Reg.D5.S3.Analytic.Probability.UniformFiberCoupling

open Finset LeanInformationAudit
open scoped Classical D5.S3.Analytic.Probability.UniformFiberCoupling
open _root_.D5.S3.Analytic.Probability.UniformFiberCoupling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u v

noncomputable section

abbrev Params :=
  Σ G : Type u, Σ H : Type v, Σ g : Group G, Σ h : Group H,
    Σ _ : (letI := g; letI := h; G →* H), H

abbrev observedFiber (p : Params.{u, v}) : Type u :=
  letI := p.2.2.1
  letI := p.2.2.2.1
  Fiber p.2.2.2.2.1 p.2.2.2.2.2

abbrev signature : Signature where
  Params := Params.{u, v}
  State p := observedFiber p → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := observedFiber p → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ law => law) (fun e => nomatch e)

def negative : Realization signature.{u, v} :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {G : Type u} {H : Type v} [g : Group G] [h : Group H]
    (φ : G →* H) (t : H) [Finite (Fiber φ 1)] (ρ : Fiber φ t → ℝ),
    ((∀ d, 0 ≤ ρ d) ∧ ∑ d, ρ d = 1) ↔
      ∃ w : Fiber φ 1 → Fiber φ t → ℝ,
        (∀ x y, 0 ≤ w x y) ∧
        (∀ x, ∑ y, w x y = 1 / (Fintype.card (Fiber φ 1) : ℝ)) ∧
        (∀ y, ∑ x, w x y = 1 / (Fintype.card (Fiber φ t) : ℝ)) ∧
        displacement φ t w = R.readout () ⟨G, H, g, h, φ, t⟩ ρ

private theorem negative_fails : ¬ arena.{u, v}.Law negative := by
  intro law
  let φ : PUnit.{u+1} →* PUnit.{v+1} := 1
  let idPoint : Fiber φ 1 := ⟨1, φ.map_one⟩
  let ρ (d : Fiber φ 1) : ℝ := if d = idPoint then 1 else 0
  have nn (d : Fiber φ 1) : 0 ≤ ρ d := by
    unfold ρ
    split <;> norm_num
  obtain ⟨w, hw, _, _, recover⟩ := (law φ 1 ρ).mp ⟨nn, by simp [ρ]⟩
  have nonnegative : 0 ≤ displacement φ 1 w idPoint := by
    unfold displacement
    exact sum_nonneg fun x _ => sum_nonneg fun y _ => by split <;> simp [hw]
  have point := congrFun recover idPoint
  change displacement φ 1 w idPoint = -1 at point
  rw [point] at nonnegative
  exact (not_le.mpr (by norm_num : (-1 : ℝ) < 0)) nonnegative

def family : Registration arena.{u, v} (type_of% (@displacement_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@displacement_iff, negative, negative_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨negative, ?_, rfl, negative_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    let φ : PUnit.{u+1} →* PUnit.{v+1} := 1
    let p : Params.{u, v} := ⟨PUnit.{u+1}, PUnit.{v+1}, inferInstance, inferInstance, φ, 1⟩
    let idPoint : observedFiber p := ⟨1, φ.map_one⟩
    refine ⟨p, (fun _ => 0), (fun _ => 1), ?_⟩
    intro eq
    have point := congrFun eq idPoint
    change (0 : ℝ) = 1 at point
    norm_num at point

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@displacement_iff.{u, v}) (Realization signature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Probability.UniformFiberCoupling.displacementLaw
  realizationName := `Reg.D5.S3.Analytic.Probability.UniformFiberCoupling.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ law => law) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.UniformFiberCoupling
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Probability.UniformFiberCoupling
