import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration
import Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers

/-! The two table transports record their calibrated row readouts. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration

open _root_.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration
open _root_.D5.S3.ConceptDynamics.Attribution.FixedKernelMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers (signature actual rejected)
open LeanInformationAudit
open Finset

universe u v w s

noncomputable section

attribute [local instance 2000] tableSMul tableAction

local instance (priority := 2100) tableSubgroupAction {G X Y : Type*} [Group G]
    [MulAction G X] [MulAction G Y] (H : Subgroup G) : MulAction H (X → Y) :=
  MulAction.compHom (X → Y) H.subtype

namespace Pushforward

set_option linter.checkUnivs false in
abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
      [Fintype (X → Y)] {S : Type s} [Fintype S] [MulAction G S]
      (weights : S → ℝ) (_nn : ∀ s, 0 ≤ weights s) (_total : ∑ s, weights s = 1)
      (f : X → S → Y) (_cov : ∀ (g : G) x s, f (g • x) (g • s) = g • f x s)
      [DecidableEq Y] (P : X → Y → ℝ)
      (_marginal : ∀ x y, (∑ s, if f x s = y then weights s else 0) = P x y),
      let p := tableLaw weights f
      (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
        ((∀ (g : G) s, weights (g • s) = weights s) →
          ∀ (g : G) t, p (g • t) = p t) ∧
        (∀ x y, (∑ t, if t x = y then p t else 0) = R.readout () ⟨X, Y⟩ P x y) ∧
        seedFixedMass (G := G) weights ≤ seedFixedMass (G := G) p

private theorem rejected_law : ¬ arena.{u,v,w,s}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{u+1}
  let X := PUnit.{v+1}
  let Y := PUnit.{w+1}
  let P : X → Y → ℝ := fun _ _ => 1
  let S := PUnit.{s+1}
  let weights : S → ℝ := fun _ => 1
  let f : X → S → Y := fun _ _ => PUnit.unit
  obtain ⟨_, total, _, marginal, _⟩ := altered (G := G) weights (by simp [weights])
    (by simp [weights]) f (fun _ _ _ => Subsingleton.elim _ _) P
    (by intro x y; cases y; simp [P, weights, f])
  have zero := marginal (PUnit.unit : X) (PUnit.unit : Y)
  change (∑ t, if t PUnit.unit = PUnit.unit then tableLaw weights f t else 0) = 0 at zero
  have hit (t : X → Y) : t PUnit.unit = PUnit.unit := Subsingleton.elim _ _
  simp only [hit, ite_true, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{u,v,w,s} (type_of% (@calibration_table_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@calibration_table_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨⟨PUnit.{v+1}, PUnit.{w+1}⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
    intro equal
    have eval := congrFun (congrFun equal PUnit.unit) PUnit.unit
    exact zero_ne_one eval

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@calibration_table_law) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration.Pushforward.marginal
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration.Pushforward.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,s}⟩
  objectArena := .source ⟨arena.{u,v,w,s}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,s} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg",
        "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Pushforward

namespace Support

set_option linter.checkUnivs false in
abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
      [Fintype (X → Y)] [DecidableEq Y]
      (H : Subgroup G) (P : X → Y → ℝ) (p : (X → Y) → ℝ)
      (_pn : ∀ t, 0 ≤ p t) (_pt : ∑ t, p t = 1) (_pi : ∀ (g : G) t, p (g • t) = p t)
      (_pr : ∀ x y, (∑ t, if t x = y then p t else 0) = P x y),
      ∃ (U : Type (max v w)) (_ : Fintype U) (_ : MulAction G U)
        (q : U → ℝ) (f : X → U → Y),
        (∀ t, 0 < q t) ∧ (∑ t, q t = 1) ∧ (∀ (g : G) t, q (g • t) = q t) ∧
        (∀ x y, (∑ t, if f x t = y then q t else 0) = R.readout () ⟨X, Y⟩ P x y) ∧
        (∀ (g : G) x t, f (g • x) (g • t) = g • f x t) ∧
        seedFixedMass (G := H) q = seedFixedMass (G := H) p

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{u+1}
  let X := PUnit.{v+1}
  let Y := PUnit.{w+1}
  let P : X → Y → ℝ := fun _ _ => 1
  let p : (X → Y) → ℝ := fun _ => 1
  have hit (t : X → Y) : t PUnit.unit = PUnit.unit := Subsingleton.elim _ _
  have tableTotal : ∑ t, p t = 1 := by simp [p]
  obtain ⟨S, _, _, a, f, _, total, _, marginal, _, _⟩ :=
    altered (G := G) (⊤ : Subgroup G) P p (by simp [p]) tableTotal
      (fun _ _ => rfl) (by
        intro x y
        cases x
        cases y
        simpa only [hit, ite_true] using tableTotal)
  have zero := marginal (PUnit.unit : X) (PUnit.unit : Y)
  change (∑ s, if f PUnit.unit s = PUnit.unit then a s else 0) = 0 at zero
  have hitSeed (s : S) : f PUnit.unit s = PUnit.unit := Subsingleton.elim _ _
  simp only [hitSeed, ite_true, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{u,v,w} (type_of% (@positive_table_calibration)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_table_calibration, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨⟨PUnit.{v+1}, PUnit.{w+1}⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
    intro equal
    have eval := congrFun (congrFun equal PUnit.unit) PUnit.unit
    exact zero_ne_one eval

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_table_calibration) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration.Support.marginal
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "arg", "fn",
        "fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Support

end
end Reg.D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration
