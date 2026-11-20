import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.PUnit

/-! The stabilizer criterion observes the kernel at a supported fixed output. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers

open _root_.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

universe u v w
noncomputable section

abbrev signature : Signature.{max (v + 1) (w + 1), max v w, 0, max v w, 0} where
  Params := Σ _ : Type v, Type w
  State p := p.1 → p.2 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → p.2 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v,w} :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature.{v,w} :=
  realize signature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
      [Fintype X] [Fintype Y] [DecidableEq Y] (P : X → Y → ℝ), (∀ x y, 0 ≤ P x y) →
      (∀ x, ∑ y, P x y = 1) → (∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) →
      ∀ H : Subgroup G,
      (∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S) (w : S → ℝ) (f : X → S → Y),
        (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
        (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
        (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
        (∃ s : S, H ≤ MulAction.stabilizer G s)) ↔
      (∀ x : X, ∃ y : Y, 0 < R.readout () ⟨X, Y⟩ P x y ∧ ∀ h : H, h • x = x → h • y = y)

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro h
  let P : PUnit.{v+1} → PUnit.{w+1} → ℝ := fun _ _ => 1
  have base := stabilizer_possible_iff (G := PUnit.{u+1}) P (by simp [P])
    (by simp [P]) (by simp [P]) ⊥
  have law := base.mpr (fun x => ⟨PUnit.unit, by simp [P], by simp⟩)
  have alt := (h (G := PUnit.{u+1}) P (by simp [P]) (by simp [P]) (by simp [P]) ⊥).mp law
  obtain ⟨_, invalid, _⟩ := alt PUnit.unit
  exact (lt_irrefl (0 : ℝ)) invalid

private theorem fixed_kernel_dependence :
    ObservationalDependence signature.{v,w} actual := by
  intro _
  refine ⟨⟨PUnit.{v+1}, PUnit.{w+1}⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
  intro equal
  have eval := congrFun (congrFun equal PUnit.unit) PUnit.unit
  exact zero_ne_one eval

def family : Registration arena.{u,v,w} (type_of% (@stabilizer_possible_iff.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stabilizer_possible_iff.{u,v,w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := fixed_kernel_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stabilizer_possible_iff.{u,v,w}) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers.support_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers.family
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
    owner := `D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev exactArena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
      [Fintype X] [Fintype Y] [DecidableEq Y] (P : X → Y → ℝ), (∀ x y, 0 ≤ P x y) →
      (∀ x, ∑ y, P x y = 1) → (∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) →
      ∀ H : Subgroup G,
      (∃ (S : Type (max u v w)) (_ : Fintype S) (_ : MulAction G S) (w : S → ℝ) (f : X → S → Y),
        (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
        (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
        (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
        (∃ s : S, MulAction.stabilizer G s = H)) ↔
      Finite (G ⧸ H) ∧
        (∀ x : X, ∃ y : Y, 0 < R.readout () ⟨X, Y⟩ P x y ∧
          ∀ h : H, h • x = x → h • y = y)

private theorem exact_rejected_law : ¬ exactArena.{u,v,w}.Law rejected := by
  classical
  intro h
  let _ : Finite (PUnit.{u+1} ⧸ (⊥ : Subgroup PUnit.{u+1})) :=
    Finite.of_surjective QuotientGroup.mk QuotientGroup.mk_surjective
  let P : PUnit.{v+1} → PUnit.{w+1} → ℝ := fun _ _ => 1
  have base := exact_stabilizer_possible_iff (G := PUnit.{u+1}) P (by simp [P])
    (by simp [P]) (by simp [P]) ⊥
  have law := base.mpr ⟨inferInstance, fun x => ⟨PUnit.unit, by simp [P], by simp⟩⟩
  have alt := (h (G := PUnit.{u+1}) P (by simp [P]) (by simp [P]) (by simp [P]) ⊥).mp law
  obtain ⟨_, invalid, _⟩ := alt.2 PUnit.unit
  exact (lt_irrefl (0 : ℝ)) invalid

def exactFamily : Registration exactArena.{u,v,w} (type_of% (@exact_stabilizer_possible_iff.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@exact_stabilizer_possible_iff.{u,v,w}, rejected, exact_rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, exact_rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := fixed_kernel_dependence

def exactRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_stabilizer_possible_iff.{u,v,w}) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers.exact_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers.exactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena.{u,v,w}⟩
  objectArena := .source ⟨exactArena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exactArena.{u,v,w} ⟨exactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body",
        "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
