import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass
import Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers

/-! The full fixed mass criterion reads the calibrated kernel on the deterministic readout marginals. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass

open _root_.D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass
open _root_.D5.S3.ConceptDynamics.Attribution.FixedKernelMass (seedFixedMass)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers (signature actual rejected)
open LeanInformationAudit
open Finset

universe u v w

noncomputable section

abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
      [Fintype X] [Fintype Y] [DecidableEq Y] (H : Subgroup G) (P : X → Y → ℝ),
      (∀ x y, 0 ≤ P x y) → (∀ x, ∑ y, P x y = 1) →
      (∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) →
      let N := Subgroup.normalClosure (H : Set G)
      (∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S)
        (a : S → ℝ) (f : X → S → Y),
        (∀ s, 0 < a s) ∧ (∑ s, a s = 1) ∧ (∀ g : G, ∀ s, a (g • s) = a s) ∧
        (∀ x y, (∑ s, if f x s = y then a s else 0) = R.readout () ⟨X, Y⟩ P x y) ∧
        (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
        seedFixedMass (G := H) a = 1) ↔
      ∀ x y, 0 < P x y → ∀ n : N, n • x = x → n • y = y

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{u+1}
  let X := PUnit.{v+1}
  let Y := PUnit.{w+1}
  let P : X → Y → ℝ := fun _ _ => 1
  obtain ⟨S, _, _, a, f, _, total, _, marginal, _, _⟩ :=
    (altered (G := G) (⊤ : Subgroup G) P (by simp [P]) (by simp [P]) (by simp [P])).mpr
      (fun _ _ _ _ _ => Subsingleton.elim _ _)
  have zero := marginal (PUnit.unit : X) (PUnit.unit : Y)
  change (∑ s, if f PUnit.unit s = PUnit.unit then a s else 0) = 0 at zero
  have hit (s : S) : f PUnit.unit s = PUnit.unit := Subsingleton.elim _ _
  simp only [hit, if_true, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{u,v,w} (type_of% (@full_subgroup_fixed_seed_mass_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@full_subgroup_fixed_seed_mass_iff, rejected, rejected_law⟩
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
    (@full_subgroup_fixed_seed_mass_iff) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass.fixedMass
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass.family
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
    owner := `D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "body",
        "body", "arg", "fn", "fn"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass
