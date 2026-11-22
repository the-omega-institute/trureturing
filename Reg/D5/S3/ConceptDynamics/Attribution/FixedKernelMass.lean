import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.FixedKernelMass
import Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers

/-! The upper bound on fixed seed mass reads the kernel on stabilizer-fixed outputs. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.FixedKernelMass

open _root_.D5.S3.ConceptDynamics.Attribution.FixedKernelMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers (signature actual rejected)
open LeanInformationAudit
open Finset

universe u v w s

noncomputable section

abbrev arena : Arena where
  signature := signature.{v,w}
  Law R :=
    ∀ {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
      [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] (P : X → Y → ℝ),
      (∀ x y, 0 ≤ P x y) → (∀ x, ∑ y, P x y = 1) →
      (∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) →
      ∃ x₀ : X, (∀ x, rowFixedMass (G := G) P x₀ ≤ rowFixedMass (G := G) P x) ∧
        (∀ (T : Type s) [Fintype T] [MulAction G T] (v : T → ℝ) (F : X → T → Y),
          (∀ t, 0 ≤ v t) →
          (∀ x y, (∑ t, if F x t = y then v t else 0) = P x y) →
          (∀ g : G, ∀ x t, F (g • x) (g • t) = g • F x t) →
          seedFixedMass (G := G) v ≤ rowFixedMass (G := G) (R.readout () ⟨X, Y⟩ P) x₀) ∧
        ∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S)
          (w : S → ℝ) (f : X → S → Y),
          (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
          (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
          (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
          seedFixedMass (G := G) w = rowFixedMass (G := G) P x₀

private theorem rejected_law : ¬ arena.{u,v,w,s}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{u+1}
  let P : PUnit.{v+1} → PUnit.{w+1} → ℝ := fun _ _ => 1
  obtain ⟨x₀, _, bound, _⟩ := altered (G := G) P (by simp [P]) (by simp [P]) (by simp [P])
  let mass : PUnit.{s+1} → ℝ := fun _ => 1
  let readout : PUnit.{v+1} → PUnit.{s+1} → PUnit.{w+1} := fun _ _ => PUnit.unit
  have impossible := bound PUnit.{s+1} mass readout (by simp [mass])
    (by intro x y; cases y; simp [P, mass, readout]) (by simp [readout])
  change seedFixedMass (G := G) mass ≤ rowFixedMass (G := G) (fun _ _ => 0) x₀ at impossible
  have fixed : ∀ (z : PUnit.{s+1}) (g : G), g • z = z := fun _ _ => Subsingleton.elim _ _
  simp [seedFixedMass, rowFixedMass, mass, fixed] at impossible
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) impossible

def family : Registration arena.{u,v,w,s} (type_of% (@maximal_fixed_seed_mass)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@maximal_fixed_seed_mass, rejected, rejected_law⟩
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
    (@maximal_fixed_seed_mass) (Realization signature.{v,w}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.FixedKernelMass.fixedMass
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.FixedKernelMass.family
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
    owner := `D5.S3.ConceptDynamics.Attribution.FixedKernelMass
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.FixedKernelMass
