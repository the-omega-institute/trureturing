import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity
import Reg.Support.DependentFamily

/-! The bound reads the subgroup-fixed mass of the seed weights. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity

open _root_.D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity
open _root_.D5.S3.ConceptDynamics.Attribution.FixedKernelMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

universe u v

noncomputable section

abbrev signature : Signature where
  Params := Type v
  State S := S → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ S := S → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law R :=
    ∀ {G : Type u} {S : Type v} [Group G] [MulAction G S] [Fintype S]
      (H : Subgroup G) (a : S → ℝ)
      (_nonneg : ∀ s, 0 ≤ a s) (_invariant : ∀ (g : G) s, a (g • s) = a s) (d : ℕ),
      let lossSets := Set.range fun g : G => {s : S | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
      let N := Subgroup.normalClosure (H : Set G)
      let total := ∑ s, a s
      (∀ s : S, 0 < a s → (¬∀ n : N, n • s = s) →
        d ≤ Nat.card {B : lossSets // s ∈ B.val}) →
        (d : ℝ) * (total - seedFixedMass (G := N) a) ≤
          (Nat.card ↥lossSets : ℝ) * (total - seedFixedMass (G := H) (R.readout () S a))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{u+1}
  let S := PUnit.{v+1}
  let H : Subgroup G := ⊤
  let a : S → ℝ := fun _ => 0
  let broken (g : G) : Set S := {s | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
  have card : Nat.card ↥(Set.range broken) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨broken PUnit.unit, ⟨PUnit.unit, rfl⟩⟩, ?_⟩
    rintro ⟨_, ⟨g, rfl⟩⟩
    cases g
    rfl
  have bad := altered (G := G) H a (fun _ => le_rfl) (fun _ _ => rfl) 0
    (fun _ _ _ => Nat.zero_le _)
  change ((0 : ℕ) : ℝ) * _ ≤ (Nat.card ↥(Set.range broken) : ℝ) *
    ((∑ s, a s) - seedFixedMass (G := H) (fun _ : S => 1)) at bad
  have fixed (s : S) (h : H) : h • s = s := Subsingleton.elim _ _
  apply (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1))
  simpa [card, a, seedFixedMass, fixed] using bad

def family : Registration arena.{u,v} (type_of% (@normal_closure_loss_mul_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normal_closure_loss_mul_le, rejected, rejected_law⟩
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
    refine ⟨PUnit.{v+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun equal PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normal_closure_loss_mul_le) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity.lossMultiplicity
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity
