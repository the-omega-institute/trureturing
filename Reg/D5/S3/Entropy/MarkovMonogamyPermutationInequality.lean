import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.MarkovMonogamyPermutationInequality
import Reg.Support.DependentFamily

/-! Source-bound audit of the finite Markov permutation inequality. -/

namespace Reg.D5.S3.Entropy.MarkovMonogamyPermutationInequality

open _root_.D5.S3.Entropy.MarkovMonogamyPermutationInequality
open _root_.D5.S3.Entropy.Mixing.MixtureEntropyBracket
open _root_.D5.S3.Entropy.MutualInformation
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Divergence.ChainRule
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Construct the pair law from a position's mass function and its onward transition. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : ℕ → Type, Fin n
  State p := p.2.1 (p.1 - 1 - p.2.2.val) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p :=
    (p.2.1 (p.1 - 1 - p.2.2.val) → p.2.1 (p.1 + p.2.2.val) → ℝ) →
      (p.2.1 (p.1 - 1 - p.2.2.val) × p.2.1 (p.1 + p.2.2.val) → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => mixtureJoint w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 2) (fun e => nomatch e)

/-- Retain every chain hypothesis and replace the right-hand pair-law constructor. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (n : ℕ) (α : ℕ → Type) [∀ t, Fintype (α t)]
      (p : α 0 → ℝ) (k : ∀ t, α t → α (t + 1) → ℝ),
      ((∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1) →
      (∀ t, t + 1 < 2 * n → (∀ a b, 0 ≤ k t a b) ∧ ∀ a, ∑ b, k t a b = 1) →
      ∀ f : Equiv.Perm (Fin n),
        (∑ i : Fin n, mutualInformation
          (mixtureJoint
            (mixture p (composedTransition k 0 (n - 1 - i.val) (Nat.zero_le _)))
            (composedTransition k (n - 1 - i.val) (n + (f i).val) (by omega)))) ≤
        ∑ i : Fin n, mutualInformation
          (R.readout () ⟨n, α, i⟩
            (mixture p (composedTransition k 0 (n - 1 - i.val) (Nat.zero_le _)))
            (composedTransition k (n - 1 - i.val) (n + i.val) (by omega)))

private theorem singleton_transition (s t : ℕ) (h : s ≤ t) (a b : Fin 1) :
    composedTransition (α := fun _ => Fin 1) (fun _ _ _ => 1) s t h a b = 1 := by
  classical
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  induction t, h using Nat.le_induction with
  | base => simp [composedTransition, Nat.leRecOn_self, Subsingleton.elim a (0 : Fin 1)]
  | succ t h ih =>
    simpa [composedTransition, Nat.leRecOn_succ h] using ih

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (fun _ => Fin 1) (fun _ => 1) (fun _ _ _ => 1)
    (by constructor <;> simp) (by intro t ht; constructor <;> simp) (Equiv.refl _)
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  norm_num [rejected, realize, mutualInformation, klDivergence, marginal,
    mixtureJoint, mixture, singleton_transition, Real.log_div] at hbad
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (fun _ => Fin 1), 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h (fun _ _ => 1)) (0, 0)
  norm_num [actual, realize, mixtureJoint] at he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Entropy.MarkovMonogamyPermutationInequality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Entropy.MarkovMonogamyPermutationInequality.unit
  realizationName :=
    `Reg.D5.S3.Entropy.MarkovMonogamyPermutationInequality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => mixtureJoint w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.MarkovMonogamyPermutationInequality
    definition := some {
      owner := `D5.S3.Entropy.MarkovMonogamyPermutationInequality
      name := `D5.S3.Entropy.MarkovMonogamyPermutationInequality.claim
      path := #[] }
    coordinates := #[0, 1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Entropy.MarkovMonogamyPermutationInequality
