import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage
import Reg.Support.DependentFamily

/-! Source-bound audit of sequential success for classical permutation ensembles. -/

namespace Reg.D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage

open _root_.D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Convexity

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe sequential success as the transcript decoder varies. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ m : ℕ, Σ _ : StdSimplex ℝ (Fin m),
    Σ _ : Fin m → Equiv.Perm (Fin n), Σ _ : StdSimplex ℝ (Fin n),
      Fin n → Fin n → StdSimplex ℝ (Fin n)
  State p := Fin p.1 → Fin p.1 → Fin p.1 → Fin p.1 → StdSimplex ℝ (Fin p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p δ => sequentialSuccess p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 δ)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the ensemble, every parallel comparison, and the strict sequential advantage. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∃ (n m : ℕ) (p : StdSimplex ℝ (Fin m)) (π : Fin m → Equiv.Perm (Fin n))
    (q₁ : StdSimplex ℝ (Fin n)) (q₂ : Fin n → Fin n → StdSimplex ℝ (Fin n))
    (δ : Fin n → Fin n → Fin n → Fin n → StdSimplex ℝ (Fin m)) (c : ℝ),
    (∀ (q : StdSimplex ℝ (Fin n × Fin n))
      (d : (Fin n × Fin n) → (Fin n × Fin n) → StdSimplex ℝ (Fin m)),
      parallelSuccess p π q d ≤ c) ∧ c < r.readout () ⟨n, m, p, π, q₁, q₂⟩ δ

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨n, m, p, π, q₁, q₂, δ, c, hparallel, hsequential⟩
  let q := q₁.map (fun x => (x, x))
  have hbound := hparallel q (fun _ _ => p)
  have hnonneg : 0 ≤ parallelSuccess p π q (fun _ _ => p) := by
    unfold parallelSuccess
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (p.weights_nonneg i)
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (q.weights_nonneg x) (p.weights_nonneg i)
  change c < (0 : ℝ) at hsequential
  exact (not_lt_of_ge (hnonneg.trans hbound)) hsequential

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 2, .single 0, (fun _ => Equiv.refl _), .single 0,
    (fun _ _ => .single 0)⟩, (fun _ _ _ _ => .single 0),
    (fun _ _ _ _ => .single 1), ?_⟩
  change sequentialSuccess (StdSimplex.single (0 : Fin 2)) (fun _ => Equiv.refl (Fin 1))
      (.single 0) (fun _ _ => .single 0) (fun _ _ _ _ => .single 0) ≠
    sequentialSuccess (StdSimplex.single (0 : Fin 2)) (fun _ => Equiv.refl (Fin 1))
      (.single 0) (fun _ _ => .single 0) (fun _ _ _ _ => .single 1)
  norm_num [sequentialSuccess, Fin.sum_univ_succ, StdSimplex.weights_single,
    Finsupp.single_apply]

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
      (@_root_.D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature
      (fun _ p δ => sequentialSuccess p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 δ)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage
    definition := some {
      owner := `D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage
      name := `D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage.claim
      path := #[] }
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.ClassicalPermutationSequentialAdvantage
