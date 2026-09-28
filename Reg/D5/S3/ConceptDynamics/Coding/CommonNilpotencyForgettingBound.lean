import D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => n + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {A : CountMat n n} {Q : Type},
    [Fintype Q] → ∀ (L : IncomingLift A Q),
    let D := differenceSpace L.project
    let T := edgeLinear L
    let W := imageChain T D
    D = LinearMap.ker (Finsupp.lmapDomain ℚ ℚ L.project) ∧
    Module.finrank ℚ D = Fintype.card Q - R.readout () () n ∧
    (∀ a, D.map (T a) ≤ D) ∧
    (∀ (w : List (Edge A)),
      (∀ (i j : Fin n) (p : FinitePath A w.length i j), pathWord p ≠ w) →
      wordOperator T w = 0) ∧
    (∀ d, Forgets L d ↔ ∀ w : List (Edge A), w.length = d →
      D.map (wordOperator T w) = ⊥) ∧
    (∀ w : List (Edge A), D.map (wordOperator T w) = ⊥ ↔
      (wordOperator T w).domRestrict D = 0) ∧
    (∀ {d : ℕ} {i j : Fin n} (p : FinitePath A d i j),
      (pathWord p).length = d ∧
      ∀ u : {q : Q // L.project q = j},
        wordOperator T (pathWord p) (Finsupp.single u.val 1) =
          Finsupp.single (L.liftPath p u).val 1) ∧
    W 0 = D ∧
    (∀ j, W (j + 1) = ⨆ a, (W j).map (T a)) ∧
    (∀ j, W j = ⨆ w : {w : List (Edge A) // w.length = j},
      D.map (wordOperator T w.val)) ∧
    (∀ j, W (j + 1) ≤ W j) ∧
    (∀ j, W (j + 1) = W j → ∀ k, W (j + k) = W j) ∧
    (∀ d, Forgets L d ↔ W d = ⊥) ∧
    (∀ d, IsLeast {j | Forgets L j} d ↔ IsLeast {j | W j = ⊥} d) ∧
    ((∃ d, Forgets L d) → ∃ d ≤ Fintype.card Q - n, IsLeast {j | Forgets L j} d) ∧
    ((∃ d, Forgets L d) ↔ W (Fintype.card Q - n) = ⊥) ∧
    (∃ L₀ : IncomingLift (fun (_ _ : Fin 1) => 2) Bool,
      (∀ u, (L₀.lift ⟨0, 0, 0⟩ u).val = u.val) ∧
      (∀ u, (L₀.lift ⟨0, 0, 1⟩ u).val = !u.val) ∧
      ((1 / 2 : ℚ) • (edgeLinear L₀ ⟨0, 0, 0⟩ + edgeLinear L₀ ⟨0, 0, 1⟩)).domRestrict
        (differenceSpace L₀.project) = 0 ∧
      ∀ d, ¬ Forgets L₀ d)

theorem actual_law : arena.Law actual := by
  intro n A Q inst L
  exact common_nilpotency_forgetting_bound L

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A : CountMat 1 1 := fun _ _ => 1
  let L : IncomingLift A Bool := {
    project := fun _ => 0
    onto := by intro v; exact ⟨false, Subsingleton.elim _ _⟩
    lift := fun _ _ => ⟨false, Subsingleton.elim _ _⟩ }
  have htrue := (common_nilpotency_forgetting_bound L).2.1
  have hfalse := (h L).2.1
  change Module.finrank ℚ (differenceSpace L.project) =
    Fintype.card Bool - (1 + 1) at hfalse
  change Module.finrank ℚ (differenceSpace L.project) = Fintype.card Bool - 1 at htrue
  norm_num only [Fintype.card_bool, Nat.reduceAdd, Nat.reduceSub] at hfalse htrue
  omega

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), Nat.zero_ne_one⟩

register_information_theorem common_nilpotency_forgetting_bound in arena
  readout via (realize signature (fun _ _ n => n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.CommonNilpotencyForgettingBound
