import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.CycleSingleCutMinimax
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.CycleSingleCutMinimax
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.TotalVariation.Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.TotalVariation.CycleSingleCutMinimax
universe u

abbrev signature : Signature where
  Params := Type u
  State B := B → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ B := B → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ μ => μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

/-- Vary the prescribed marginal in the first single-cut conclusion while retaining
the complete source telescope and every other conclusion. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {B : Type u} [Fintype B]
    (n : ℕ) (μ : B → ℝ) (g : Equiv.Perm B)
    (_hμ : Probability μ) (_hinv : ∀ x, μ (g x) = μ x),
    (∀ k : Fin (n + 1), Joint (r.readout () B μ) (cutLaw μ g k) ∧
      ∀ i, error μ g (cutLaw μ g k) i = if i = k then moved μ g else 0) ∧
    (∀ π : Fin (n + 1) → ℝ, Probability π → Joint μ (mixture μ g π) ∧
      ∀ i, error μ g (mixture μ g π) i = moved μ g * π i) ∧
    (∀ P : (Fin (n + 1) → B) → ℝ, Joint μ P → ∀ i, error μ g P i =
      ∑ y, if y (next i) ≠ transport g i (y i) then P y else 0) ∧
    (∀ P : (Fin (n + 1) → B) → ℝ, Joint μ P → moved μ g ≤ ∑ i, error μ g P i) ∧
    (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
      ((∃ P, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
    IsLeast {t | ∃ P : (Fin (n + 1) → B) → ℝ, Joint μ P ∧ worst μ g P = t}
      (moved μ g / (n + 1)) ∧
    ((∃ P : (Fin (n + 1) → B) → ℝ, Joint μ P ∧ ∀ i, error μ g P i ≤ 0) ↔ moved μ g = 0) ∧
    (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) → moved μ g ≤ ∑ i, ε i →
      0 < moved μ g →
      Probability (fun i => ε i / ∑ j, ε j) ∧
      Joint μ (mixture μ g (fun i => ε i / ∑ j, ε j)) ∧
      (∀ i, error μ g (mixture μ g (fun i => ε i / ∑ j, ε j)) i ≤ ε i) ∧
      (∀ i, ε i = 0 → ε i / (∑ j, ε j) = 0)) ∧
    (∀ A : Set (((Fin (n + 1) → B) → ℝ)), Convex ℝ A →
      (∀ k, cutLaw μ g k ∈ A) →
      (∀ π, Probability π → mixture μ g π ∈ A) ∧
      (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
        ((∃ P ∈ A, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
      IsLeast {t | ∃ P ∈ A, Joint μ P ∧ worst μ g P = t} (moved μ g / (n + 1))) ∧
    RestrictedCounterexample

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let μ : V → ℝ := fun _ => 1
  let g : Equiv.Perm V := Equiv.refl V
  have hμ : Probability μ := ⟨fun _ => by norm_num [μ], by simp [μ, V]⟩
  have hz := congrFun (((h 2 μ g hμ (fun _ => rfl)).1 (0 : Fin 3)).1.2 0) ⟨()⟩
  have hp := congrFun (((cycle_single_cut_minimax 2 μ g hμ (fun _ => rfl)).1
    (0 : Fin 3)).1.2 0) ⟨()⟩
  have he : (0 : ℝ) = 1 := by
    simpa [rejected, realize, μ] using hz.symm.trans hp
  norm_num at he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun h ⟨()⟩
  norm_num [actual, realize] at he

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{u + 3, u + 3, u + 1, 1, 1, 0, 1, 1, 0, 0, 0, u + 1, u, 0, u, 0, 0} (@_root_.D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax.{u}) (type_of% (arena.{u})) (type_of% (arena.{u})) (type_of% (realize.{u + 1, u, 0, u, 0} signature.{u} (fun _ _ μ => μ) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "TotalVariation") "CycleSingleCutMinimax") "cycle_single_cut_minimax") "Reg.D5.S3.TotalVariation.CycleSingleCutMinimax/Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u})⟩,
  objectArena := ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  readout := some (realize.{u + 1, u, 0, u, 0} signature.{u} (fun _ _ μ => μ) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.TotalVariation.CycleSingleCutMinimax, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.TotalVariation.CycleSingleCutMinimax
