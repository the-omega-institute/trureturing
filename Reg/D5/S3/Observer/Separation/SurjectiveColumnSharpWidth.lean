import D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
open _root_.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := (r : ℕ) × (Fin r → Type)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => sharpWidth p.2 m rhoPosition) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ} (_hr : 1 ≤ r) (h : ℕ) (hh : h ≤ r)
    (D : Fin r → Type) [∀ i, Finite (D i)] [∀ i, Nonempty (D i)],
    (∀ (A B Z O : Type) [Finite A] [Finite B] [Finite Z] [Finite O]
      [Nonempty A] [Nonempty B] [Nonempty O]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O) (b₀ : B),
      Function.Surjective (fun a => ψ a b₀) →
      width (Alphabet A B D) (task ψ G) rhoPosition ≤
        width (Alphabet A B D) (task ψ G) (piPosition h) ^ (2^h)) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∀ k : Fin (2*r+3), sharpCapacity D m (piPosition h) k.val = piCount r h m k.val) ∧
      (∀ k : Fin (2*r+3), sharpCapacity D m rhoPosition k.val = rhoCount r m k.val) ∧
      sharpWidth D m (piPosition h) = 2^h*m^(2^(r-h)) ∧
      R.readout () ⟨r,D⟩ m = m^(2^r)) ∧
    (∀ α C : ℝ, α < (2:ℝ)^h → 0<C → ∃ m : ℕ, 2 ≤ m ∧
      C * (sharpWidth D m (piPosition h) : ℝ)^α < (sharpWidth D m rhoPosition : ℝ)) ∧
    (∀ (A B Z O : Type) [Finite A] [Finite B] [Finite Z] [Finite O]
      [Nonempty A] [Nonempty B] (ψ : A → B → Z) (o : O),
      width (Alphabet A B D) (task ψ (fun _ _ => o)) (piPosition h) = 1 ∧
      width (Alphabet A B D) (task ψ (fun _ _ => o)) rhoPosition = 1 ∧
      ∀ C : ℝ,
        (width (Alphabet A B D) (task ψ (fun _ _ => o)) rhoPosition : ℝ) ≤
          C * (width (Alphabet A B D) (task ψ (fun _ _ => o)) (piPosition h) : ℝ)^(2^h : ℕ) →
        1 ≤ C)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := ((h (r := 1) (by decide) 0 (by decide) (fun _ => Unit)).2.1 2 (by decide)).2.2.2
  change (0 : ℕ) = 2^(2^1) at bad
  norm_num at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, fun _ => Unit⟩, (2 : ℕ), (3 : ℕ), ?_⟩
    change sharpWidth (fun _ : Fin 1 => Unit) 2 rhoPosition ≠
      sharpWidth (fun _ : Fin 1 => Unit) 3 rhoPosition
    have two := ((result (r := 1) (by decide) 0 (by decide) (fun _ => Unit)).2.1 2 (by decide)).2.2.2
    have three := ((result (r := 1) (by decide) 0 (by decide) (fun _ => Unit)).2.1 3 (by decide)).2.2.2
    rw [two, three]
    norm_num

register_information_theorem result in arena
  readout via (realize signature (fun _ p m => sharpWidth p.2 m rhoPosition) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.result
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "surjective-column registration is not declaredValidated"

#print axioms registration

end
end Reg.D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
