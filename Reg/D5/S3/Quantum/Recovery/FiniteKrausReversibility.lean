import D5.S3.Quantum.Recovery.FiniteKrausReversibility
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FiniteKrausReversibility
open LeanInformationAudit Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility
universe v w u

abbrev signature : Signature where
  Params := Type u
  State d := Matrix d d ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ d := Matrix d d ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {s : Type v} {n : Type w} {d : Type u}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]
    [Fintype d] [DecidableEq d]
    (E : s → Matrix n d ℂ) (hTP : (∑ a, (E a)ᴴ * E a) = 1)
    (v : d) (c : Matrix s s ℂ)
    (hE : ∀ a b, (E a)ᴴ * E b = c a b • (1 : Matrix d d ℂ)),
    ∃ r : ℕ, ∃ A : Fin r → Matrix d n ℂ,
      (∑ b, (A b)ᴴ * A b) = 1 ∧
      ∀ X : Matrix d d ℂ,
        (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = R.readout () d X

theorem actual_law : arena.{v,w,u}.Law actual := by
  intro s n d _ _ _ _ _ _ E hTP v c hE
  exact scalar_products_construct_left_inverse E hTP v c hE

theorem rejected_law : ¬ arena.{v,w,u}.Law rejected := by
  intro h
  let s := ULift.{v} (Fin 1)
  let n := ULift.{w} (Fin 1)
  let d := ULift.{u} (Fin 1)
  let i : d := ⟨0⟩
  let E : s → Matrix n d ℂ := fun _ _ _ => 1
  have hTP : (∑ a, (E a)ᴴ * E a) = 1 := by
    ext j k
    change (∑ _a : s, ∑ _b : n, star (1 : ℂ) * 1) = (1 : Matrix d d ℂ) j k
    simp [Matrix.one_apply, Subsingleton.elim j k]
  have hE : ∀ a b, (E a)ᴴ * E b = (1 : ℂ) • (1 : Matrix d d ℂ) := by
    intro a b
    ext j k
    change (∑ _b : n, star (1 : ℂ) * 1) = (1 : ℂ) * (1 : Matrix d d ℂ) j k
    simp [Matrix.one_apply, Subsingleton.elim j k]
  obtain ⟨r, A, _, hrec⟩ := h E hTP i (fun _ _ => 1) hE
  have hzero := hrec (0 : Matrix d d ℂ)
  have hentry := congrArg (fun M : Matrix d d ℂ => M i i) hzero
  norm_num [rejected, realize, signature] at hentry

def registration : Registration arena.{v,w,u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let d := ULift.{u} (Fin 1)
    let i : d := ⟨0⟩
    refine ⟨d, (0 : Matrix d d ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix d d ℂ => M i i) h
    norm_num [actual, realize, signature] at he

register_information_theorem scalar_products_construct_left_inverse in arena
  readout via (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.FiniteKrausReversibility
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg"]
      stateBinder := 16 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Quantum.Recovery.FiniteKrausReversibility
