import D5.S3.Quantum.Reduction.IsometricCompression
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Reduction.IsometricCompression
open LeanInformationAudit
open scoped Matrix BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Reduction.IsometricCompression
universe u v w

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p.1 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {n : Type u} {d : Type v}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    {ι : Type w} (U : Matrix n d ℂ)
    (K : ι → Matrix n n ℂ) (k : ι → Matrix d d ℂ)
    (h : ∀ a, K a * U = U * k a) (w : List ι),
    (w.map K).prod * U = r.readout () ⟨n,d⟩ U * (w.map k).prod

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d _ _ _ _ ι U K k h w
  exact word_intertwines U K k h w

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let U : Matrix (ULift.{u} (Fin 1)) (ULift.{v} (Fin 1)) ℂ := fun _ _ => 1
  have heq := h U (fun _ : ULift.{w} (Fin 1) => 0) (fun _ => 0)
    (by intro a; simp) []
  have hz : U = 0 := by simpa [rejected, realize] using heq
  have hentry := congrFun (congrFun hz (ULift.up 0)) (ULift.up 0)
  exact one_ne_zero (show (1 : ℂ) = 0 from hentry)

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩, (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

register_information_theorem word_intertwines in arena
  readout via (realize signature.{u,v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Reduction.IsometricCompression
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Quantum.Reduction.IsometricCompression
