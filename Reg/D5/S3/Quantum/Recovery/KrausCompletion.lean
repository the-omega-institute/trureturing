import D5.S3.Quantum.Recovery.KrausCompletion
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.KrausCompletion
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open LeanInformationAudit Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder Matrix
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.KrausCompletion
universe u v w z

namespace RowReset
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (v : b) (B : Matrix c a ℂ) (X : Matrix a a ℂ),
    (∑ j, rowReset v B j * X * (rowReset v B j)ᴴ) =
      Matrix.trace (B * R.readout () a X * Bᴴ) • Matrix.single v v (1 : ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  exact @row_reset_action.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} (Fin 1)
  let b := ULift.{v} (Fin 1)
  let c := ULift.{w} (Fin 1)
  let v : b := ⟨0⟩
  let B : Matrix c a ℂ := fun _ _ => 1
  have hh := h (a := a) (b := b) (c := c) v B 1
  rw [row_reset_action] at hh
  have he := congrArg (fun M : Matrix b b ℂ => M v v) hh
  simp only [rejected, realize, signature, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.trace_zero, zero_smul, Matrix.mul_one] at he
  norm_num [B, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, Fintype.sum_unique] at he
  change (∑ _ : a, (1 : ℂ) * star 1) = 0 at he
  norm_num at he

def registration : Registration arena.{u,v,w} (arena.Law actual) where
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
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

register_information_theorem row_reset_action in arena
  readout via (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.KrausCompletion
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)
#print axioms registration
end RowReset

namespace CompleteAction
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {s : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype s]
    (K : s → Matrix b a ℂ) (P : Matrix a a ℂ)
    (v : b) (hP : Pᴴ = P) (hPP : P * P = P) (X : Matrix a a ℂ),
    (∑ i, completeKraus K P v i * X * (completeKraus K P v i)ᴴ) =
      (∑ i, K i * X * (K i)ᴴ) +
        Matrix.trace ((1 - P) * R.readout () a X) • Matrix.single v v (1 : ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  exact @complete_kraus_action.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} (Fin 1)
  let b := ULift.{v} (Fin 1)
  let s := ULift.{w} (Fin 1)
  let v : b := ⟨0⟩
  have hh := h (a := a) (b := b) (s := s) 0 0 v (by simp) (by simp) 1
  rw [complete_kraus_action _ _ _ (by simp) (by simp)] at hh
  have he := congrArg (fun M : Matrix b b ℂ => M v v) hh
  norm_num [rejected, realize, signature, Matrix.trace, Matrix.single] at he

def registration : Registration arena.{u,v,w} (arena.Law actual) where
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
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

register_information_theorem complete_kraus_action in arena
  readout via (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.KrausCompletion
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 13 }] })
  escape continues (open)
#print axioms registration
end CompleteAction

namespace CompleteChannel
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {s : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype s]
    (K : s → Matrix b a ℂ) (P : Matrix a a ℂ)
    (v : b) (hP : Pᴴ = P) (hPP : P * P = P)
    (hK : (∑ i, (K i)ᴴ * K i) = P),
    ∃ channel : QuantumChannel a b, ∀ X : Matrix a a ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (R.readout () a X))) =
      (∑ i, K i * X * (K i)ᴴ) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v (1 : ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  exact @complete_quantum_channel.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} (Fin 1)
  let b := ULift.{v} (Fin 1)
  let s := ULift.{w} (Fin 1)
  let v : b := ⟨0⟩
  obtain ⟨channel, hc⟩ := h (a := a) (b := b) (s := s) 0 0 v
    (by simp) (by simp) (by simp)
  have hh := hc (1 : Matrix a a ℂ)
  have he := congrArg (fun M : Matrix b b ℂ => M v v) hh
  norm_num [rejected, realize, signature, Matrix.trace, Matrix.single] at he

def registration : Registration arena.{u,v,w} (arena.Law actual) where
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
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

register_information_theorem complete_quantum_channel in arena
  readout via (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.KrausCompletion
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg",
        "arg", "arg"]
      stateBinder := 15 }] })
  escape continues (open)
#print axioms registration
end CompleteChannel

end Reg.D5.S3.Quantum.Recovery.KrausCompletion
