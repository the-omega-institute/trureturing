import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
universe u v w

namespace Support

abbrev signature : Signature where
  Params := Σ _ : Type u, Σ _ : Type v, Type w
  State p := p.2.2 → Matrix p.1 p.2.1 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.2.2 → Matrix p.1 p.2.1 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {n : Type u} {d : Type v} {s : Type w}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] [Fintype s]
    (E : s → Matrix n d ℂ) (a : s),
    spectralSupport (∑ b, E b * (E b)ᴴ) * E a = r.readout () ⟨n,d,s⟩ E a

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d s _ _ _ _ _ E a
  exact spectral_support_on_kraus E a

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have heq := h (n := ULift.{u} (Fin 1)) (d := ULift.{v} (Fin 1))
    (s := ULift.{w} (Fin 1)) (fun _ => 0) (ULift.up 0)
  have hz : (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

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
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1), ULift.{w} (Fin 1)⟩,
      (fun _ _ _ => (0 : ℂ)), (fun _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun (congrFun h (ULift.up 0))
      (ULift.up 0)) (ULift.up 0))

register_information_theorem spectral_support_on_kraus in arena
  readout via (realize signature.{u,v,w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "fn"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration
end Support

namespace Candidate

abbrev signature : Signature where
  Params := Type v
  State p := CStarMatrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => CStarMatrix.ofMatrix.symm x) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{v}
  Law r := ∀ {n : Type u} {d : Type v} {s : Type w}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] [Fintype s]
    (E : s → Matrix n d ℂ) (v : d),
    let Q := ∑ a, E a * (E a)ᴴ
    let P := spectralSupport Q
    let W := spectralInverseSqrt Q
    ∃ recovery : QuantumChannel n d, ∀ X : Matrix n n ℂ,
      r.readout () d (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      (∑ a, (E a)ᴴ * W * X * W * E a) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v 1

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d s _ _ _ _ _ E v
  exact spectral_transpose_candidate E v

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  obtain ⟨recovery, hr⟩ := h (n := ULift.{u} (Fin 1)) (d := ULift.{v} (Fin 1))
    (s := ULift.{w} (Fin 1)) (fun _ => 0) (ULift.up 0)
  have heq := hr 0
  have hz : (show Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ from
      fun _ _ => 1) = 0 := by
    simpa [rejected, realize] using heq
  exact one_ne_zero (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

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
    refine ⟨ULift.{v} (Fin 1), CStarMatrix.ofMatrix (fun _ _ => (0 : ℂ)),
      CStarMatrix.ofMatrix (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

register_information_theorem spectral_transpose_candidate in arena
  readout via (realize signature.{v}
    (fun _ _ x => CStarMatrix.ofMatrix.symm x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "body",
        "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration
end Candidate

end Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
