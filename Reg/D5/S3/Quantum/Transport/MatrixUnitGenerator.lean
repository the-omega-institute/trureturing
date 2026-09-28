import D5.S3.Quantum.Transport.MatrixUnitGenerator
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Transport.MatrixUnitGenerator
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder
noncomputable section
namespace Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator
universe u v w z

namespace Algebraic

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {d : Type u} {n : Type v}
    [Fintype d] [DecidableEq d] [Nonempty d] [Fintype n] [DecidableEq n]
    (F D : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i)
    (hD : ∀ i j k l, D i j * F k l + F i j * D k l =
      if j = k then D i l else 0)
    (hDstar : ∀ i j, (D i j)ᴴ = D j i),
    (transportGenerator F D)ᴴ = -transportGenerator F D ∧
      (∀ i j, transportGenerator F D * F i j - F i j * transportGenerator F D =
        r.readout () ⟨d,n⟩ D i j) ∧
      transportGenerator F D * unitSupport F - unitSupport F * transportGenerator F D =
        supportVelocity D

theorem actual_law : arena.{u,v}.Law actual := by
  intro d n _ _ _ _ _ F D hmul hstar hD hDstar
  exact matrix_unit_transport_generator F D hmul hstar hD hDstar

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hr := h (d := ULift.{u} (Fin 1)) (n := ULift.{v} (Fin 1))
    (fun _ _ => 0) (fun _ _ => 0)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have heq := hr.2.1 (ULift.up 0) (ULift.up 0)
  have hz : (0 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v} (arena.Law actual) where
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
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩,
      (fun _ _ _ _ => (0 : ℂ)), (fun _ _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun (congrFun (congrFun h
      (ULift.up 0)) (ULift.up 0)) (ULift.up 0)) (ULift.up 0))

register_information_theorem matrix_unit_transport_generator in arena
  readout via (realize signature.{u,v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration
end Algebraic

namespace RealPath

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {d : Type u} {n : Type v}
    [Fintype d] [DecidableEq d] [Nonempty d] [Fintype n] [DecidableEq n]
    (F : ℝ → d → d → Matrix n n ℂ) (D : d → d → Matrix n n ℂ) (t : ℝ)
    (hmul : ∀ u i j k l, F u i j * F u k l = if j = k then F u i l else 0)
    (hstar : ∀ u i j, (F u i j)ᴴ = F u j i)
    (hderiv : ∀ i j a b, HasDerivAt (fun u => F u i j a b) (D i j a b) t),
    (transportGenerator (F t) D)ᴴ = -transportGenerator (F t) D ∧
      (∀ i j, transportGenerator (F t) D * F t i j - F t i j * transportGenerator (F t) D =
        r.readout () ⟨d,n⟩ D i j) ∧
      transportGenerator (F t) D * unitSupport (F t) -
        unitSupport (F t) * transportGenerator (F t) D = supportVelocity D

theorem actual_law : arena.{u,v}.Law actual := by
  intro d n _ _ _ _ _ F D t hmul hstar hderiv
  exact generator_from_real_path F D t hmul hstar hderiv

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hr := h (d := ULift.{u} (Fin 1)) (n := ULift.{v} (Fin 1))
    (fun _ _ _ => 0) (fun _ _ => 0) 0
    (by intros; simp) (by intros; simp)
    (by intros; exact hasDerivAt_const _ _)
  have heq := hr.2.1 (ULift.up 0) (ULift.up 0)
  have hz : (0 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v} (arena.Law actual) where
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
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩,
      (fun _ _ _ _ => (0 : ℂ)), (fun _ _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun (congrFun (congrFun h
      (ULift.up 0)) (ULift.up 0)) (ULift.up 0)) (ULift.up 0))

register_information_theorem generator_from_real_path in arena
  readout via (realize signature.{u,v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "arg", "fn", "fn"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration
end RealPath

end Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator
