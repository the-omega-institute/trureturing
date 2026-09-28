import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
open LeanInformationAudit Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder Matrix
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
universe u v w z

namespace Scalar
abbrev signature : Signature where
  Params := (_ : Type u) × Type v
  State p := p.2 → Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.2 → Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {d : Type u} {s : Type v} [Fintype d] [DecidableEq d] [Fintype s]
    (F : s → Matrix d d ℂ)
    (hF : ∀ X : Matrix d d ℂ, (∑ a, F a * X * (F a)ᴴ) = X) (j₀ : d) (a : s),
      F a = R.readout () ⟨d, s⟩ F a j₀ j₀ • (1 : Matrix d d ℂ)

theorem actual_law : arena.{u,v}.Law actual := by
  exact @identity_kraus_scalar.{u,v}

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let s := ULift.{v} (Fin 1)
  let i : d := ⟨0⟩
  let j : s := ⟨0⟩
  have hF : ∀ X : Matrix d d ℂ, (∑ _a : s, (1 : Matrix d d ℂ) * X * (1 : Matrix d d ℂ)ᴴ) = X := by
    intro X
    simp
  have hh := h (fun _ => 1) hF i j
  have he := congrArg (fun M : Matrix d d ℂ => M i i) hh
  norm_num [rejected, realize, signature] at he
  change (1 : ℂ) = 0 at he
  exact one_ne_zero he

def registration : Registration arena.{u,v} (arena.Law actual) where
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
    let s := ULift.{v} (Fin 1)
    let i : d := ⟨0⟩
    let j : s := ⟨0⟩
    refine ⟨⟨d, s⟩, (0 : s → Matrix d d ℂ), (fun _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun F : s → Matrix d d ℂ => F j i i) h
    norm_num [actual, realize, signature] at he

register_information_theorem identity_kraus_scalar in arena
  readout via (realize signature.{u,v} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 5 }] })
  escape continues (open)
#print axioms registration
end Scalar

namespace Commute
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
  Law R := ∀ {d : Type u} {s : Type v} [Fintype d] [DecidableEq d] [Fintype s]
    (F : s → Matrix d d ℂ)
    (hF : ∀ X : Matrix d d ℂ, (∑ a, F a * X * (F a)ᴴ) = X) (a : s) (X : Matrix d d ℂ),
      F a * X = R.readout () d X * F a

theorem actual_law : arena.{u,v}.Law actual := by
  exact @identity_kraus_commute.{u,v}

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let s := ULift.{v} (Fin 1)
  let i : d := ⟨0⟩
  let j : s := ⟨0⟩
  have hF : ∀ X : Matrix d d ℂ, (∑ _a : s, (1 : Matrix d d ℂ) * X * (1 : Matrix d d ℂ)ᴴ) = X := by
    intro X
    simp
  have hh := h (fun _ => 1) hF j 1
  have he := congrArg (fun M : Matrix d d ℂ => M i i) hh
  norm_num [rejected, realize, signature] at he
  change (1 : ℂ) = 0 at he
  exact one_ne_zero he

def registration : Registration arena.{u,v} (arena.Law actual) where
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

register_information_theorem identity_kraus_commute in arena
  readout via (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "arg"]
      stateBinder := 8 }] })
  escape continues (open)
#print axioms registration
end Commute

namespace Products
abbrev signature : Signature where
  Params := (_ : Type u) × (_ : Type v) × Type w
  State p := p.2.2 → Matrix p.2.1 p.1 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.2.2 → Matrix p.2.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {d : Type u} {n : Type v} {s : Type w} {t : Type z}
    [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n] [Fintype s] [Fintype t]
    (E : s → Matrix n d ℂ) (A : t → Matrix d n ℂ)
    (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (j₀ : d) (a c : s),
    (R.readout () ⟨d, n, s⟩ E a)ᴴ * E c =
      (∑ b, star ((A b * E a) j₀ j₀) * ((A b * E c) j₀ j₀)) •
        (1 : Matrix d d ℂ)

theorem actual_law : arena.{u,v,w,z}.Law actual := by
  exact @left_inverse_error_products.{u,v,w,z}

theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let s := ULift.{w} (Fin 1)
  let t := ULift.{z} (Fin 1)
  let i : d := ⟨0⟩
  let j : s := ⟨0⟩
  let E : s → Matrix n d ℂ := fun _ _ _ => 1
  let A : t → Matrix d n ℂ := fun _ _ _ => 1
  have hA : (∑ b, (A b)ᴴ * A b) = 1 := by
    ext j k
    change (∑ _b : t, ∑ _i : d, star (1 : ℂ) * 1) = (1 : Matrix n n ℂ) j k
    simp [Matrix.one_apply, Subsingleton.elim j k]
  have hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X := by
    intro X
    ext j k
    change (∑ _b : t, ∑ _q : n, (∑ _p : n, (1 : ℂ) *
      (∑ _a : s, ∑ l : d, (∑ k : d, (1 : ℂ) * X k l) * star 1)) * star 1) = X j k
    simp [Fintype.sum_unique, Subsingleton.elim j (default : d),
      Subsingleton.elim k (default : d)]
    congr 1 <;> exact Subsingleton.elim _ _
  have hh := h E A hA hleft i j j
  have he := congrArg (fun M : Matrix d d ℂ => M i i) hh
  simp only [rejected, realize, signature, Pi.zero_apply, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.zero_apply] at he
  norm_num [A, E, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_unique] at he
  change (∑ _ : n, star (0 : ℂ) * 1) =
    star (∑ _ : n, (1 : ℂ) * 1) * (∑ _ : n, (1 : ℂ) * 1) at he
  norm_num at he

def registration : Registration arena.{u,v,w,z} (arena.Law actual) where
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
    let n := ULift.{v} (Fin 1)
    let s := ULift.{w} (Fin 1)
    let i : d := ⟨0⟩
    let j : n := ⟨0⟩
    let k : s := ⟨0⟩
    refine ⟨⟨d, n, s⟩, (0 : s → Matrix n d ℂ), (fun _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun E : s → Matrix n d ℂ => E k j i) h
    norm_num [actual, realize, signature] at he

register_information_theorem left_inverse_error_products in arena
  readout via (realize signature.{u,v,w} (fun _ _ X => X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "arg", "fn"]
      stateBinder := 10 }] })
  escape continues (open)
#print axioms registration
end Products

end Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
