import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Reg.Support.DependentFamily
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basis

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

abbrev joinSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ U : CountMat n m, CountMat m n
  State p := Edge (p.2.2.1 * p.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge (p.2.2.1 * p.2.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def reverseEdge {n m : Nat} {M : CountMat n m} (a : Edge M) : Edge M :=
  ⟨a.source, a.target, Fin.rev a.number⟩

def joinActual : Realization joinSignature :=
  realize joinSignature (fun _ _ a => a) (fun e => nomatch e)

def joinRejected : Realization joinSignature :=
  realize joinSignature (fun _ _ a => reverseEdge a) (fun e => nomatch e)

def joinArena : Arena where
  signature := joinSignature
  Law r := ∀ {n m : Nat} (U : CountMat n m) (V : CountMat m n)
    (a : Edge (U * V)),
    join U V (split U V a).1 (split U V a).2 (by rfl) =
      r.readout () ⟨n, m, U, V⟩ a

theorem join_rejected_law : ¬ joinArena.Law joinRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 2
  let V : CountMat 1 1 := fun _ _ => 1
  have hUV : (U * V) 0 0 = 2 := by
    change (∑ _ : Fin 1, (2 : Nat) * 1) = 2
    simp
  let a : Edge (U * V) :=
    ⟨0, 0, hUV.symm ▸ (0 : Fin 2)⟩
  have hh := h U V a
  rw [join_split] at hh
  have hn := congrArg (fun e : Edge (U * V) => e.number.val) hh
  simp [joinRejected, realize, reverseEdge, U, V, a] at hn

def joinRegistration : Registration joinArena (joinArena.Law joinActual) where
  actual := joinActual
  bridge := Iff.rfl
  variation := ⟨by
    intro n m U V a
    simpa [joinActual, realize] using join_split U V a,
    joinRejected, join_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨joinRejected, ?_, rfl, join_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 2
    let V : CountMat 1 1 := fun _ _ => 1
    have hUV : (U * V) 0 0 = 2 := by
      change (∑ _ : Fin 1, (2 : Nat) * 1) = 2
      simp
    let a : Edge (U * V) :=
      ⟨0, 0, hUV.symm ▸ (0 : Fin 2)⟩
    let b : Edge (U * V) :=
      ⟨0, 0, hUV.symm ▸ (1 : Fin 2)⟩
    change ∃ p : joinSignature.Params, ∃ x y : joinSignature.State p, x ≠ y
    exact ⟨⟨1, 1, U, V⟩, a, b, by simp [a, b]⟩

register_information_theorem join_split in joinArena
  readout via (realize joinSignature (fun _ _ a => a) (fun e => nomatch e))
  realizes joinRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

abbrev splitSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, CountMat n m
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def splitActual : Realization splitSignature :=
  realize splitSignature (fun _ _ a => a) (fun e => nomatch e)

def splitRejected : Realization splitSignature :=
  realize splitSignature (fun _ _ a => reverseEdge a) (fun e => nomatch e)

def splitArena : Arena where
  signature := splitSignature
  Law r := ∀ {n m : Nat} (U : CountMat n m) (V : CountMat m n)
    (a : Edge U) (b : Edge V) (h : a.target = b.source),
    split U V (join U V a b h) =
      (r.readout () ⟨n, m, U⟩ a, b)

theorem split_rejected_law : ¬ splitArena.Law splitRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 2
  let V : CountMat 1 1 := fun _ _ => 1
  have hU : U 0 0 = 2 := by rfl
  let a : Edge U := ⟨0, 0, hU.symm ▸ (0 : Fin 2)⟩
  let b : Edge V := ⟨0, 0, 0⟩
  have hh := h U V a b rfl
  rw [split_join] at hh
  have hfirst := congrArg (fun p : Edge U × Edge V => p.1) hh
  have hn := congrArg (fun e : Edge U => e.number.val) hfirst
  simp [splitRejected, realize, reverseEdge, U, V, a, b] at hn

def splitRegistration : Registration splitArena (splitArena.Law splitActual) where
  actual := splitActual
  bridge := Iff.rfl
  variation := ⟨by
    intro n m U V a b h
    simpa [splitActual, realize] using split_join U V a b h,
    splitRejected, split_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨splitRejected, ?_, rfl, split_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 2
    have hU : U 0 0 = 2 := by rfl
    let a : Edge U := ⟨0, 0, hU.symm ▸ (0 : Fin 2)⟩
    let b : Edge U := ⟨0, 0, hU.symm ▸ (1 : Fin 2)⟩
    change ∃ p : splitSignature.Params, ∃ x y : splitSignature.State p, x ≠ y
    refine ⟨⟨1, 1, U⟩, a, b, ?_⟩
    intro h
    have hn := congrArg (fun e : Edge U => e.number.val) h
    exact Nat.zero_ne_one hn

register_information_theorem split_join in splitArena
  readout via (realize splitSignature (fun _ _ a => a) (fun e => nomatch e))
  realizes splitRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms joinRegistration
#print axioms splitRegistration

end Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
