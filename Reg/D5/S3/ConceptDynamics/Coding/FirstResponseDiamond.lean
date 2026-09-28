import D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Reg.Support.DependentFamily
import Mathlib.Algebra.BigOperators.Fin

open _root_.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond

abbrev signature : Signature where
  Params := Nat
  State q := CountMat q q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := CountMat q q
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q C => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {q r' s : Nat} (C : CountMat q q)
    (leftClass : Fin q → Fin r') (rightClass : Fin q → Fin s)
    (leftRep : Fin r' → Fin q) (rightRep : Fin s → Fin q)
    (hleftRep : ∀ f, leftClass (leftRep f) = f)
    (hrightRep : ∀ h, rightClass (rightRep h) = h)
    (hcolumns : ∀ u v, leftClass u = leftClass v → ∀ i, C i u = C i v)
    (hrows : ∀ u v, rightClass u = rightClass v → ∀ k, C u k = C v k),
    ∃ D : CountMat s r',
      columnMembership leftClass * (r.readout () q C) * columnSelector leftRep =
        (columnMembership leftClass * rowMembership rightClass) * D ∧
      rowSelector rightRep * C * rowMembership rightClass =
        D * (columnMembership leftClass * rowMembership rightClass) ∧
      Nonempty (ExchangeChain ℕ
        (columnMembership leftClass * C * columnSelector leftRep)
        (rowSelector rightRep * C * rowMembership rightClass) 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let C : CountMat 1 1 := fun _ _ => 1
  let lc : Fin 1 → Fin 1 := fun _ => 0
  let rc : Fin 1 → Fin 1 := fun _ => 0
  let lr : Fin 1 → Fin 1 := fun _ => 0
  let rr : Fin 1 → Fin 1 := fun _ => 0
  have hh := h C lc rc lr rr
    (by intro f; exact (Fin.eq_zero f).symm) (by intro g; exact (Fin.eq_zero g).symm)
    (by intro u v huv i; simp [C])
    (by intro u v huv k; simp [C])
  obtain ⟨D, hleft, hright, _⟩ := hh
  have hl := congrFun (congrFun hleft 0) 0
  have hr := congrFun (congrFun hright 0) 0
  have hl' : 0 = D 0 0 := by
    simpa [rejected, realize, Matrix.mul_apply, Fin.sum_univ_succ,
      columnMembership, rowMembership, columnSelector, lc, rc, lr] using hl
  have hr' : 1 = D 0 0 := by
    calc
      1 = (rowSelector rr * C * rowMembership rc) 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
        rfl
      _ = (D * (columnMembership lc * rowMembership rc)) 0 0 := hr
      _ = D 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
        change D 0 0 * (1 * 1) = D 0 0
        exact Nat.mul_one _
  exact Nat.zero_ne_one (hl'.trans hr'.symm)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro q r s C leftClass rightClass leftRep rightRep hleftRep hrightRep hcolumns hrows
    simpa [actual, realize] using
      first_response_diamond C leftClass rightClass leftRep rightRep hleftRep hrightRep hcolumns hrows,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let z : CountMat 1 1 := fun _ _ => 0
    let o : CountMat 1 1 := fun _ _ => 1
    refine ⟨(1 : Nat), z, o, ?_⟩
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [actual, realize, z, o] at hh

register_information_theorem first_response_diamond in arena
  readout via (realize signature (fun _ q C => C) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
