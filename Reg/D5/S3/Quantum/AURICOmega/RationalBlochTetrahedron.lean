import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron

/-! The third off-diagonal Gram entry is a necessary observation in the coordinate obstruction. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron
  (no_rational_bloch_tetrahedral_triangle)
open LeanInformationAudit
open Omega.Geometry.BargmannGram (Quad4)

set_option autoImplicit false

noncomputable section

private abbrev Params := Σ _ : Quad4, Σ _ : Quad4, Omega.Nat

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params (fun _ => Quad4) (fun _ => Omega.Int)

private abbrev three : Omega.Nat := Omega.Nat.one.succ.succ

private def actual : Realization signature :=
  realize signature (fun _ p c => (Omega.Int.ofNat three).mul (c.dot p.1))
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ p _ => (Omega.Int.ofNat (p.2.2.mul p.2.2)).neg)
    (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (a b : Quad4) (d : Omega.Nat) (c : Quad4) (_ : Omega.Not (Omega.Eq d Omega.Nat.zero))
      (_ : Omega.Eq a.w Omega.Int.zero) (_ : Omega.Eq b.w Omega.Int.zero)
      (_ : Omega.Eq c.w Omega.Int.zero)
      (_ : Omega.Eq (a.dot a) (Omega.Int.ofNat (d.mul d)))
      (_ : Omega.Eq (b.dot b) (Omega.Int.ofNat (d.mul d)))
      (_ : Omega.Eq (c.dot c) (Omega.Int.ofNat (d.mul d)))
      (_ : Omega.Eq ((Omega.Int.ofNat three).mul (a.dot b)) (Omega.Int.ofNat (d.mul d)).neg)
      (_ : Omega.Eq ((Omega.Int.ofNat three).mul (b.dot c)) (Omega.Int.ofNat (d.mul d)).neg)
      (_ : Omega.Eq (R.readout () ⟨a, ⟨b, d⟩⟩ c) (Omega.Int.ofNat (d.mul d)).neg), Omega.False

private def axis : Quad4 := ⟨Omega.Int.zero, Omega.Int.ofNat three, Omega.Int.zero, Omega.Int.zero⟩

private def neighbor : Quad4 :=
  ⟨Omega.Int.zero, Omega.Int.one.neg, Omega.Int.two, Omega.Int.two⟩

private theorem nativeEq {α : Type} {a b : α} (h : Omega.Eq a b) : a = b :=
  Omega.Eq.rec rfl h

private theorem omegaEq {α : Type} {a b : α} (h : a = b) : Omega.Eq a b :=
  h ▸ Omega.rfl

private theorem native_add_ofNat (a b : Omega.Nat) :
    (Omega.Int.ofNat a).add (Omega.Int.ofNat b) = Omega.Int.ofNat (a.add b) := rfl

private theorem native_mul_ofNat (a b : Omega.Nat) :
    (Omega.Int.ofNat a).mul (Omega.Int.ofNat b) = Omega.Int.ofNat (a.mul b) := rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply Omega.False.elim
  apply h axis neighbor three axis (Omega.Nat.succ_ne_zero _)
  all_goals
    apply omegaEq
    simp only [axis, neighbor, rejected, realize, Quad4.dot, Omega.Int.zero, Omega.Int.one, Omega.Int.two,
      nativeEq (Omega.Int.neg_mul_neg _ _), nativeEq (Omega.Int.mul_neg _ _),
      nativeEq (Omega.Int.neg_mul _ _), nativeEq (Omega.Int.mul_zero _),
      nativeEq (Omega.Int.zero_mul _), nativeEq (Omega.Int.add_zero _),
      nativeEq (Omega.Int.zero_add _), native_mul_ofNat, native_add_ofNat,
      three, Omega.Nat.one, nativeEq (Omega.Nat.mul_zero _), nativeEq (Omega.Nat.mul_succ _ _),
      nativeEq (Omega.Nat.add_zero _), nativeEq (Omega.Nat.add_succ _ _)] <;> rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨Quad4.one, ⟨neighbor, three⟩⟩, Quad4.one, Quad4.zero, ?_⟩
  intro heq
  change (Omega.Int.ofNat three).mul (Quad4.one.dot Quad4.one) =
    (Omega.Int.ofNat three).mul (Quad4.zero.dot Quad4.one) at heq
  simp only [Quad4.one, Quad4.zero, Quad4.dot, Omega.Int.zero, Omega.Int.one,
    nativeEq (Omega.Int.mul_one _), nativeEq (Omega.Int.mul_zero _),
    nativeEq (Omega.Int.zero_mul _), nativeEq (Omega.Int.add_zero _)] at heq
  exact Omega.False.elim (Omega.Nat.succ_ne_zero _ (Omega.Int.ofNat_inj.mp (omegaEq heq)))

def family : Registration arena (type_of% @no_rational_bloch_tetrahedral_triangle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_rational_bloch_tetrahedral_triangle, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@no_rational_bloch_tetrahedral_triangle) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => (Omega.Int.ofNat three).mul (c.dot p.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron
