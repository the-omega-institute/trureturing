import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
import Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound

universe u

namespace ChainBound

abbrev signature : Signature where
  Params := ℕ
  State n := CountMat n n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := CountMat n n
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    Nonempty (ExchangeChain ℕ (rho.readout () n A) B (2 * m - 1))

theorem actual_law : arena.Law actual := by
  intro n k m A B R S c
  exact compatible_exchange_chain_bound c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨chain⟩ := h certificateU
  have hz := chain_zero_power_reverse chain 1 (by simp [bad, realize])
  have hv := congrArg (fun M : CountMat 1 1 => M 0 0) hz
  norm_num [U, pow_two, Matrix.mul_apply] at hv

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), U, P2, ?_⟩
    intro h
    exact (by decide : (1 : ℕ) ≠ 2) (congrArg (fun M : CountMat 1 1 => M 0 0) h)

register_information_theorem compatible_exchange_chain_bound in arena
  readout via (realize signature (fun _ _ A => A) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration

end ChainBound

/-- A total intervention, including empty and singleton state families. -/
def other {α : Type u} (x : α) : α := by
  classical
  exact if h : ∃ y, y ≠ x then Classical.choose h else x

theorem other_ne {α : Type u} (x : α) (h : ∃ y, y ≠ x) : other x ≠ x := by
  simp only [other, dif_pos h]
  exact Classical.choose_spec h

theorem edge_loop (r : Edge I2) : r = loop r.source := by
  rcases r with ⟨i, j, a⟩
  have h := identity_edge a
  subst j
  have ha : a = identityNumber i := by
    apply Fin.ext
    have ha := a.isLt
    simp only [identityMatrix, if_pos rfl] at ha
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
  cases ha
  rfl

theorem other_loop_ne : other (loop 0) ≠ loop 0 := by
  apply other_ne
  refine ⟨loop 1, ?_⟩
  intro h
  have := congrArg (fun r : Edge I2 => r.source.val) h
  exact Nat.one_ne_zero this

theorem other_source_ne : (other (loop 0)).source ≠ (loop 0).source := by
  intro h
  apply other_loop_ne
  rw [edge_loop (other (loop 0)), h]
  rfl

theorem other_target_ne : (other (loop 0)).target ≠ (loop 0).source := by
  have h := identity_edge (other (loop 0)).number
  rw [← h]
  exact other_source_ne

abbrev OutFiber (r s : Edge I2) := {b : Edge I2 //
  ∃ h : r.target = b.source, (certificateI2.outgoingLift r b h).val = s}
abbrev InFiber (r s : Edge I2) := {a : Edge I2 //
  ∃ h : a.target = r.source, (certificateI2.incomingLift a r h).val = s}

def outSingleton (r s : Edge I2) (h : r.target = s.source) : OutFiber r s ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨s, h, lagOne_outgoing _ _ _ _ h⟩
  left_inv := by
    rintro ⟨b, hb⟩
    apply Subtype.ext
    obtain ⟨h, he⟩ := hb
    exact ((lagOne_outgoing _ _ _ _ h).symm.trans he).symm
  right_inv := fun _ => Subsingleton.elim _ _

def outEmpty (r s : Edge I2) (h : r.target ≠ s.source) : OutFiber r s ≃ Empty where
  toFun b := by
    apply False.elim
    obtain ⟨hb, he⟩ := b.property
    have he' : b.val = s := (lagOne_outgoing _ _ _ _ hb).symm.trans he
    exact (h (hb.trans (congrArg Edge.source he'))).elim
  invFun e := nomatch e
  left_inv b := by
    obtain ⟨hb, he⟩ := b.property
    have he' : b.val = s := (lagOne_outgoing _ _ _ _ hb).symm.trans he
    exact (h (hb.trans (congrArg Edge.source he'))).elim
  right_inv e := nomatch e

def inSingleton (r s : Edge I2) (h : s.target = r.source) : InFiber r s ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨s, h, lagOne_incoming _ _ _ _ h⟩
  left_inv := by
    rintro ⟨a, ha⟩
    apply Subtype.ext
    obtain ⟨h, he⟩ := ha
    exact ((lagOne_incoming _ _ _ _ h).symm.trans he).symm
  right_inv := fun _ => Subsingleton.elim _ _

def inEmpty (r s : Edge I2) (h : s.target ≠ r.source) : InFiber r s ≃ Empty where
  toFun a := by
    apply False.elim
    obtain ⟨ha, he⟩ := a.property
    have he' : a.val = s := (lagOne_incoming _ _ _ _ ha).symm.trans he
    exact (h ((congrArg Edge.target he').symm.trans ha)).elim
  invFun e := nomatch e
  left_inv a := by
    obtain ⟨ha, he⟩ := a.property
    have he' : a.val = s := (lagOne_incoming _ _ _ _ ha).symm.trans he
    exact (h ((congrArg Edge.target he').symm.trans ha)).elim
  right_inv e := nomatch e

def edgeBad : Realization edgeSignature :=
  realize edgeSignature (fun _ _ r => other r) (fun e => nomatch e)

namespace RowCount

def arena : Arena where
  signature := edgeSignature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m)
    (r s : Edge R),
    c.squareMatrix ((Fintype.equivFin (Edge R)) (rho.readout () ⟨n, k, R⟩ r))
        ((Fintype.equivFin (Edge R)) s) =
      Nat.card {b : Edge B //
        ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s}

theorem actual_law : arena.Law edgeActual := by
  intro n k m A B R S c r s
  exact square_row_lift_count c r s

theorem rejected_law : ¬ arena.Law edgeBad := by
  intro h
  have he := h certificateI2 (loop 0) (loop 0)
  change certificateI2.squareMatrix ((Fintype.equivFin (Edge I2)) (other (loop 0)))
    ((Fintype.equivFin (Edge I2)) (loop 0)) = Nat.card (OutFiber (loop 0) (loop 0)) at he
  rw [square_row_lift_count] at he
  have hzero := Nat.card_congr (outEmpty (other (loop 0)) (loop 0) other_target_ne)
  have hone := Nat.card_congr (outSingleton (loop 0) (loop 0) rfl)
  change Nat.card (OutFiber (other (loop 0)) (loop 0)) = _ at he
  rw [hzero, hone] at he
  norm_num at he

def registration : Registration arena (arena.Law edgeActual) where
  actual := edgeActual
  bridge := Iff.rfl
  variation := ⟨actual_law, edgeBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨edgeBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, 2, I2⟩, loop 0, loop 1, ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg (fun r : Edge I2 => r.source.val) h)

register_information_theorem square_row_lift_count in arena
  readout via (realize edgeSignature (fun _ _ r => r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms registration

end RowCount

namespace ColumnCount

def arena : Arena where
  signature := edgeSignature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m)
    (r s : Edge R),
    c.squareMatrix ((Fintype.equivFin (Edge R)) (rho.readout () ⟨n, k, R⟩ s))
        ((Fintype.equivFin (Edge R)) r) =
      Nat.card {a : Edge A //
        ∃ h : a.target = r.source, (c.incomingLift a r h).val = s}

theorem actual_law : arena.Law edgeActual := by
  intro n k m A B R S c r s
  exact square_column_lift_count c r s

theorem rejected_law : ¬ arena.Law edgeBad := by
  intro h
  have he := h certificateI2 (loop 0) (loop 0)
  change certificateI2.squareMatrix ((Fintype.equivFin (Edge I2)) (other (loop 0)))
    ((Fintype.equivFin (Edge I2)) (loop 0)) = Nat.card (InFiber (loop 0) (loop 0)) at he
  rw [square_column_lift_count] at he
  have hzero := Nat.card_congr (inEmpty (loop 0) (other (loop 0)) other_target_ne)
  have hone := Nat.card_congr (inSingleton (loop 0) (loop 0) rfl)
  change Nat.card (InFiber (loop 0) (other (loop 0))) = _ at he
  rw [hzero, hone] at he
  norm_num at he

def registration : Registration arena (arena.Law edgeActual) where
  actual := edgeActual
  bridge := Iff.rfl
  variation := ⟨actual_law, edgeBad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨edgeBad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, 2, I2⟩, loop 0, loop 1, ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg (fun r : Edge I2 => r.source.val) h)

register_information_theorem square_column_lift_count in arena
  readout via (realize edgeSignature (fun _ _ r => r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 9 }] })
  escape continues (open)

#print axioms registration

end ColumnCount

end Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound
