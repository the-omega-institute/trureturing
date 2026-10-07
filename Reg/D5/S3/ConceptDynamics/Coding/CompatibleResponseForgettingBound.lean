import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.compatible_exchange_chain_bound) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ A => A) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgettingBound") "compatible_exchange_chain_bound") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ A => A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.compatible_exchange_chain_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.anchorEnumeration }


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

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_row_lift_count) (type_of% (realize.{0, 0, 0, 0, 0} edgeSignature (fun _ _ r => r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "square_row_lift_count") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} edgeSignature (fun _ _ r => r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, definition := none, coordinates := #[0, 1, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_row_lift_count, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.anchorEnumeration }


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

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_column_lift_count) (type_of% (realize.{0, 0, 0, 0, 0} edgeSignature (fun _ _ r => r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "square_column_lift_count") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} edgeSignature (fun _ _ r => r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, definition := none, coordinates := #[0, 1, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_column_lift_count, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.anchorEnumeration }


#print axioms registration

end ColumnCount

end Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual)
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_column_lift_count\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_column_lift_count, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.arena
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual)
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.observation0 : {n k m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n} →
          (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) →
            (r s : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeSignature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat
                  (fun (n : Nat) =>
                    @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                  n
                  (@Sigma.mk.{0, 0} Nat
                    (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R)) :=
  fun {n k m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n}
    (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m)
    (r s : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
      n (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R))
    s

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_column_lift_count\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_column_lift_count, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_column_lift_count\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_column_lift_count, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ColumnCount\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ColumnCount.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual)
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_row_lift_count\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_row_lift_count, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.arena
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual)
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.observation0 : {n k m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n} →
          (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) →
            (r s : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeSignature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat
                  (fun (n : Nat) =>
                    @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                  n
                  (@Sigma.mk.{0, 0} Nat
                    (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R)) :=
  fun {n k m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n}
    (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m)
    (r s : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
      n (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R))
    r

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_row_lift_count\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_row_lift_count, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_row_lift_count\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_row_lift_count, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"RowCount\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.RowCount.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.actual)
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"compatible_exchange_chain_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.compatible_exchange_chain_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.arena
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.actual)
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.observation0 : {n k m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n} →
          (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.signature PUnit.unit.{1} n :=
  fun {n k m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n}
    (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.actual PUnit.unit.{1} n A

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"compatible_exchange_chain_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.compatible_exchange_chain_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"compatible_exchange_chain_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.compatible_exchange_chain_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgettingBound\",\"ChainBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound.ChainBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
