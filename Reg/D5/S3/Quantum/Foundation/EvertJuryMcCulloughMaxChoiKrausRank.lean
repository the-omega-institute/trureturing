import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
import Reg.Support.DependentFamily

/-! The rank readout in each bound and each attainment has its own product binder. -/

namespace Reg.D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank

open _root_.D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

inductive RankClause
  | leftBound | leftAttainment | commonBound | commonAttainment
  deriving DecidableEq

instance : Fintype RankClause where
  elems := ⟨[RankClause.leftBound, RankClause.leftAttainment,
    RankClause.commonBound, RankClause.commonAttainment], by decide⟩
  complete clause := by cases clause <;> decide

instance : Nonempty RankClause := ⟨.leftBound⟩

abbrev signature : Signature where
  Params := ℕ
  State n := MatrixProduct n n
  Role := RankClause
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    ((∀ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi →
        (∃ L : CMatrix n, IsLeftUnit Phi L) →
        R.readout .leftBound n Phi ≤ ((n ^ 3 : ℕ) : ℕ∞)) ∧
      (∃ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi ∧
        (∃ L : CMatrix n, IsLeftUnit Phi L) ∧
        R.readout .leftAttainment n Phi = ((n ^ 3 : ℕ) : ℕ∞))) ∧
    ((∀ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi →
        (∃ T : CMatrix n, IsUnit Phi T) →
        R.readout .commonBound n Phi ≤ ((n ^ 3 : ℕ) : ℕ∞)) ∧
      (∃ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi ∧
        (∃ T : CMatrix n, IsUnit Phi T) ∧
        R.readout .commonAttainment n Phi = ((n ^ 3 : ℕ) : ℕ∞)))

private def intervened (role : RankClause) : Realization signature :=
  realize signature
    (fun j _ Phi => if j = role then
      (if j = .leftBound ∨ j = .commonBound then ⊤ else 0) else choiKrausRank Phi)
    (fun e => nomatch e)

private theorem intervened_not_law (role : RankClause) : ¬ arena.Law (intervened role) := by
  intro holds
  have reading := holds 1 (by decide)
  have original := result 1 (by decide)
  cases role
  · obtain ⟨Phi, hPhi, leftUnit, _⟩ := original.1.2
    have impossible := reading.1.1 Phi hPhi leftUnit
    change (⊤ : ℕ∞) ≤ ((1 ^ 3 : ℕ) : ℕ∞) at impossible
    have htop : ((1 ^ 3 : ℕ) : ℕ∞) = ⊤ := top_le_iff.mp impossible
    exact ENat.natCast_ne_top _ htop
  · obtain ⟨_, _, _, impossible⟩ := reading.1.2
    change (0 : ℕ∞) = ((1 ^ 3 : ℕ) : ℕ∞) at impossible
    simp at impossible
  · obtain ⟨Phi, hPhi, commonUnit, _⟩ := original.2.2
    have impossible := reading.2.1 Phi hPhi commonUnit
    change (⊤ : ℕ∞) ≤ ((1 ^ 3 : ℕ) : ℕ∞) at impossible
    have htop : ((1 ^ 3 : ℕ) : ℕ∞) = ⊤ := top_le_iff.mp impossible
    exact ENat.natCast_ne_top _ htop
  · obtain ⟨_, _, _, impossible⟩ := reading.2.2
    change (0 : ℕ∞) = ((1 ^ 3 : ℕ) : ℕ∞) at impossible
    simp at impossible

private theorem zero_rank (n : ℕ) : choiKrausRank (0 : MatrixProduct n n) = 0 := by
  apply le_antisymm _ bot_le
  apply sInf_le
  refine ⟨0, rfl, ⟨(fun k => Fin.elim0 k), ?_⟩⟩
  intro A B
  simp

def sourceRegistration : Registration arena claim where
  actual := realize signature (fun _ _ Phi => choiKrausRank Phi) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨result, intervened .leftBound, intervened_not_law .leftBound⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervened i, ?_, rfl, intervened_not_law i⟩
      intro j different
      funext n Phi
      change choiKrausRank Phi =
        (if j = i then (if j = .leftBound ∨ j = .commonBound then ⊤ else 0) else choiKrausRank Phi)
      rw [ite_eq_right different]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨Phi, _, _, hrank⟩ := (result 1 (by decide)).2.2
    refine ⟨(1 : ℕ), (0 : MatrixProduct 1 1), Phi, ?_⟩
    change choiKrausRank (0 : MatrixProduct 1 1) ≠ choiKrausRank Phi
    rw [zero_rank, hrank]
    simp

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Phi => choiKrausRank Phi) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
    definition := some {
      owner := `D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
      name := `D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "body", "body", "body", "fn", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "fn", "arg", "arg", "arg", "body", "arg", "arg", "fn", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "arg", "fn", "arg", "body", "body", "body", "fn", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "arg", "arg", "arg", "body", "arg", "arg", "fn", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false } ] }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false } ] }

end

end Reg.D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
