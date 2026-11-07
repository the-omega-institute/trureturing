import D5.S3.Arith.DirichletRoots.OeisA318314
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-family registration for the rational recurrence and its uniqueness. -/

namespace Reg.D5.S3.Arith.DirichletRoots.OeisA318314

open _root_.D5.S3.Arith.DirichletRoots.OeisA318314
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => f n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := SourceSpec (R.readout () ()) ∧
    ∀ u : ℕ → ℚ, SourceSpec u → ∀ n, 0 < n → u n = R.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1.1
  change (0 : ℚ) = 1 at hh
  norm_num at hh

def family : Registration arena (type_of% (@source_solution_unique)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_solution_unique, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change f 0 ≠ f 1
    have hz : f 0 = 0 := by rw [f]; norm_num
    rw [hz, source_solution_unique.1.1]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@source_solution_unique) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.DirichletRoots.OeisA318314.source_solution_unique.audit
  realizationName := `Reg.D5.S3.Arith.DirichletRoots.OeisA318314.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => f n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def squareActual : Realization signature :=
  realize signature (fun _ _ n => (root * root) n) (fun e => nomatch e)

abbrev squareArena : Arena where
  signature := signature
  Law R := ∀ n, R.readout () () n = (oddUnitaryCount n : ℚ)

private theorem squareRejected : ¬ squareArena.Law rejected := by
  intro h
  have hh := h 1
  change (0 : ℚ) = (oddUnitaryCount 1 : ℚ) at hh
  exact (by decide : (0 : ℚ) ≠ (oddUnitaryCount 1 : ℚ)) hh

def squareFamily : Registration squareArena (type_of% (@root_square)) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨root_square, rejected, squareRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, squareRejected⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (root * root) 0 ≠ (root * root) 1
    rw [root_square, root_square]
    norm_num [oddUnitaryCount, Nat.odd_iff]
def squareAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_square) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.DirichletRoots.OeisA318314.root_square.audit
  realizationName := `Reg.D5.S3.Arith.DirichletRoots.OeisA318314.squareFamily
  realizationSource := none
  generated := false
  arena := .source ⟨squareArena⟩
  objectArena := .source ⟨squareArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareArena ⟨squareFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some squareActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def sourceActual : Realization signature :=
  realize signature (fun _ _ n => root n) (fun e => nomatch e)

abbrev sourceArena : Arena where
  signature := signature
  Law R := SourceSpec (R.readout () ()) ∧ ∀ n, 0 < n → R.readout () () n = f n

private theorem sourceRejected : ¬ sourceArena.Law rejected := by
  intro h
  have hh := h.1.1
  change (0 : ℚ) = 1 at hh
  norm_num at hh

def sourceFamily : Registration sourceArena (type_of% (@root_source)) where
  actual := sourceActual
  bridge := Iff.rfl
  variation := ⟨root_source, rejected, sourceRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, sourceRejected⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change root 0 ≠ root 1
    rw [ArithmeticFunction.map_zero, root_structure.1.1]
    norm_num
def sourceAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@root_source) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.DirichletRoots.OeisA318314.root_source.audit
  realizationName := `Reg.D5.S3.Arith.DirichletRoots.OeisA318314.sourceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨sourceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some sourceActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def wholeActual : Realization signature :=
  realize signature (fun _ _ n => f n) (fun e => nomatch e)

abbrev wholeArena : Arena where
  signature := signature
  Law R := SourceSpec (R.readout () ()) ∧
    (∀ u : ℕ → ℚ, SourceSpec u → ∀ n, 0 < n → u n = R.readout () () n) ∧
    (∀ n, 0 < n → (R.readout () () n).den = twoPart n * auxiliary n) ∧
    (R.readout () () 1).den = 1 ∧
    (∀ m n, 0 < m → 0 < n → Nat.Coprime m n →
      (R.readout () () (m * n)).den = (R.readout () () m).den * (R.readout () () n).den) ∧
    (∀ e, (R.readout () () (2 ^ e)).den = 2 ^ halvingSum e) ∧
    (∀ p e, Nat.Prime p → p ≠ 2 →
      (R.readout () () (p ^ e)).den = 2 ^ (e - binaryWeight e)) ∧
    (∀ p e, Nat.Prime p →
      (R.readout () () (p ^ e)).den = 2 ^ ((2 - p % 2) * e - binaryWeight e) ∧
      (((2 - p % 2) * e - binaryWeight e : ℕ) : ℤ) =
        (2 - (p : ℤ) % 2) * e - binaryWeight e)

private theorem wholeRejected : ¬ wholeArena.Law rejected := by
  intro h
  have hh := h.1.1
  change (0 : ℚ) = 1 at hh
  norm_num at hh

def wholeFamily : Registration wholeArena (type_of% (@whole_block)) where
  actual := wholeActual
  bridge := Iff.rfl
  variation := ⟨whole_block, rejected, wholeRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, wholeRejected⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change f 0 ≠ f 1
    have hz : f 0 = 0 := by rw [f]; norm_num
    rw [hz, source_solution_unique.1.1]
    norm_num
def wholeAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@whole_block) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.DirichletRoots.OeisA318314.whole_block.audit
  realizationName := `Reg.D5.S3.Arith.DirichletRoots.OeisA318314.wholeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨wholeArena⟩
  objectArena := .source ⟨wholeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wholeArena ⟨wholeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some wholeActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.DirichletRoots.OeisA318314
