/- GID: D5/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/DiagonalEscape/DiagonalCompletionEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary finite prefixes admit a compatible diagonal escape sequence. -/

import D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion

/- Library-search audit trail (2026-08-21):
   * The repository exact hits `InverseStageSystem`, `CompatibleStageFamily`,
     and `completionMap` are imported and used directly.
   * Searches under D5 and pinned Mathlib found no packaged binary diagonal
     completion theorem; only basic Fin and Bool extensionality was needed.
   * Loogle and LeanSearch supplied no stronger theorem (the LeanSearch
     endpoint was unavailable), so the finite-prefix construction is proved
     directly from the source restriction channels. -/

namespace D5.S3.ObserverMemory.DiagonalEscape.DiagonalCompletionEscape

open D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The binary stage of length n is the space of Boolean words on `Fin n`. -/
def binaryStageSystem : InverseStageSystem Nat where
  Stage := fun n => Fin n -> Bool
  restrict := fun {i j} h word k =>
    word ⟨k.1, Nat.lt_of_lt_of_le k.2 h⟩
  restrict_refl := by
    intro i word
    funext k
    rfl
  restrict_trans := by
    intro i j k hij hjk word
    funext x
    rfl

/-- The canonical finite prefix probe of an infinite Boolean sequence. -/
def prefixProbe (n : Nat) (sequence : Nat -> Bool) : Fin n -> Bool :=
  fun k => sequence k.1

private theorem prefix_compatible {i j : Nat} (h : i <= j)
    (sequence : Nat -> Bool) :
    binaryStageSystem.restrict h (prefixProbe j sequence) = prefixProbe i sequence := by
  funext k
  rfl

/-- A diagonal sequence and its compatible binary finite-prefix section escape
every sequence in a proposed enumeration. -/
theorem diagonal_completion_escape (enumeration : Nat -> Nat -> Bool) :
    ∃ diagonal : Nat -> Bool,
      ∃ family : CompatibleStageFamily binaryStageSystem,
        (∀ n, diagonal n = if enumeration n n then false else true) ∧
        (∀ n, family.stage n = prefixProbe n diagonal) ∧
        (∀ {i j : Nat} (h : i <= j),
          binaryStageSystem.restrict h (prefixProbe j diagonal) = prefixProbe i diagonal) ∧
        (∀ n, diagonal ≠ enumeration n) := by
  let diagonal : Nat -> Bool := fun n =>
    if enumeration n n then false else true
  have hprefix :
      ∀ {i j : Nat} (h : i <= j),
        binaryStageSystem.restrict h (prefixProbe j diagonal) = prefixProbe i diagonal := by
    intro i j h
    exact prefix_compatible h diagonal
  let diagonalFamily : CompatibleStageFamily binaryStageSystem :=
    completionMap binaryStageSystem prefixProbe prefix_compatible diagonal
  refine ⟨diagonal, diagonalFamily, ?_, ?_, hprefix, ?_⟩
  · intro n
    rfl
  · intro n
    rfl
  · intro n hsame
    have hcoordinate := congrFun hsame n
    simp [diagonal] at hcoordinate

example :
    ∃ diagonal : Nat -> Bool,
      ∀ n, diagonal n = if (fun _ _ => false) n n then false else true := by
  refine ⟨fun _ => true, ?_⟩
  intro n
  rfl

#print axioms diagonal_completion_escape

end

end D5.S3.ObserverMemory.DiagonalEscape.DiagonalCompletionEscape
