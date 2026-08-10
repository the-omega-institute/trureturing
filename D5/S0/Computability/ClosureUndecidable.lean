/- GID: D5/S0/Computability/ClosureUndecidable
   generality: G
   mirror-B: D5/B/S0/Computability/ClosureUndecidable
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: No computable total reading decides a nontrivial behavior-level closure predicate. -/

import Mathlib.Computability.Halting

namespace D5.S0.Computability.ClosureUndecidable

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- **Closure readings are unreachable in the kernel.** Let `Closed` be any
closure predicate on partial recursive codes that is taken at the same layer
as its objects: whether a code counts as closed depends only on the behavior
the code describes. If the predicate is nontrivial — some code is closed and
some code is not — then no total computable reading decides it. This is a
declared thin honest wrapper around Mathlib's `ComputablePred.rice₂` (Rice's
theorem), whose proof is the fixed-point diagonal: a code that consults the
hypothetical reading on itself and enacts the opposite verdict. -/
theorem closure_reading_unreachable (Closed : Set Code)
    (same_layer : ∀ c₁ c₂ : Code, eval c₁ = eval c₂ → (c₁ ∈ Closed ↔ c₂ ∈ Closed))
    {cClosed cOpen : Code} (hClosed : cClosed ∈ Closed) (hOpen : cOpen ∉ Closed) :
    ¬ComputablePred fun c => c ∈ Closed := by
  intro h
  rcases (ComputablePred.rice₂ Closed same_layer).1 h with rfl | rfl
  · exact hClosed
  · exact hOpen trivial

/-- The empty-ledger behavior class: codes whose described program certifies
nothing, i.e. whose evaluation is everywhere undefined. -/
def EmptyLedger : Set Code :=
  {c | eval c = fun _ => Part.none}

/-- The empty-ledger predicate is taken at the same layer as its objects:
codes of equal behavior are equi-silent. -/
theorem emptyLedger_same_layer :
    ∀ c₁ c₂ : Code, eval c₁ = eval c₂ → (c₁ ∈ EmptyLedger ↔ c₂ ∈ EmptyLedger) := by
  intro c₁ c₂ h
  simp only [EmptyLedger, Set.mem_setOf_eq, h]

/-- Witness instantiation: the empty-ledger reading is itself unreachable.
The everywhere-undefined behavior has a code, the total identity behavior has
a code outside the class, so the closure predicate "the ledger is empty" is
nontrivial and behavior-level — hence no total computable reading decides it. -/
theorem empty_ledger_reading_unreachable :
    ¬ComputablePred fun c => c ∈ EmptyLedger := by
  obtain ⟨cSilent, hSilent⟩ := Nat.Partrec.Code.exists_code.1 Nat.Partrec.none
  obtain ⟨cTotal, hTotal⟩ := Nat.Partrec.Code.exists_code.1 Nat.Partrec.some
  refine closure_reading_unreachable EmptyLedger emptyLedger_same_layer
    (cClosed := cSilent) (cOpen := cTotal) hSilent fun hmem => ?_
  have h0 := congrFun (hTotal.symm.trans hmem) 0
  simp at h0

end D5.S0.Computability.ClosureUndecidable
