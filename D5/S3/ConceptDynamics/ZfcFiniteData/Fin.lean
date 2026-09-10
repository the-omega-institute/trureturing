/- GID: D5/S3/ConceptDynamics/ZfcFiniteData/Fin
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteData/Fin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.GroupWithZero.Nat]
   utility: none
   digest: Vorspiel.Fin.Basic for first-order set definition elimination. -/
module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.TautoSet

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Fin/Basic.lean, original lines 1-109.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose]
public section

lemma eq_finZeroElim {α : Sort u} (x : Fin 0 → α) : x = finZeroElim := funext (by rintro ⟨_, _⟩; contradiction)

namespace Fin

variable {n : ℕ} {i : Fin n}

section last'

variable [NeZero n]

end last'

section

end

@[inline] def addCast (m) : Fin n → Fin (m + n) := castLE <| Nat.le_add_left n m

@[simp] lemma addCast_val (i : Fin n) : (i.addCast m : ℕ) = i := rfl

namespace Fin1

variable {n : Fin 1}

-- `n` is intentionally kept as a global simp lemma (every `Fin 1` element is `0`);
-- scoping it would break implicit uses elsewhere.
set_option warning.simp.varHead false in
@[simp] lemma eq_one : n = 0 := by cases n; omega;

end Fin1

end Fin

end
