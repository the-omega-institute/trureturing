/- GID: D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.List.Basic, mathlib/module/Mathlib.Data.Finset.Lattice.Fold]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.claim; result=D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.result; claim=D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.claim
   digest: The starting sequence 1 2 refutes Theorem 23 with a 1 allowed inside S. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ChaffinSloaneGijswijtMergeRefutation

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #9218)
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-- `s` ends in `k` consecutive copies of its own length-`p` suffix. -/
def IsCurlAt (s : List ℕ) (p k : ℕ) : Prop :=
  0 < p ∧ p * k ≤ s.length ∧
    s.drop (s.length - p * k) = (List.replicate k (s.drop (s.length - p))).flatten

instance (s : List ℕ) (p k : ℕ) : Decidable (IsCurlAt s p k) := by
  unfold IsCurlAt; infer_instance

/-- `s = X Y ^ k` for some nonempty `Y`. -/
def IsCurl (s : List ℕ) (k : ℕ) : Prop := ∃ p ≤ s.length, IsCurlAt s p k

instance (s : List ℕ) (k : ℕ) : Decidable (IsCurl s k) := by
  unfold IsCurl; infer_instance

/-- The curling number of `s`: the greatest `k` with `s = X Y ^ k` for nonempty `Y`.
The empty sequence has no such `k`; the value `1` there is a convention and is never
used below. -/
def cn (s : List ℕ) : ℕ :=
  max 1 (((Finset.range (s.length + 1)).filter (fun k => 1 ≤ k ∧ IsCurl s k)).sup id)

/-- One step of the process: append the curling number. -/
def step (s : List ℕ) : List ℕ := s ++ [cn s]

/-- `iter t s` is the sequence `S_t` obtained from `s` by `t` steps. -/
def iter : ℕ → List ℕ → List ℕ
  | 0, s => s
  | (t + 1), s => step (iter t s)

/-- The `n`-th element, counted from zero, of the infinite continuation of `s`. -/
def term (s : List ℕ) (n : ℕ) : ℕ := (iter (n + 1) s).getD n 0

/-- Gijswijt's sequence is the continuation of the one-element sequence `1`. -/
abbrev G (n : ℕ) : ℕ := term [1] n

/-- Theorem 23 of Chaffin, Linderman, Sloane and Wilks with the hypothesis weakened as in
the last sentence of their Section 5: the starting sequence may contain a 1 provided it
does not end with 1.  The tail length `t` is the first step whose curling number is one,
so `iter t s` is the extension `S⁽ᵉ⁾`; putting that hypothesis on `t` rather than invoking
the curling number conjecture keeps the statement unconditional.  The conclusion
`S⁽∞⁾ = S⁽ᵉ⁾ G` is read off term by term. -/
def claim : Prop :=
  ∀ (s : List ℕ) (t : ℕ),
    1 ∈ s →
    s.getLast? ≠ some 1 →
    cn (iter t s) = 1 →
    (∀ r, r < t → cn (iter r s) ≠ 1) →
    ∀ m, term s (s.length + t + m) = G m

/-- The weakened statement is false.  The starting sequence `1 2` contains a 1 and does
not end with 1, and `cn (1 2) = 1` gives it tail length `0`, so its extension is `1 2`
itself.  Its continuation runs `1 2 1 1 2 1 2 2 2 3 …` because `1 2 1 1 2 1` is the square
of `1 2 1`, whereas `S⁽ᵉ⁾ G` runs `1 2 1 1 2 1 1 2 2 2 …`; the two differ at the seventh
term. -/
theorem result : ¬ claim := by
  intro h
  have := h [1, 2] 0 (by decide) (by decide) (by decide)
    (fun r hr => absurd hr (Nat.not_lt_zero r)) 4
  revert this
  decide

end D5.S3.Combinatorics.ChaffinSloaneGijswijtMergeRefutation
