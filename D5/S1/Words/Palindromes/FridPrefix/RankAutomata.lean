/- GID: D5/S1/Words/Palindromes/FridPrefix/RankAutomata
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/RankAutomata
   mirror-E: none(waiver:finite-endpoint-rank-checker)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/RankProductA.a_endpoint_score_bound; instance=D5/S1/Words/Palindromes/FridPrefix/RankA.rankA
   digest: A weighted chunk evaluator adds integer scores along deterministic finite-state runs. -/

/-
proof_shape: definitions and certificate data only.
escape_witness: consumed by the all-word product-potential induction.
admission_basis: escape-witness (content is supplied by RankProductA).
Direct frozen dependencies: none; NFA is a pinned Mathlib owner.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.Int.Basic

namespace D5.S1.Words.FridPrefix

/-- A deterministic chunk automaton with integral edge weights and zero terminal weight. -/
structure ChunkRank where
  width : ℕ
  initial : ℕ
  transitions : Array (Array ℕ)
  weights : Array (Array ℤ)

/-- Accumulate the edge weights while reading numeric chunks. -/
def chunkScore (r : ChunkRank) (xs : List ℕ) : ℤ :=
  (xs.foldl (fun s x => ((r.transitions.getD s.1 #[]).getD x 0,
      s.2+(r.weights.getD s.1 #[]).getD x 0)) (r.initial,(0:ℤ))).2

end D5.S1.Words.FridPrefix
