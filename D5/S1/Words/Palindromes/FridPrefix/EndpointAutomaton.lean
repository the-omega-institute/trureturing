/- GID: D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/EndpointAutomaton
   mirror-E: none(waiver:finite-endpoint-rank-checker)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/RankProductA.a_endpoint_score_bound; instance=D5/S1/Words/Palindromes/FridPrefix/RankA.rankA
   digest: The 17-state paired-digit recognizer supplies exact finite endpoint transitions. -/

/-
proof_shape: definitions and certificate data only.
escape_witness: consumed by the all-word product-potential induction.
admission_basis: escape-witness (content is supplied by RankProductA).
Direct frozen dependencies: none; NFA is a pinned Mathlib owner.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Computability.NFA

namespace D5.S1.Words.FridPrefix

/-- Paired-digit transitions; every triple is (first bit, second bit, destination). -/
def endpointRows : List (List (ℕ × ℕ × ℕ)) := [
  [(0,0,0), (0,0,1), (0,1,2), (0,1,3), (1,0,4), (1,1,5)],
  [(1,1,6)],
  [(0,0,7), (1,0,8)],
  [(0,0,1), (1,0,9)],
  [(0,1,10)],
  [(0,0,0), (0,0,1)],
  [],
  [(0,0,11), (0,1,12), (1,0,13)],
  [(0,0,14), (0,0,11), (0,1,12)],
  [(0,0,1), (0,1,3)],
  [(0,0,15)],
  [(0,0,1), (0,1,3), (1,0,9), (1,1,16)],
  [(0,0,7)],
  [(0,0,7)],
  [(0,0,7), (1,0,8)],
  [(0,1,10)],
  [(0,0,7)]]

/-- The paired canonical-endpoint NFA, with accepting states 3, 9 and 11. -/
def endpoint : NFA (Fin 2 × Fin 2) (Fin 17) where
  start := {q | q.val=0}
  accept := {q | q.val ∈ [3,9,11]}
  step := fun q d => {t | (d.1.val,d.2.val,t.val) ∈ endpointRows.getD q.val []}

/-- Exact numeric paired chunks obtained by reading a fixed number of endpoint bits. -/
def movesFrom : ℕ → ℕ → List (ℕ × ℕ × ℕ)
  | q, 0 => [(0,0,q)]
  | q, width+1 => (endpointRows.getD q []).flatMap (fun (x,y,t) =>
      (movesFrom t width).map (fun (a,b,s) => (x*2^width+a,y*2^width+b,s)))

/-- The same recognizer with paired chunks of a fixed width as its alphabet. -/
def chunkEndpoint (width : ℕ) : NFA (ℕ × ℕ) (Fin 17) where
  start := endpoint.start
  accept := endpoint.accept
  step := fun q d => {t | (d.1,d.2,t.val) ∈ movesFrom q.val width}

end D5.S1.Words.FridPrefix
