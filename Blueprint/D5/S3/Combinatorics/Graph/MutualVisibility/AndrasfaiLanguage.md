# The Andrasfai forbidden language

## Abstract

The exact finite forbidden language and uniqueness of closed labelled lifts.

**Definition 1.1 (Wildcard triple repetitions).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.Triples`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.Triples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Triples contains the empty word and is closed under appending [a,b,true] for arbitrary Boolean letters a,b. It is exactly the Kleene star (Sigma Sigma 1)*, including zero repetitions.

**Definition 1.2 (An occurrence with arbitrary context).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.ContainsForbidden`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.ContainsForbidden` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite Boolean word contains a forbidden factor if it equals p ++ [true,true] ++ t ++ [true] ++ s for some arbitrary prefix p, suffix s and Triples word t. This is the entire family 11(Sigma Sigma 1)*1, not just its length-six member.

**Definition 1.3 (The partial four-state machine as a Mathlib DFA).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.machine`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.machine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

From states 0,1,2,3 the transitions on letters 0,1 are respectively (0,1), (0,2), (3,reject), (1,1). The Mathlib DFA adds state 4 as an absorbing reject state, starts in state 0, and accepts all states except 4. Rejecting runs are not closed lifts of the original four-state automaton.

**Theorem 1.4 (Finite language equivalence).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.accepts_iff_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.accepts_iff_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Boolean word w, the standard DFA accepts w exactly when ContainsForbidden(w) is false. Any readable 11 reaches state 2; each wildcard triple then returns to 2 or rejects, and the last 1 rejects. Rejection is absorbing, so an occurrence anywhere is fatal. Conversely a run from 0 satisfies a simultaneous suffix invariant: state 2 has a suffix 11 followed by a Triples word; state 3 adds one zero to such a suffix; state 1 either ends in 1 or adds two zeros to such a suffix; state 4 certifies an actual forbidden occurrence. Appending one letter preserves this invariant. Thus a rejected finite word contains the forbidden factor, establishing the converse without an assumed language equality.

**Theorem 1.5 (Uniqueness at lengths not divisible by three).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.closed_run_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.closed_run_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite word w whose length is not divisible by three, and any states q,r other than reject, if reading w returns q to q and r to r, then q=r. This fixes the labelled starting position; there is no quotient by rotations. For two different nonrejecting runs, the unordered state pairs (0,1), (1,2), (0,3) form a three-cycle. The remaining pairs (0,2), (1,3), (2,3) have strictly decreasing ranks until they enter that cycle. Exact local transition cases prove rank monotonicity and a phase increment in Z/3Z. Induction over an arbitrary word propagates these facts. A closed pair has constant rank, hence lies in the three-cycle; its phase can return only when the word length is divisible by three, a contradiction.

**Definition 1.6 (Periodically admissible finite words).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.PeriodicAvoidance`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.PeriodicAvoidance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural k, k concatenated copies of w contain no forbidden factor. The private recursive copies function starts with the empty word and appends one complete w at each successor. All boundaries between copies are included.

**Theorem 1.7 (Existence and uniqueness of the based closed lift).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.exists_unique_closed_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.exists_unique_closed_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word w whose length is not divisible by three, PeriodicAvoidance(w) holds if and only if there is exactly one state q distinct from reject for which reading w from q returns q. If two consecutive copies contain 11, that doubled word synchronizes all nonrejecting runs. Its evaluations after two, three and four periods are nonrejecting by periodic avoidance. The two-period value is fixed by the doubled word; applying one more period and synchronization shows it is already fixed by one period. If the doubled word has no 11, the suffix invariant confines the run from zero to states zero and one. If the period ends at zero, zero is a closed state. If it ends at one, its last letter is one and the doubled word ends at one too, giving a closed state one. The uniqueness theorem then excludes any second nonrejecting starting state. Conversely a nonrejecting fixed state remains fixed after every number of complete periods, by induction using concatenation of DFA runs. Any forbidden occurrence in those periods would reject from every starting state, contradicting that fixed state. A run ending outside reject has no rejecting intermediate state because rejection is absorbing.

The exact periodic-word-to-subset bridge and the matrix trace counting correspondence remain separate obligations. This theorem establishes both existence and uniqueness for finite words satisfying PeriodicAvoidance; it does not assume or prove that the actual graph subset count is a trace.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.ContainsForbidden`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.PeriodicAvoidance`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.Triples`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.accepts_iff_avoids`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.closed_run_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.exists_unique_closed_run`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiLanguage.machine`
