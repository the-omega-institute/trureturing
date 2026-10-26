# MatchingTemplate for Latin tableaux

## Abstract

Literal source Latin tableaux: MatchingTemplate

Daugherty et al., arXiv:2610.29291v1, Conjecture 6.3 asks for the full count of Latin tableaux of shape (k,k-1,...,5,4,3,3) for every integer k at least five. Cells and integer symbols retain their fixed identities, and the prescribed symbol multiplicities are those of the conjugate partition.

**Definition 1.1 (Literal matchings).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.matchings`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.matchings` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Ordered injective choices from the actual availability sets; the carrier retains each fixed column and symbol.

**Theorem 1.2 (Exact matching membership).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.mem_matchings`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.mem_matchings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Membership is equivalent to positional set membership and no repeated entry.

**Definition 1.3 (Insertion of a new row and symbol).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.border`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.border` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Remove each chosen symbol from its actual column, insert the fresh symbol in every column, then append the new universal column.

**Definition 1.4 (Ordered tail templates).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.Tail`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.Tail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The three-column base is [{x},{y,z},{x,y,z}], with distinct actual symbols. A step prefixes a fresh forced symbol and inserts it in every remaining column.

**Theorem 1.5 (Tail symbols lie in their actual carrier).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_subsets`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_subsets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Induction on the template proves each availability set is contained in B.

**Theorem 1.6 (Two tail choices).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_matchings`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_matchings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The base has two choices. Every inductive forced prefix preserves that exact number.

**Theorem 1.7 (Tail preservation).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_transition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

For every actual matching and every fresh universal symbol, deleting the matching and bordering yields another tail template on the enlarged actual symbol set.

**Definition 1.8 (The three distinguished columns).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.headGraph`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.headGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

One column contains {a,c}, the other two contain {b,c}; the distinguished column remains a fixed position.

**Definition 1.9 (The two head choices).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.headRows`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.headRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

The two literal permutations compatible with each distinguished position. No symmetry quotient is taken.

**Definition 1.10 (The complete availability invariant).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.Full`

*Formalization.* `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.Full` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Three distinct high symbols a,b,c lie outside B. The fixed head is followed by a tail whose columns are enlarged by all three high symbols.

**Theorem 1.11 (Four literal next rows).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_matchings`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_matchings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

An exact head-tail splitting gives a product of two head choices and two tail choices. Append is injective on the fixed three-entry head.

**Theorem 1.12 (The full all-parameter transition).**

Lean statement: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_transition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock (2026). *Counting and Constructing Latin tableaux*. URL: <https://arxiv.org/abs/2610.29291v1>.

*Commentary.*

Every one of the four rows preserves the complete invariant. The high triple (a,b,c) becomes (b,c,u), and the low carrier becomes insert a B. All six distinguished-position/head-choice cases are proved.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.Full`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.Tail`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.border`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_matchings`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_transition`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.headGraph`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.headRows`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.matchings`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.mem_matchings`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_matchings`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_subsets`
- Truth anchor: `D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.tail_transition`
