# The unpruned frontier model

## Abstract

The full open-grid frontier model has 4672 states, one Boolean witness-existence test per checked column, and two absent-column terminal checks.

**Definition 1.1 (All states).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

State is Fin 4672. The first 64 states are (8,8,a,b), the next 512 are (8,a,b,c), and the final 4096 are (a,b,c,d), with real masks in lexicographic order. Real masks are 0 through 7; the absent symbol is 8.

**Definition 1.2 (Append one real mask).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append drops the first symbol, appends the supplied real mask, and encodes the resulting four columns in the next appropriate state block.

**Theorem 1.3 (Distinct appended masks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full state s, append s is injective on Fin 8. Thus distinct appended masks do not create edge multiplicity.

**Theorem 1.4 (Literal column shift).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state s, real mask m and i in Fin 4, the i-th column of append s m is the (i+1)-th column of s when i<3, and is m when i=3. This includes all three state blocks.

**Definition 1.5 (Existing vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex exists in the five-column window exactly when its column symbol is less than 8. The real empty symbol 0 still has all three vertices.

**Definition 1.6 (Selected vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex is selected exactly when it exists and the corresponding row bit in its column symbol is set. An absent symbol never selects a vertex.

**Definition 1.7 (Boolean witness existence).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the three middle-column vertices has a selected closed neighbour. Every selected middle vertex has an existing closed-neighbour witness whose selected closed neighbourhood contains only that vertex. Candidate witnesses and selected vertices exclude absent columns. Witnesses are existential propositions and are not path choices.

**Definition 1.8 (The executable finite predicate).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

accepts is the Boolean decision of Local over the finite five-column vertex domain.

**Definition 1.9 (Append a fifth symbol).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four state columns followed by the supplied symbol form the tested window.

**Definition 1.10 (Admitted directed edges).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Edge`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge from s to t means that some real mask appends to t and the resulting five-column window is accepted.

**Definition 1.11 (Unit edge weights).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.transition`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer matrix entry is 1 for an admitted edge and 0 otherwise.

**Definition 1.12 (All two-column starts).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.initial`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial weight is 1 at all 64 states in the first block and 0 elsewhere. This includes every labelled pair of real masks, without symmetry reduction.

**Definition 1.13 (Both open-end checks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A terminal state must accept its four columns followed by 8, and must also accept its last three columns followed by 8,8. These check the final two real columns.

The all-length bijection between actual accepted mask words and successful full-state paths remains unproved here. The identification of the Boolean Local predicate with the actual-grid ColumnTest, the separate width-one count, the full-state quotient certificate and the original generating-series endpoint also remain open formal interfaces. No actual-count or quotient equality is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.initial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.transition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding](BarkerMinimalGridEncoding.md)
