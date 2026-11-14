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

**Theorem 1.3 (Literal column shift).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state s, real mask m and i in Fin 4, the i-th column of append s m is the (i+1)-th column of s when i<3, and is m when i=3. This includes all three state blocks.

**Definition 1.4 (Exact binary masks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positional-base equivalence finFunctionFinEquiv, composed with finTwoEquiv at every row, identifies all Fin 8 masks with Fin 3 → Bool.

**Theorem 1.5 (Little-endian row bits).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m in Fin 8 and row r in Fin 3, maskEquiv m r is exactly Nat.testBit m.val r.val. All 24 entries are kernel checked.

**Definition 1.6 (Present and absent symbols).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.symbol`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An absent Option mask is encoded by 8. A present mask is encoded by its inverse under maskEquiv and therefore has value less than 8, including the present empty mask 0.

**Definition 1.7 (Actual signed column coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.paddedWindow`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.paddedWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every actual word w of width n and real centre c, the five symbols encode the padded columns c+i−2 for i in Fin 5.

**Definition 1.8 (Existing vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex exists in the five-column window exactly when its column symbol is less than 8. The real empty symbol 0 still has all three vertices.

**Definition 1.9 (Selected vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex is selected exactly when it exists and the corresponding row bit in its column symbol is set. An absent symbol never selects a vertex.

**Definition 1.10 (Boolean witness existence).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the three middle-column vertices has a selected closed neighbour. Every selected middle vertex has an existing closed-neighbour witness whose selected closed neighbourhood contains only that vertex. Candidate witnesses and selected vertices exclude absent columns. Witnesses are existential propositions and are not path choices.

**Theorem 1.11 (Exact finite-window fidelity).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.local_paddedWindow_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.local_paddedWindow_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n, word w and actual centre c, Local (paddedWindow w c) is equivalent to ColumnTest (decode w) c. Signed-coordinate transport preserves every existing selected vertex, Manhattan distance, witness existence and uniqueness, including both open ends.

**Theorem 1.12 (Every real centre).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff_local`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n and word w, ValidWord w is equivalent to Local (paddedWindow w c) at every c in Fin n. This follows through the actual-grid column criterion.

**Definition 1.13 (Executable accepted words).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.acceptedWords`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.acceptedWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite family filters every numeric Fin n → Fin 8 word by the exact Local test at all padded real centres.

**Theorem 1.14 (Actual subset cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_eq_acceptedWords`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_eq_acceptedWords` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width n, actualCount n equals the cardinality of acceptedWords n. The proof composes the actual subset-word equivalence with the pinned numeric mask equivalence and the all-width local fidelity theorem.

**Theorem 1.15 (The original first coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual width-one minimal dominating subset count is exactly 2. The proof transports to all eight numeric masks and checks the actual local predicate; the two subsets are the middle singleton and the pair of ends.

**Definition 1.16 (The executable finite predicate).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

accepts is the Boolean decision of Local over the finite five-column vertex domain.

**Definition 1.17 (Append a fifth symbol).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four state columns followed by the supplied symbol form the tested window.

**Definition 1.18 (Both open-end checks).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A terminal state must accept its four columns followed by 8, and must also accept its last three columns followed by 8,8. These check the final two real columns.

**Definition 1.19 (Backward transfer).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullStep`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integer state vector v and full state s, fullStep v s sums v(append s m) over precisely the accepted real masks m. Each mask contributes once.

**Definition 1.20 (All-length backward orbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullOrbit`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullOrbit 0 is the full terminal vector and fullOrbit(k+1) is fullStep(fullOrbit k). This is defined independently of actualCount.

The full transfer sums contributions from accepted mask words. The two terminal tests enforce the same open boundaries as the actual graph. The all-length counting correspondence and the total quotient then connect these local predicates to the actual subset series.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.Local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.acceptedWords`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.accepts`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_eq_acceptedWords`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.actualCount_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.columns_append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullOrbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.fullStep`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.local_paddedWindow_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.maskEquiv_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.paddedWindow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.present`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.symbol`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.validWord_iff_local`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer.window`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding](BarkerMinimalGridEncoding.md)
