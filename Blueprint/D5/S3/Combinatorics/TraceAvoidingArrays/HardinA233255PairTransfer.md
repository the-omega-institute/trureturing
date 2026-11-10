# Positive-height arrays with horizontal and antidiagonal bonds

## Abstract

Literal seven-column arrays and the exact transfer on labelled six-cell boundaries.

Source problem: R. H. Hardin, OEIS A233255, https://oeis.org/A233255 (OEIS licence: https://oeis.org/LICENSE). The all-height labelled count correspondence below is one part of the literal count to canonical-shape transfer argument.

An array is an individual function on a positive number of rows and seven columns with values in six colours. Its upper-left colour is zero. Only horizontal and upper-right/lower-left antidiagonal bonds exclude equal colours and colours whose sum is five. In row-major order each colour two, three, or four requires an earlier one, and each three requires an earlier two. Missing colours are allowed. No zero-height sequence value is defined.

**Definition 1.1 (Colour rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seven ordered individual colours.

**Definition 1.2 (Pair-label rows).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seven ordered complementary-pair labels.

**Definition 1.3 (Labelled boundaries).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Boundary`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six labels in columns one through six.

**Definition 1.4 (Horizontal exclusions).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every adjacent horizontal bond is tested.

**Definition 1.5 (Antidiagonal exclusions).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.bonds`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The preceding column j+1 is bonded to the next column j.

**Definition 1.6 (The literal array predicate).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Legal`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing HardinA233251TriangleStrip.widthLegal is applied at width seven with rowLegal and bonds. Its scanner normalization uses strict earlier cells.

**Definition 1.7 (Decidability of horizontal exclusions).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{decidableRowLegal} (c) : \operatorname{Decidable} (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233255PairTransfer}.\operatorname{rowLegal} (c))) = \operatorname{inferInstanceAs} (\operatorname{Decidable} (\forall (j: \operatorname{Fin} (6)), (c (\operatorname{Fin}.\operatorname{castSucc} (j)) \ne c (\operatorname{Fin}.\operatorname{succ} (j))) \land ((\operatorname{Fin}.\operatorname{val} (c (\operatorname{Fin}.\operatorname{castSucc} (j))) + \operatorname{Fin}.\operatorname{val} (c (\operatorname{Fin}.\operatorname{succ} (j)))) \ne 5)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The instance decides the six adjacent horizontal bonds by finite universal quantification and decidable conjunction. Fin.val explicitly reads each colour as a natural number.

**Definition 1.8 (The positive-height literal count).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.a`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The filter ranges over individual arrays without a quotient.

**Definition 1.9 (The preceding boundary).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.pairs`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the existing complementary-pair map after discarding column zero.

**Definition 1.10 (The literal next-row bond test).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.compatible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every preceding boundary label excludes its bonded next-row label.

**Definition 1.11 (Proper pair words).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Consecutive labels differ.

**Definition 1.12 (Compatible pair words).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.labelCompatible`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.labelCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six cross-row exclusions are expressed in pair labels.

**Definition 1.13 (The successor boundary).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.labelBoundary`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.labelBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Discard column zero only after scanning the entire row.

**Definition 1.14 (The exact labelled continuation transfer).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.pairV`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.pairV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each actual pair word is weighted by its scanner fibre. The empty continuation has weight one.

**Theorem 1.15 (All continuation heights).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.continuation_pair_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.continuation_pair_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the number of rows replaces the individual-colour row sum by the exact scanner-fibre sum. Both initial scanner flags remain arbitrary.

**Theorem 1.16 (The anchored literal readout).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.literal_pair_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.literal_pair_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing literal array decomposition and the continuation identity give this equality at every positive height. Fixing its first colour to zero leaves six pair labels with the exact scanner weight, so the first-row sum also counts individual colours. Precisely, for every natural n, a(n+1) is the integer sum over all functions q from Fin 6 to Fin 3 of rowWeight((false,false),q) times pairV(n,rowFinish((false,false),q),q), with a zero summand unless the word obtained by prepending zero to q is proper. Reducing labelled boundaries to the sixteen canonical proper shapes and aggregating the first-row weights by those shapes are further mathematical obligations; this identity asserts no recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.continuation_pair_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.labelBoundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.labelCompatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.literal_pair_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.pairV`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
