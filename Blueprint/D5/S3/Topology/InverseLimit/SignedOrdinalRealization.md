# One literal omega-one prefix

## Abstract

SignedOrdinalRealization

**Definition 1.1 (One literal omega-one prefix).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.finalPrefix`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.finalPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The final Prefix reads each carrier from the same canonical well-founded run under CH. Below omega the carriers are full Boolean cubes. Closedness, nonemptiness, compatibility and onto restrictions are inherited from the actual later state and its coherence. There is no second recursion.

**Definition 1.2 (Data at every proper cutoff).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.properData`

*Formalization.* `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.properData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only proper countable cutoffs carry Data. Whole U, V and nu are read at the original row birth. Incoming I and J are read at their carrier stage. Permanent reservoirs are read from the original outgoing R at max(row,label), including at the last row of a successor slice.

**Theorem 1.3 (Original laws on all proper slices).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.properLaws`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.properLaws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All eligible A through F and DI/DJ hold at every proper cutoff, including successors. F uses the regular bounded incoming evidence retained by the actual state, from the previous outgoing R or the actual limit Extension.

**Theorem 1.4 (The slice is literal).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every proper slice has exactly the final Prefix carrier at the same ordinal.

**Theorem 1.5 (Every run carrier is preserved).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.carrier_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.carrier_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every earlier carrier in an actual state equals the corresponding final Prefix carrier. Pairwise coherence makes the value independent of which later state is used to read it.

**Theorem 1.6 (The actual top carrier).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.top_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.top_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every stage from omega onward the final carrier is literally the top carrier of the canonical run state.

**Theorem 1.7 (The original initial cubes).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.initial_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.initial_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every coordinate at most omega the carrier is the full Boolean function space.

**Theorem 1.8 (The identical whole birth).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.wholeBirth_read`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.wholeBirth_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final whole birth is the actual newborn Q, transported solely across equality of the literal carrier.

**Theorem 1.9 (Original whole measure labels).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.whole_measure`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.whole_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each original label and natural index reads the identical signed measure in the actual whole birth, with the necessary heterogeneous equality.

**Theorem 1.10 (Slice measures retain whole labels).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_nu`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_nu` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed measure in every proper slice equals the original whole birth measure. Labels need not be eligible at the cutoff to be preserved.

**Theorem 1.11 (Actual incoming J).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_J`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For eligible old rows and labels the proper Data J is exactly the actual incoming predecessor J at that carrier.

**Theorem 1.12 (The selected outgoing carrier).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.successor_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.successor_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier at succ(a) equals the coordinates.carrier of the same selected R at a.

**Theorem 1.13 (Final projections factor literally).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.projection_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.projection_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction between two proper carriers composed with final projection equals the earlier final projection.

**Theorem 1.14 (Onto the initial countable cube).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.initial_onto`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.initial_onto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same final cube maps onto the full Boolean cube on omega by its original coordinate restriction. Compact inverse-limit lifting supplies a point above every initial function.

**Theorem 1.15 (Permanent slice reservoirs).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_N`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_N` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every born row and label pair in any proper slice reads the original permanent reservoir at their unique outgoing maximum.

**Theorem 1.16 (Original reservoirs at every eligible carrier).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.reservoir_incoming`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.reservoir_incoming` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permanent outgoing maximum reservoirs equal the actual incoming oldN at every eligible later carrier.

**Theorem 1.17 (Actual cofinal support launches).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.launch`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.launch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each original support index is launched arbitrarily late. The newborn V at outgoing row a is the exact pullback of the original U along the same final Prefix restriction. Its archive is available at succ(a); support indices remain distinct from whole measure labels.

No final endpoint is asserted.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.carrier_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.finalPrefix`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.initial_carrier`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.initial_onto`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.launch`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.projection_factor`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.properData`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.properLaws`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.reservoir_incoming`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_J`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_N`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_carrier`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.slice_nu`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.successor_carrier`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.top_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.wholeBirth_read`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalRealization.whole_measure`
- Dependency: [D5/S3/Topology/InverseLimit/SignedBallHistoryCapture](SignedBallHistoryCapture.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalHistory](SignedOrdinalHistory.md)
