# Attained summaries and finite-block prefix queries

## Abstract

Fixed scalar summaries attain a first sufficient root block and support exact prefix counts by rollback through the original ternary substitution.

Use the original letters one, two and three and the substitution tau: one to two, two to three, three to three followed by one. These are the Letter and tau of OriginalHFoundation. The finite word at level t and letter a is the existing image tau t a, independently defined by substitution of finite lists. The numerical transitions below never read that word.

**Definition 1.1 (Three scalar coordinates).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Triple`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Triple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Triple contains three natural numbers one, two and three. It is a fixed-size tuple, with no level-indexed array.

**Definition 1.2 (Letter-indexed coordinate).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.at`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.at` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For a triple v and original letter a, v.at a selects v.one, v.two or v.three according to the letter. The letters are labels, not prefix counts.

**Definition 1.3 (Simultaneous forward update).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.forward`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.forward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For v=(a,b,c), forward v=(b,c,a+c). Each new coordinate is evaluated from the old tuple.

**Definition 1.4 (Reverse update on attained tuples).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.reverse`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.reverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For v=(u,v,w), reverse returns (w-v,u,v), using natural subtraction. Its correctness and subtraction premise are asserted for actual attained successors; no claim of invertibility on arbitrary triples is made.

**Definition 1.5 (Six scalar summary coordinates).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Summary`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Summary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Summary contains a lengths triple and a counts triple. Counts refer to the letter one.

**Definition 1.6 (Literal initial summary).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.initial`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

The level-zero lengths are (1,1,1) and counts are (1,0,0), exactly the lengths and one-counts of the three singleton letters.

**Definition 1.7 (Simultaneous summary advancement).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.advance`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.advance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

advance applies forward separately to the old lengths and counts triples.

**Definition 1.8 (Simultaneous summary rollback).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.rollback`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.rollback` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

rollback applies reverse separately to the lengths and counts triples. On generated(t+1) it equals generated(t), including zero count coordinates.

**Definition 1.9 (Numeric provenance at every level).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.generated`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.generated` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

generated 0=initial and generated(t+1)=advance(generated t). These recurrences construct the six numerical coordinates from fixed literals, without word inputs or tables. They also describe the sequence of summaries reached by acquisition.

**Definition 1.10 (Retained attained data).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Top`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Top` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Top contains a natural layer counter and its summary. It has no word, prefix value, stack or array.

**Definition 1.11 (First threshold acquisition).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.acquire`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.acquire` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For a natural threshold N, acquire N starts at layer zero with initial. At each layer it tests whether the current third length is at least N. If so it returns that counter and those six coordinates; otherwise it replaces the summary by advance of the current summary and increments the counter. Its auxiliary alignment argument is a proposition erased from computation. The termination measure is used only in the proof, not as a runtime fuel argument or a stopping test.

**Definition 1.12 (An analysis-only binary bound).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.analysisBits`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.analysisBits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

analysisBits N is the least natural b with N strictly less than 2^b. Thus N+1 is at most 2^b, and every smaller b fails that strict inequality. This quantity is used only to state and prove bounds; acquire neither accepts nor computes it.

**Definition 1.13 (Active query registers).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.State`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

State contains the active layer, six summary coordinates, original letter, residual natural length r and accumulated natural count Q. The retained top is supplied separately and is never updated by a descent.

**Definition 1.14 (Query initialization).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.start`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.start` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

start z a m copies the top layer and summary into the active state, with active letter a, residual m and total zero. The general finite-block argument allows every a; the scalar query uses the root three.

**Definition 1.15 (One exact numeric descent).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.descend`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.descend` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

At layer zero descend leaves the state unchanged. At a positive layer it first rolls back both triples and reduces the layer by one. Old letter one becomes two, and old letter two becomes three, retaining r and Q. For old letter three, let L be the third length in the rolled-back summary. If r is at most L, the new letter is three and r,Q are retained. If r is greater than L, the new letter is one, the new residual is r-L, and the new total is Q plus the rolled-back third count. Equality r=L belongs to the left branch.

**Definition 1.16 (Reached states by iteration).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.trajectory`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.trajectory` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

trajectory z a m k is the k-fold iteration of descend from start z a m. It is a mathematical description of a sequence of active states; it is not an array input, a supplied proof trace, or an oracle consulted by descend.

**Definition 1.17 (Terminal singleton readout).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.readout`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.readout` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

readout q is q.total plus q.residual if q.letter is one, and q.total otherwise. At a reachable terminal state the residual is zero or one, so this is exactly the count contributed by the remaining singleton prefix.

**Definition 1.18 (Complete single scalar query).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.query`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.query` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

query z m applies readout to trajectory z three m z.layer. Thus its evaluation uses exactly the top's number of descents. There is no branch that stops early at address zero, no previous prefix value, and no expanded word input.

**Definition 1.19 (Full finite-prefix invariant).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Invariant`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Invariant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Invariant rank m q is the conjunction of four clauses: q.summary=generated(q.layer); q.residual is at most the active length coordinate; q.total+q.residual is at most m; and rank=q.total+countOne(take q.residual (image tau q.layer q.letter)). All quantities are natural numbers, so nonnegativity is part of their domain. The rank is the count of the fixed initial finite-block prefix, not a value provided to the numerical transition.

**Definition 1.20 (Subtraction premises at reached states).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Legal`

*Formalization.* `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

Legal q states that if q.layer is positive then its lengths.two is at most lengths.three and counts.two is at most counts.three, making both rollback subtractions nonnegative. It also states that in a right split the rolled-back third length is at most the residual. Positive layer supplies the premise for decrementing the counter. These are properties of reached states, not assumptions imposed on query callers.

**Theorem 1.21 (First acquisition and complete prefix-query simulation).**

Lean statement: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.attained_summary_query`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Hofstadter/AttainedSummaryQuery.attained_summary_query` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pierre Letouzey, Shuo Li, Wolfgang Steiner (2024). *Pointwise order of generalized Hofstadter functions G, H and beyond*. URL: <https://arxiv.org/abs/2410.00529v2>.

*Commentary.*

For every natural N, put z=acquire N and T=z.layer. The theorem proves the following conjunction. The attained summary equals generated T; its third length is at least N; every earlier generated third length is less than N; and any other level satisfying those firstness conditions is T. For b=analysisBits N, N is strictly less than 2^b, every smaller exponent has power at most N, and T is at most 3b. For every natural t and original letter a, generated t's length equals the length of image tau t a and its count equals that word's one-count, with count at most length at most 2^t. For every natural m at most N and every k at most T, the reached active layer is T-k, the full Invariant for countOne(take m (image tau T three)) holds, and Legal holds. At k=T the layer is zero and the residual is zero or one. Finally query z m equals that actual finite prefix's one-count, query z m is at most m, and its natural complement m-query z m is at most m. Nonnegativity follows from the natural-number domains.

The summary proof uses image tau (t+1) one=image tau t two, image tau (t+1) two=image tau t three, and image tau (t+1) three=image tau t three followed by image tau t one. Induction matches the numerical recurrences to lengths and counts. Three forward updates take (a,b,c) to (a+c,a+b+c,a+b+2c); each coordinate at level 3j is at least 2^j. Each update at most doubles the largest length, giving the upper bound 2^t. These bounds prove that threshold acquisition terminates and that the first attained T is at most 3b.

The common query argument is uniform in every initial level T, original letter a, and m at most that finite block's length. Rollback on generated(t+1) is generated t. At a three split, finite-list take and append identities conserve the prefix count. In the right branch the old residual bound gives 0<r-L at most the right-block length, and countOne(left) at most L gives Q+countOne(left)+(r-L) at most Q+r. This preserves the address budget. The terminal singleton identity converts the conserved count into the scalar readout. This all-state induction supplies the acquired-root instance; no correct summary, invariant or return value is a caller hypothesis.

Closed endpoints include m=0, the complete root block whenever its length is within N, a complete parent block, and the split equality r=L. The left equality branch retains a complete left block; a complete parent in the right branch leaves a complete right block. For N=1, acquisition returns layer zero and the literal initial summary, so the singleton readout handles m=0 and m=1 directly. The all-state layer equation ensures exactly T positive-layer descents, including m=0. Every active residual and total is at most m, and every reached summary coordinate is bounded by 2 to its active layer, hence by 2^T.

The finite root block is block T in OriginalHFoundation. Its word_characterization identifies take m of that block with wordPrefix word m whenever m is at most its length. The original_h_morphic_prefix identity then makes the complement m-query z m equal the existing original H(m). This is an application of the existing infinite-word correspondence, not a new definition of H.

The original substitution and H correspondence are supplied by the cited Library note and its mathematical sources. The attained-summary and rollback induction here is a derivation from that substitution and finite-list identities; no novelty claim is made. The statements concern exact natural-number transitions and finite-block semantics. They do not assert binary serialization, physical copying costs, local-head arithmetic, visited-space bounds, time bounds, original input acquisition or three dependent physical query occurrences.

## References

- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Invariant`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Legal`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.State`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Summary`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Top`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.Triple`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.acquire`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.advance`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.analysisBits`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.at`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.attained_summary_query`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.descend`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.forward`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.generated`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.initial`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.query`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.readout`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.reverse`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.rollback`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.start`
- Truth anchor: `D5/S1/Words/Hofstadter/AttainedSummaryQuery.trajectory`
- Dependency: [D5/S1/Words/Hofstadter/OriginalHFoundation](OriginalHFoundation.md)
