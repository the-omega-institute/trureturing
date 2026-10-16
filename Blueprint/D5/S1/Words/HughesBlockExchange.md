# Actual Masks and the Block Exchange Minimum

## Abstract

The minimum run obstruction for a maximal separating block exchange of actual source masks.

Let the alphabet be arbitrary. A word is a finite list. The two ordered source words u and v are nonempty; Side.first denotes u and Side.second denotes v. A mask records one source at each position, including positions whose letters coincide. The ordered projection selects the letters at positions bearing one source label. Equal lengths are essential: no position may disappear in a zip.

**Definition 1.1 (Ordered source projections).**

$$\forall alpha \in \operatorname{Type},\; \forall q \in Side,\; \forall w \in List\left(alpha\right),\; \forall M \in List\left(Side\right),\; projection\left(q, w, M\right) = filterMap\left(\lambda p. ite\left(snd\left(p\right) = q, some\left(fst\left(p\right)\right), none\left(\right)\right), zip\left(w, M\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zip letters with labels and select the letters bearing q, preserving position order. Optional heads and last elements below are written headOption and lastOption.

**Definition 1.2 (Actual native source masks).**

$$\forall alpha \in \operatorname{Type},\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; \forall w \in List\left(alpha\right),\; \forall M \in List\left(Side\right),\; ValidMask\left(u, v, w, M\right) \Leftrightarrow \left(ValidTwoSchedule\left(u, v, M\right) \land evaluateTwo\left(u, v, M\right) = some\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.ValidMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing binary schedule must consume both sources exactly and evaluate to the actual word. An induction on the schedule proves equivalence to equal word and schedule lengths with ordered projections exactly u and v. The evaluator induction shifts the native occurrence counters when removing a source head.

**Definition 1.3 (Maximal inserted runs).**

$$\forall M \in List\left(Side\right),\; rho\left(M\right) = countP\left(\lambda block. headOption\left(block\right) = some\left(first\right), splitBy\left(\lambda x. \lambda y. x = y, M\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Split the schedule into its maximal homogeneous nonempty blocks, and count the blocks headed by the first source. Equivalently, count transitions from the second source to the first, placing a virtual second-source label before the schedule.

A cut E consists of four letter lists X, A, B and Y. The original word is XABY and its successor is XBAY. A and B are nonempty; the exterior lists may be empty. Transport exchanges the label slices along with these letter blocks. The slices have the exact lengths of the corresponding letter blocks. Their reassembly and the inverse transport therefore preserve every position.

**Definition 1.4 (The original cut word).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; original\left(E\right) = concat\left(X\left(E\right), A\left(E\right), B\left(E\right), Y\left(E\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.original` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate X, A, B and Y in their original order.

**Definition 1.5 (The exchanged word).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; successor\left(E\right) = concat\left(X\left(E\right), B\left(E\right), A\left(E\right), Y\left(E\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exchange A and B while leaving both exterior contexts in place.

**Definition 1.6 (The actual back-transport).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; \forall N \in List\left(Side\right),\; back\left(E, N\right) = concat\left(take\left(length\left(X\left(E\right)\right), N\right), take\left(length\left(A\left(E\right)\right), drop\left(length\left(X\left(E\right)\right) + length\left(B\left(E\right)\right), N\right)\right), take\left(length\left(B\left(E\right)\right), drop\left(length\left(X\left(E\right)\right), N\right)\right), drop\left(length\left(X\left(E\right)\right) + length\left(B\left(E\right)\right) + length\left(A\left(E\right)\right), N\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.back` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cut N at the successor block lengths and reassemble its four complete slices in the original block order. Validity supplies the exact total length.

**Definition 1.7 (Both source projections commute).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; \forall N \in List\left(Side\right),\; Commuting\left(E, N\right) \Leftrightarrow \left(concat\left(projection\left(first, A\left(E\right), take\left(length\left(A\left(E\right)\right), drop\left(length\left(X\left(E\right)\right) + length\left(B\left(E\right)\right), N\right)\right)\right), projection\left(first, B\left(E\right), take\left(length\left(B\left(E\right)\right), drop\left(length\left(X\left(E\right)\right), N\right)\right)\right)\right) = concat\left(projection\left(first, B\left(E\right), take\left(length\left(B\left(E\right)\right), drop\left(length\left(X\left(E\right)\right), N\right)\right)\right), projection\left(first, A\left(E\right), take\left(length\left(A\left(E\right)\right), drop\left(length\left(X\left(E\right)\right) + length\left(B\left(E\right)\right), N\right)\right)\right)\right) \land concat\left(projection\left(second, A\left(E\right), take\left(length\left(A\left(E\right)\right), drop\left(length\left(X\left(E\right)\right) + length\left(B\left(E\right)\right), N\right)\right)\right), projection\left(second, B\left(E\right), take\left(length\left(B\left(E\right)\right), drop\left(length\left(X\left(E\right)\right), N\right)\right)\right)\right) = concat\left(projection\left(second, B\left(E\right), take\left(length\left(B\left(E\right)\right), drop\left(length\left(X\left(E\right)\right), N\right)\right)\right), projection\left(second, A\left(E\right), take\left(length\left(A\left(E\right)\right), drop\left(length\left(X\left(E\right)\right) + length\left(B\left(E\right)\right), N\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.Commuting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the label slices of the arbitrary successor mask N. For each of the two sources, project its letters in A and B and require the two concatenation orders to agree. These projections belong to N, rather than to the selected minimum mask. Back-transport is valid for the original ordered sources exactly when both equations hold, by cancelling the exterior projected words separately.

Admissibility requires a whole maximal inserted run next to a whole separating base block. For a left exchange, A is pure first, B is pure second, X does not end first, and Y begins first. For a right exchange, A is pure second, B is pure first, X ends first, and Y does not begin first. The nonempty pure blocks and all these exterior boundary conditions are retained in Admissible.

**Definition 1.8 (Consecutive maximal separating runs).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; \forall M \in List\left(Side\right),\; Admissible\left(E, M\right) \Leftrightarrow \left(A\left(E\right) \neq [] \land \left(B\left(E\right) \neq [] \land \left(\exists P \in List\left(Side\right),\; \exists Q \in List\left(Side\right),\; \exists R \in List\left(Side\right),\; \exists S \in List\left(Side\right),\; \left(length\left(P\right) = length\left(X\left(E\right)\right) \land \left(length\left(Q\right) = length\left(A\left(E\right)\right) \land \left(length\left(R\right) = length\left(B\left(E\right)\right) \land length\left(S\right) = length\left(Y\left(E\right)\right)\right)\right)\right) \land \left(M = concat\left(P, Q, R, S\right) \land \left(splitBy\left(\lambda x. \lambda y. x = y, M\right) = concat\left(splitBy\left(\lambda x. \lambda y. x = y, P\right), [Q,R], splitBy\left(\lambda x. \lambda y. x = y, S\right)\right) \land \left(\left(Q = replicate\left(length\left(A\left(E\right)\right), first\right) \land \left(R = replicate\left(length\left(B\left(E\right)\right), second\right) \land headOption\left(S\right) = some\left(first\right)\right)\right) \lor \left(Q = replicate\left(length\left(A\left(E\right)\right), second\right) \land \left(R = replicate\left(length\left(B\left(E\right)\right), first\right) \land lastOption\left(P\right) = some\left(first\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The splitBy decomposition places A and B as whole consecutive maximal runs. The other neighbouring inserted run is present. The equivalent endpoint conditions also allow an empty exterior context.

**Definition 1.9 (A chosen global minimum mask).**

$$\forall alpha \in \operatorname{Type},\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; \forall w \in List\left(alpha\right),\; \forall M \in List\left(Side\right),\; \forall r \in \mathbb{N},\; IsMinimumMask\left(u, v, w, M, r\right) \Leftrightarrow \left(ValidMask\left(u, v, w, M\right) \land \left(rho\left(M\right) = r \land \left(\forall N \in List\left(Side\right),\; ValidMask\left(u, v, w, N\right) \Rightarrow r \le rho\left(N\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.IsMinimumMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected mask is actual, has r maximal inserted runs, and no actual mask of the same word has fewer runs. The minimum ranges over all masks, including different labelings of repeated letters.

**Definition 1.10 (Minimum with an empty-family value).**

$$\forall P \in List\left(Side\right) \to Prop\left(\right),\; minRuns\left(P\right) = min\left(\left\{rho\left(M\right) \mid M \in P\right\} \cup \left\{\infty\right\}\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.minRuns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The least attained natural run count is found by well ordering and then embedded in the naturals with infinity. An empty family has value infinity. This definition requires neither finiteness nor decidable equality of the alphabet.

**Definition 1.11 (The all-mask minimum degree).**

$$\forall alpha \in \operatorname{Type},\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; \forall w \in List\left(alpha\right),\; degree\left(u, v, w\right) = minRuns\left(\lambda M. ValidMask\left(u, v, w, M\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.degree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the minimum over all actual native masks of the specified word.

**Definition 1.12 (The commuting minimum).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; c\left(E, u, v\right) = minRuns\left(\lambda N. ValidMask\left(u, v, successor\left(E\right), N\right) \land Commuting\left(E, N\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the minimum over valid successor masks satisfying both commutations.

**Definition 1.13 (The noncommuting minimum).**

$$\forall alpha \in \operatorname{Type},\; \forall E \in BlockCut\left(alpha\right),\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; b\left(E, u, v\right) = minRuns\left(\lambda N. ValidMask\left(u, v, successor\left(E\right), N\right) \land \neg Commuting\left(E, N\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the minimum over valid successor masks failing at least one commutation. If there is no such mask, this value is infinity.

**Theorem 1.14 (Native schedule and projection equivalence).**

$$\forall alpha \in \operatorname{Type},\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; \forall w \in List\left(alpha\right),\; \forall M \in List\left(Side\right),\; ValidMask\left(u, v, w, M\right) \Leftrightarrow \left(length\left(M\right) = length\left(w\right) \land \left(projection\left(first, w, M\right) = u \land projection\left(second, w, M\right) = v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.mask_projections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal total lengths and both ordered source projections characterize the original schedule validity and evaluation. This is the original evaluator induction.

**Definition 1.15 (A single inserted-run start).**

$$\forall p \in Side,\; \forall q \in Side,\; step\left(p, q\right) = ite\left(p = second \land q = first, 1, 0\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A transition contributes one precisely from second to first, and zero otherwise.

**Definition 1.16 (Recursive inserted-run starts).**

$$\forall p \in Side,\; starts\left(p, []\right) = 0 \land \left(\forall q \in Side,\; \forall s \in List\left(Side\right),\; starts\left(p, cons\left(q, s\right)\right) = step\left(p, q\right) + starts\left(q, s\right)\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.starts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read every label with the previous label as state. The empty suffix contributes zero.

**Definition 1.17 (The final label with an empty fallback).**

$$\forall p \in Side,\; \forall s \in List\left(Side\right),\; lastSide\left(p, s\right) = getD\left(lastOption\left(s\right), p\right)$$

*Formalization.* `D5/S1/Words/HughesBlockExchange.lastSide` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Return the last actual label, using p only for the empty list.

**Theorem 1.18 (Run starts across concatenation).**

$$\forall p \in Side,\; \forall s \in List\left(Side\right),\; \forall t \in List\left(Side\right),\; starts\left(p, concat\left(s, t\right)\right) = starts\left(p, s\right) + starts\left(lastSide\left(p, s\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.starts_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The suffix starts from the actual final prefix label, or from p for an empty prefix.

**Theorem 1.19 (Maximal runs and transition starts).**

$$\forall M \in List\left(Side\right),\; rho\left(M\right) = starts\left(second, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.rho_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A virtual initial second label makes the recursive transition count equal to rho.

**Theorem 1.20 (Ordered projections across a fitting cut).**

$$\forall alpha \in \operatorname{Type},\; \forall q \in Side,\; \forall a \in List\left(alpha\right),\; \forall b \in List\left(alpha\right),\; \forall s \in List\left(Side\right),\; \forall t \in List\left(Side\right),\; length\left(a\right) = length\left(s\right) \Rightarrow projection\left(q, concat\left(a, b\right), concat\left(s, t\right)\right) = concat\left(projection\left(q, a, s\right), projection\left(q, b, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.projection_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matching prefix word and mask lengths allow both zipped projections to split at the cut.

**Theorem 1.21 (Projection of a pure label block).**

$$\forall alpha \in \operatorname{Type},\; \forall q \in Side,\; \forall t \in Side,\; \forall a \in List\left(alpha\right),\; projection\left(q, a, replicate\left(length\left(a\right), t\right)\right) = ite\left(t = q, a, []\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.projection_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complete block is retained for its own label and erased for the other label.

**Theorem 1.22 (Starts of a nonempty pure block).**

$$\forall p \in Side,\; \forall q \in Side,\; \forall n \in \mathbb{N},\; 0 < n \Rightarrow starts\left(p, replicate\left(n, q\right)\right) = step\left(p, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.starts_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the first transition can contribute in a positive length pure block.

**Theorem 1.23 (The transported admissible successor mask).**

$$\forall alpha \in \operatorname{Type},\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; \forall E \in BlockCut\left(alpha\right),\; \forall M \in List\left(Side\right),\; \left(ValidMask\left(u, v, original\left(E\right), M\right) \land Admissible\left(E, M\right)\right) \Rightarrow \left(\exists N \in List\left(Side\right),\; ValidMask\left(u, v, successor\left(E\right), N\right) \land \left(Commuting\left(E, N\right) \land rho\left(N\right) + 1 = rho\left(M\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.intended_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual pure blocks preserve both projections under transport. Maximality and the exterior inserted run make exactly one inserted run disappear.

**Theorem 1.24 (Universal lower bounds for the minimum).**

$$\forall P \in List\left(Side\right) \to Prop\left(\right),\; \forall k \in WithTop\left(\mathbb{N}\right),\; k \le minRuns\left(P\right) \Leftrightarrow \left(\forall N \in List\left(Side\right),\; P\left(N\right) \Rightarrow k \le rho\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.le_minRuns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A lower bound holds for the minimum exactly when it holds for every member, including the empty-family infinity case.

**Theorem 1.25 (Every actual member bounds the minimum).**

$$\forall P \in List\left(Side\right) \to Prop\left(\right),\; \forall N \in List\left(Side\right),\; P\left(N\right) \Rightarrow minRuns\left(P\right) \le rho\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.minRuns_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual mask in the family supplies an upper bound by its native run count.

**Theorem 1.26 (The complete exchange minimum criterion).**

$$\forall alpha \in \operatorname{Type},\; \forall u \in List\left(alpha\right),\; \forall v \in List\left(alpha\right),\; \forall w \in List\left(alpha\right),\; \forall z \in List\left(alpha\right),\; \forall E \in BlockCut\left(alpha\right),\; \forall M \in List\left(Side\right),\; \forall r \in \mathbb{N},\; \left(u \neq [] \land \left(v \neq [] \land \left(w = original\left(E\right) \land \left(z = successor\left(E\right) \land \left(IsMinimumMask\left(u, v, w, M, r\right) \land \left(1 < r \land Admissible\left(E, M\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(c\left(E, u, v\right) = r - 1 \land \left(degree\left(u, v, z\right) = min\left(r - 1, b\left(E, u, v\right)\right) \land \left(degree\left(u, v, z\right) = r - 1 \Leftrightarrow r - 1 \le b\left(E, u, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesBlockExchange.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport any successor labeling back across the two nonempty exchanged blocks. Only boundary transitions change. Comparing the two transition sums shows that the inserted-run count changes by at most one, without a purity assumption on this arbitrary labeling. For a commuting valid successor mask, back-transport is an original mask. Minimality at r therefore forces at least r minus one successor runs. The chosen admissible exchange supplies the matching mask: its two pure blocks preserve both ordered projections and exactly two adjacent inserted runs merge. Thus the commuting minimum equals r minus one. Partition all valid successor masks by the two commutation equations to obtain the minimum identity and its exactness criterion. The statement includes r equal to two, coincident letters, empty exterior contexts, and the infinite noncommuting minimum. It concerns insertion-run minima and does not assert an iteration-depth theorem or a characterization of a physical channel.

## References

- Truth anchor: `D5/S1/Words/HughesBlockExchange.Admissible`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.Commuting`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.IsMinimumMask`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.ValidMask`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.b`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.back`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.c`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.degree`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.intended_successor`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.lastSide`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.le_minRuns`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.mask_projections`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.minRuns`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.minRuns_le`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.original`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.projection`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.projection_append`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.projection_pure`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.result`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.rho`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.rho_starts`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.starts`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.starts_append`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.starts_pure`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.step`
- Truth anchor: `D5/S1/Words/HughesBlockExchange.successor`
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation](Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.md)
