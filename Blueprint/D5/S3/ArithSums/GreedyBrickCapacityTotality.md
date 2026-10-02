# Greedy brick rows and capacities

## Abstract

Natural gap transfers realize the literal row scan and supported contiguous brick placement.

Capacities and occupied row widths are stored from top to bottom. The function widths forms cumulative sums of the natural capacities. Zero gaps are allowed. The published A395531 Python generator stores rows in the opposite order. sourceRowStep reverses that convention: it first tests a new top row, then scans existing rows downwards, extending the first row whose width plus the new brick width is supported below. The floor is always available. This model uses unbounded natural numbers.

**Theorem 1.1 (Capacity transfer bounds and exact area increment).**

$$\forall n \in \mathbb{N},\; \forall cs \in List\left(\mathbb{N}\right),\; \left(0 < n \land \left(\forall c \in \mathbb{N},\; member\left(c, cs\right) \Rightarrow c \le 2 \cdot n - 1\right)\right) \Rightarrow \left(length\left(cs\right) \le length\left(step\left(n, cs\right)\right) \land \left(length\left(step\left(n, cs\right)\right) \le length\left(cs\right) + 1 \land \left(\left(\forall c \in \mathbb{N},\; member\left(c, step\left(n, cs\right)\right) \Rightarrow c \le 2 \cdot n - 1\right) \land area\left(step\left(n, cs\right)\right) = area\left(cs\right) + n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickCapacityTotality.step_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every capacity is at most 2n-1. A placement preserves height or creates exactly one row, preserves the capacity bound, and increases weighted area by n. The donor-transfer induction proves all four conclusions on arbitrary bounded natural capacity lists.

**Theorem 1.2 (All finite literal trajectories have the exact placed area).**

$$\forall N \in \mathbb{N},\; \left(\forall c \in \mathbb{N},\; member\left(c, trajectory\left(N\right)\right) \Rightarrow c \le 2 \cdot N - 1\right) \land \left(area\left(trajectory\left(N\right)\right) = sumRangeId\left(N + 1\right) \land \left(length\left(trajectory\left(N\right)\right) \le length\left(trajectory\left(N + 1\right)\right) \land length\left(trajectory\left(N + 1\right)\right) \le length\left(trajectory\left(N\right)\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickCapacityTotality.reachable_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction from the empty wall gives the capacity cap 2N-1 and area equal to the sum of labels 0 through N. Height is monotone and increases by at most one at each placement.

**Theorem 1.3 (Positive monotone reconstructed rows and exact inverse gaps).**

$$\forall N \in \mathbb{N},\; 0 < N \Rightarrow \left(length\left(widths\left(trajectory\left(N\right)\right)\right) = length\left(trajectory\left(N\right)\right) \land \left(PairwiseLe\left(widths\left(trajectory\left(N\right)\right)\right) \land \left(sum\left(widths\left(trajectory\left(N\right)\right)\right) = area\left(trajectory\left(N\right)\right) \land \left(capacities\left(widths\left(trajectory\left(N\right)\right)\right) = trajectory\left(N\right) \land \left(\forall w \in \mathbb{N},\; member\left(w, widths\left(trajectory\left(N\right)\right)\right) \Rightarrow 0 < w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickCapacityTotality.reachable_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive endpoint N, cumulative gap sums give positive widths increasing downwards, preserve height and area, and recover the original capacities under the inverse map.

**Theorem 1.4 (Every positive row has an actual least birth).**

$$\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left(\exists B \in \mathbb{N},\; 0 < B \land \left(length\left(trajectory\left(B\right)\right) = m \land \left(\left(\forall K \in \mathbb{N},\; K < B \Rightarrow length\left(trajectory\left(K\right)\right) < m\right) \land B \le birthBound\left(m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickCapacityTotality.birth_totality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact area and uniform capacity bound force every positive height to be reached. Its least reaching endpoint has exactly that height. The first birth is at most 1; for m>=2 the endpoint is at most 2m(m-1)-1. No missing-row default is used.

**Theorem 1.5 (The two recursive algorithms are conjugate).**

$$\forall n \in \mathbb{N},\; \forall cs \in List\left(\mathbb{N}\right),\; 0 < n \Rightarrow widths\left(step\left(n, cs\right)\right) = sourceRowStep\left(n, widths\left(cs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickCapacityTotality.row_transition_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural capacity list and positive brick width, reconstructing widths after transfer agrees with applying the source row scan. The recursive proof tracks a common offset through the donor scan. No reachability premise, capacity bound or conjectured identity is used.

occupied(ws,u,y) means that unit cell (u,y) belongs to the wall. Row zero is the floor; each row is the half-open interval [0,w). AppendSite enumerates supported existing-row frontiers without making a greedy choice. PlacementSite also permits a supported new top row. LegalBrick requires disjointness over the entire new interval, support over its entire bottom unless on the floor, and left contact with the axis or the occupied wall. BrickAddition requires the exact union of old occupied cells with the new interval, together with those three constraints.

**Theorem 1.6 (The source scan realizes the leftmost highest legal placement).**

$$\forall n \in \mathbb{N},\; \forall ws \in List\left(\mathbb{N}\right),\; \left(0 < n \land PairwiseLe\left(ws\right)\right) \Rightarrow \left(\exists x \in \mathbb{N},\; \exists y \in \mathbb{N},\; PlacementSite\left(n, ws, x, y\right) \land \left(\left(\forall xp \in \mathbb{N},\; \forall yp \in \mathbb{N},\; LegalBrick\left(n, ws, xp, yp\right) \Rightarrow \left(x \le xp \land yp \le y\right)\right) \land BrickAddition\left(ws, sourceRowStep\left(n, ws\right), n, x, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GreedyBrickCapacityTotality.source_row_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For widths increasing downwards, the source scan gives one legal brick addition. Its left endpoint is no larger, and its row is no lower, than those of every LegalBrick position. The proof also shows internally that every physical position satisfying the stated cell constraints is among the enumerated frontiers. Positive row widths are supplied for actual nonempty trajectories by the existing reachable_rows theorem; positive least births use birth_totality.

birthBound(m) is 1 when m=1 and 2m(m-1)-1 otherwise. sumRangeId(k) denotes the sum of the natural labels in range(k). These results establish the row algorithm and the contiguous integer-cell placement model. The labelled-history and continuous-plane theorems are supplied by the separate GreedyBrickLabelledHistory source. The original OEIS self-composition identity is not proved. Source statements are attributed to OEIS A395531 and A233380; the algorithm-correspondence and geometric proofs are derivations of the stated rule.

## References

- Truth anchor: `D5/S3/ArithSums/GreedyBrickCapacityTotality.birth_totality`
- Truth anchor: `D5/S3/ArithSums/GreedyBrickCapacityTotality.reachable_invariants`
- Truth anchor: `D5/S3/ArithSums/GreedyBrickCapacityTotality.reachable_rows`
- Truth anchor: `D5/S3/ArithSums/GreedyBrickCapacityTotality.row_transition_correspondence`
- Truth anchor: `D5/S3/ArithSums/GreedyBrickCapacityTotality.source_row_geometry`
- Truth anchor: `D5/S3/ArithSums/GreedyBrickCapacityTotality.step_invariants`
