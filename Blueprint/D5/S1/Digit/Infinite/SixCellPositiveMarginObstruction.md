# Connected Instruments and Positive Margins

## Abstract

Connected scalar instruments and the six-cell positive-margin obstruction.

**Definition 1.1 (Actual cells).**

Lean statement: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.cell`

*Formalization.* `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cell of color i consists of scalars x in X=[-1,1+t] with Q(x)=i. The function outside X has no effect on the instrument.

**Definition 1.2 (Connected instruments).**

Lean statement: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.connectedInstrument`

*Formalization.* `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.connectedInstrument` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each color fibre is a nonempty connected subset of the real line. Singleton cells and every endpoint assignment are allowed; colors need not be ordered.

**Definition 1.3 (Closed grid purity).**

Lean statement: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.closedGridPure`

*Formalization.* `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.closedGridPure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of closed cell coordinates, all legal branch points in that rectangle have the same window label. The legal tail interval is [-1,1+t] for three, null and two, and [-1,t] for five and twenty-five.

**Theorem 1.4 (The six-cell obstruction).**

Lean statement: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t=(sqrt(5)-1)/2, g=t^3 and X=[-1,1+t]. For every integer q with 1<=q<=6, every Q from the real line to Fin q whose q fibres in X are nonempty connected intervals, every deterministic decoder from Fin q times Fin q to the five legal window labels, and every eta>0, there is an infinite Boolean address x without adjacent ones and real errors e_0,e_1 with |e_0|<eta and |e_1|<eta such that the decoder returns a label different from the first three-bit window of x.

The two readings are Q(clip_X(kappa(x)+e_0)) and Q(clip_X(kappa(Tx)+e_1)); T deletes exactly three individual bits of that same address. The clip is the projection to X. The five labels are three (010), null (000), five (001), two (100) and twenty-five (101), in low-to-high bit order. The address scalar is the existing infinite grouped-window series.

A positive uniform margin would make every closed cell rectangle pure: approximate any two differently labelled points in that rectangle by targets in its actual fibres. Singleton fibres require no interior. Each graph point is realized by one actual legal address and its actual tail.

After ordering the cells, the common legal tails -1 and t force the colors of g,t,2t,1+t to be 2,3,4,5. The diagonal branch fixed points -1/2,0,t/2,(1+t)/2 force colors 0,1,2,3. Shared boundaries between the first four closed cells pass the occupied current colors from one tail column to the next. The third such boundary makes label two occupy current color four in tail color three. Label twenty-five at tail t occupies that same rectangle, contradicting purity.

An instrument with fewer than six cells embeds into six color slots; the same forced color constraints and contradiction apply. The proof allows arbitrary initial color numbering, singleton cells and every assignment of shared endpoints.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.cell`
- Truth anchor: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.closedGridPure`
- Truth anchor: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.connectedInstrument`
- Truth anchor: `D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction.result`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
