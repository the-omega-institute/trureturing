# Three-donor correction on the actual calendar

## Abstract

Six actual donors convert an adaptive charge array into one global preset stream.

**Definition 1.1 (Non-donor entries).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.outside`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.outside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

outside(a,r,i) is zero at r,r+1,r+2 and equals a(i) at every other natural offset.

**Definition 1.2 (The repaired ordered row).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.correctedRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.correctedRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let u be the sum of a(h) over h<r and z the sum of outside(a,r,h) over h<=m, in ZMod(2). The corrected row equals outside plus u at r and u+z at r+2. It is zero at r+1. The three donors absorb full-window parity and cancel the prefix through r, making the literal inverse zero at that mark. All other entries remain unchanged.

**Definition 1.3 (Six ordinary INITIAL phases).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.Donor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.Donor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Donor(m,j) means j=m-4+e*m+delta in ZMod(2m-1), for natural e<2 and delta<3. The six phases retain their original INITIAL labels; the theorem does not remove these sources.

**Definition 1.4 (Chronological corrected charges).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.codingRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.codingRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At issued index t, first read the own-path array at INITIAL phase t*m+h in the cyclic phase group, for each local offset h. Then correct that row at local mark m-4-floor(t/2). The physical word is its prefix-parity inverse, with exactly m literal bits.

**Theorem 1.5 (Native shared coding archive and unchanged non-donors).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall f \in \operatorname{Option}\left(\operatorname{LiveRecord}\left(2 \cdot m - 2\right)\right) \to Y,\; \forall table \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right) \to Y,\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \forall d \in \mathbb{N},\; \forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall s \in \mathbb{N},\; \left(\left(\left(\left(\left(5 \le m \land \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall s \in \mathbb{N},\; s < 2 \cdot m - 2 \Rightarrow f\left(\operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = table\left(j\right)\right)\right) \land 1 \le d\right) \land d \le 2 \cdot m - 10\right) \land \left(\forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(2 \cdot m - 2, m, alphabet\right)\right),\; \operatorname{output}\left(2 \cdot m - 2, \operatorname{flattenWords}\left(history\right)\right) = \operatorname{some}\left(0\right) \Rightarrow \left(\exists c \in \mathbb{N},\; c \le d \land \operatorname{execute}\left(2 \cdot m - 2, pi, d, \operatorname{flattenWords}\left(history\right), \operatorname{some}\left(0\right), nil\right) = \operatorname{some}\left((f\left(\operatorname{OriginalRecord}\left(2 \cdot m - 2, \operatorname{flattenWords}\left(history\right)\right)\right),c)\right)\right)\right)\right) \land s < 2 \cdot m - 2\right) \Rightarrow \left(\left(\left(\left(\left(\forall t \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \left(\neg \operatorname{Donor}\left(m, j\right)\right) \Rightarrow \operatorname{windowCharge}\left(2 \cdot m - 2, m, \operatorname{codingRow}\left(table, pi, d, \operatorname{val}\left(t\right)\right), j - \operatorname{val}\left(t\right) \cdot m\right) = \operatorname{phaseCharges}\left(table, pi, d, \operatorname{val}\left(t\right), j\right)\right) \land \operatorname{length}\left(\operatorname{chargeBlocks}\left(2 \cdot m - 2, m, alphabet, \operatorname{codingRows}\left(table, pi, d\right)\right)\right) = d\right) \land \operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(2 \cdot m - 2, m, alphabet, \operatorname{codingRows}\left(table, pi, d\right)\right), \operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = \operatorname{chargeArchive}\left(2 \cdot m - 2, m, \operatorname{codingRows}\left(table, pi, d\right), v, j\right)\right) \land \operatorname{length}\left(\operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(2 \cdot m - 2, m, alphabet, \operatorname{codingRows}\left(table, pi, d\right)\right), \operatorname{some}\left(\langle v,-j,s\rangle\right)\right)\right) = d\right) \land \left(\neg none \in \operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(2 \cdot m - 2, m, alphabet, \operatorname{codingRows}\left(table, pi, d\right)\right), \operatorname{some}\left(\langle v,-j,s\rangle\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_donor_coding_archive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The display uses k=2m-2. codingRows(table,pi,d) is List.ofFn(t:Fin(d) => codingRow(table,pi,d,val(t))). Proof arguments to chargeBlocks, output, execute and OriginalRecord are omitted; nil is the empty acquired archive. flattenWords is the original history flatMap of complete literal words. Cyclic subtraction includes the cast of the chronological index times m. Y is arbitrary, including higher universes.

The arbitrary correct controller supplies the root-zero and support facts from `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges`. The root mark is m-4>0, so the correction preserves its zero first entry. This clears every inherited legal tail. The marks are nonincreasing, giving each chronological seam inequality; all three corrected donor positions lie within the ordered window. The parity and prefix-zero identities therefore permit direct use of `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety` for the full literal archive, under either original alphabet.

Write t=2h+e. The actual calendar identity 2m=1 in ZMod(2m-1) puts each corrected offset at INITIAL phase m-4+e*m+delta. The horizon bound keeps h<=m-4, so natural subtraction has not truncated this placement. Outside these six phases, the full-window charge remains exactly the original own-path coordinate. Off the physical window both charges are zero. The same words work for both INITIAL scalars; only their own scalar archives are read.

This is the first d-block coding portion. Donor coordinates have been changed and require the four additional identifying rows. Those rows, their seam safety, label decoding, other adaptive horizons, finite price attainment and the four-block price inequality are outside this coding-prefix theorem.

**Definition 1.6 (One literal occupied bit).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.pairRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.pairRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pairRow(r,h) is one exactly at h=r or h=r+1, and zero elsewhere. Its prefix-parity inverse is the complete word whose only true bit is at local position r.

**Definition 1.7 (Four actual identifying rows).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.suffixRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.suffixRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

suffixRow(m,d,t) is pairRow at local position m-4-floor((d+t)/2)+floor(t/2). For t=0,1,2,3 its INITIAL support is the consecutive pair beginning at m-4+((d+t) mod 2)*m+floor(t/2). Thus the first and second occurrences of each parity test the first and second edge of its own donor triple on the actual moving calendar.

**Definition 1.8 (The complete paid prefix).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.conversionRows`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.conversionRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

conversionRows(table,pi,d) lists d+4 rows: codingRow(table,pi,d,t) when t<d, and suffixRow(m,d,t-d) otherwise. Every row is issued as its m-bit prefix-parity inverse.

**Theorem 1.9 (One global stream with four additional paid blocks).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall f \in \operatorname{Option}\left(\operatorname{LiveRecord}\left(2 \cdot m - 2\right)\right) \to Y,\; \forall table \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right) \to Y,\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \forall d \in \mathbb{N},\; \left(\left(\left(\left(5 \le m \land \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall s \in \mathbb{N},\; s < 2 \cdot m - 2 \Rightarrow f\left(\operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = table\left(j\right)\right)\right) \land 1 \le d\right) \land d \le 2 \cdot m - 10\right) \land \left(\forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(2 \cdot m - 2, m, alphabet\right)\right),\; \operatorname{output}\left(2 \cdot m - 2, \operatorname{flattenWords}\left(history\right)\right) = \operatorname{some}\left(0\right) \Rightarrow \left(\exists c \in \mathbb{N},\; c \le d \land \operatorname{execute}\left(2 \cdot m - 2, pi, d, \operatorname{flattenWords}\left(history\right), \operatorname{some}\left(0\right), nil\right) = \operatorname{some}\left((f\left(\operatorname{OriginalRecord}\left(2 \cdot m - 2, \operatorname{flattenWords}\left(history\right)\right)\right),c)\right)\right)\right)\right) \Rightarrow \operatorname{OriginalPresetFeasible}\left(2 \cdot m - 2, m, alphabet, f, d + 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_donor_preset_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The display uses k=2m-2 and the same flattenWords convention as the coding-prefix theorem. Proof arguments are omitted. OriginalPresetFeasible is the original global interface from `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction`. It quantifies one literal stream shared by both free scalar values and all archives, an own-archive stopping rule, lawful issued words under either original alphabet, free initial bottom, and correct bounded execution on every original complete-word history.

The coding marks are m-4-floor(t/2). The first literal bit is zero and clears every inherited legal tail. In the four suffix words the occupied position is at most m-3, so their final bit is zero. Use that final bit as the suffix mark. At the transition from coding to suffix, the last coding mark is at least one; this proves the same chronological seam inequality used for the whole coding prefix. All d+4 blocks therefore execute successfully on every live INITIAL record. No interior endpoint or reset is needed.

In the two even-index suffix coordinates the three lower donors have codes 10,11,01, and in the two odd-index coordinates the upper donors have the same codes. The other two coordinates are zero. These six nonzero suffix columns are distinct, whereas every non-donor has suffix 0000. Equal full columns involving a donor therefore identify its original phase. For two non-donors, the unchanged coding coordinates separate unequal original labels.

Each live source subtracts successive own scalar endpoints, starting from its own remembered free value. The scalar offset cancels. A classical decoder chooses a phase having that difference column; all such phases have the same table label. The finite words extend by fixed zero words to one infinite literal stream. Live sources stop after the d+4 displayed words and pay exactly d+4 complete-block fees. Initial bottom stops immediately with f(none). The paid trace law also counts a complete issued rejecting word when present, rather than only its accepted part.

The hypothesis is correctness of the supplied controller on the entire free-zero original-history fibre. It contains no assumed preset construction, suffix separation or safety property. The range 1<=d<=2m-10 is retained; the zero and one depth optimizations, uniform fallback at other horizons, minimum-cost attainment and the unconditional full-family price inequality are separate results.

**Definition 1.10 (Uniform finite horizon).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.uniformHorizon`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.uniformHorizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

uniformHorizon(m)=2m-4-min(2,m-5)=max(2m-6,m+1), for m>=5. It equals six at width five, seven at width six, and 2m-6 thereafter.

**Definition 1.11 (Strictly internal actual positions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.uniformOccupied`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.uniformOccupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put q=min(2,m-5). At issued index t the sole occupied bit is at i=m-2-q if 4<=t<4+q, and at i=1 otherwise. Every such bit is strictly internal. Both head and tail bits are zero.

**Theorem 1.12 (Full-family native uniform fallback).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall f \in \operatorname{Option}\left(\operatorname{LiveRecord}\left(2 \cdot m - 2\right)\right) \to Y,\; \forall table \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right) \to Y,\; \left(5 \le m \land \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall s \in \mathbb{N},\; s < 2 \cdot m - 2 \Rightarrow f\left(\operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = table\left(j\right)\right)\right) \Rightarrow \operatorname{OriginalPresetFeasible}\left(2 \cdot m - 2, m, alphabet, f, \operatorname{uniformHorizon}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_uniform_phase_preset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The display uses k=2m-2, arbitrary Y, and omits proof arguments. The schedule above is a literal word of length m at every issued index. Its charge tests the actual INITIAL edge {t*m+i,t*m+i+1} modulo 2m-1. At m>=7 the missing edge starts are {0,3,m-1,m,m+3}. Every other start has an explicitly constructed chronological index. The four neighboring edge tests imply that equal incidence columns have equal vertices. The width-five and width-six branches prove injectivity for the exact finite schedule by kernel decision and are consumed by the uniform proof.

The zero heads clear every legal inherited tail; the zero tails make successive seams safe. Native execution therefore produces the incidence column in each own endpoint-difference archive. A classical inverse identifies the INITIAL phase and returns its unchanged table label. The empty live column is an ordinary successful column, never bottom or rejection. One fixed stream serves both free values and all original histories under either original alphabet. Live executions pay exactly uniformHorizon(m) complete blocks; initial bottom stops freely. No construction or safety premise remains.

Incidence tests are the mature test-cover interpretation of this separator; see de Bontridder et al., Approximation algorithms for the test cover problem, Mathematical Programming 98, 477-491, Lemma 4.2, DOI 10.1007/s10107-003-0414-6. The Lean proof supplies its own actual calendar, separating columns and native execution bridge. No originality or finite numerical extrapolation is claimed.

**Definition 1.13 (One original global adaptive controller).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.OriginalAdaptiveFeasible`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.OriginalAdaptiveFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OriginalAdaptiveFeasible(k,m,hk,alphabet,f,d) means one legal Selector stops immediately on initial bottom with f(none), and its original execution succeeds within d issued complete words on every original history, using that history's own free endpoint. Both free-value fibres share this same selector. Rejection remains paid and absorbing.

**Definition 1.14 (Global adaptive minimum).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.GlobalAdaptivePrice`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.GlobalAdaptivePrice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GlobalAdaptivePrice is BudgetPrice of OriginalAdaptiveFeasible, the infimum of feasible natural budgets in extended naturals. It is infinity when no natural budget is feasible.

**Definition 1.15 (Global preset minimum).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.GlobalPresetPrice`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.GlobalPresetPrice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GlobalPresetPrice is BudgetPrice of the existing OriginalPresetFeasible interface. The stream is shared across both initial scalars and all running archives; stopping and decoding use each execution's own archive.

**Theorem 1.16 (Unconditional four-block paid-feedback bound).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall f \in \operatorname{Option}\left(\operatorname{LiveRecord}\left(2 \cdot m - 2\right)\right) \to Y,\; \forall table \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right) \to Y,\; \left(5 \le m \land \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall s \in \mathbb{N},\; s < 2 \cdot m - 2 \Rightarrow f\left(\operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = table\left(j\right)\right)\right) \Rightarrow \left(\left(\operatorname{GlobalAdaptivePrice}\left(2 \cdot m - 2, m, alphabet, f\right) \le \operatorname{GlobalPresetPrice}\left(2 \cdot m - 2, m, alphabet, f\right) \land \operatorname{GlobalPresetPrice}\left(2 \cdot m - 2, m, alphabet, f\right) \le \operatorname{GlobalAdaptivePrice}\left(2 \cdot m - 2, m, alphabet, f\right) + 4\right) \land \operatorname{GlobalAdaptivePrice}\left(2 \cdot m - 2, m, alphabet, f\right) + 4 < \infty\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_uniform_paid_feedback_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The display uses k=2m-2 and omits the positive-k proof argument. The arbitrary target has the same phase-label table for both free values and every legal tail; f(none) is arbitrary. The costs are true global original-history costs, not separately optimized fibre prices.

The uniform fallback supplies a finite preset budget. Preset inclusion supplies an adaptive budget. Well-ordering of the natural budgets attains each minimum, with its original one-selector or one-stream witness. A correct zero-budget controller forces a constant table. At depth one, a stopping root is constant; otherwise the root-zero charge forces a false first bit. This same issued word is safe for every inherited tail, and its own scalar difference decodes the common table for both free values.

For 1<=d<=2m-10 use the six-donor construction. Outside that range and with d>=2, uniformHorizon(m)<=d+4: width five uses six blocks, width six uses seven once d>=3, and m>=7 uses 2m-6 blocks once d>=2m-9. Budget extension preserves the exact returned fee through the native paid-trace equivalence. Applying this conversion to the attained adaptive minimum yields the upper inequality. Preset inclusion yields the lower inequality, and both attained natural minima prove finiteness. No attainment, separation, construction or safety hypothesis is left in the statement.

This result is the full same-table upper price bound. It does not assert a sharp lower gap, supremum equality, or the separate attainment claim in section 31.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.Donor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.GlobalAdaptivePrice`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.GlobalPresetPrice`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.OriginalAdaptiveFeasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.codingRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.conversionRows`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.correctedRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_donor_coding_archive`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_donor_preset_feasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_uniform_paid_feedback_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.original_uniform_phase_preset`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.outside`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.pairRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.suffixRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.uniformHorizon`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection.uniformOccupied`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FullPositiveWindowPrice](FullPositiveWindowPrice.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction](GlobalPresetObstruction.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges](OwnPathCharges.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction](GlobalPresetObstruction.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety](InternalZeroSafety.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges](OwnPathCharges.md)
