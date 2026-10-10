# Near-critical INITIAL grid

## Abstract

Row and column labels on the original scalar reader's full joint INITIAL prior.

**Definition 1.1 (The physical grid phases).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridPhase`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r>=3, write n=2^r and take m>=n^2+2r, k=2m-2 and T=k+1=2m-1. A grid pair p,q in Fin n denotes the actual phase representative j=2r+pn+q modulo T. These representatives occupy exactly the interval from 2r through 2r+n^2-1, contained in the interior of the first m-bit window. Their two coordinates are unique. Coprimality gcd(m,T)=1 means every phase is actual; it supplies no phase observation to a controller.

**Definition 1.2 (A scalar row or column target).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.GridTarget`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.GridTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arbitrary injective labels:Fin n->Y supplies the live labels, with no finiteness assumption on the label universe Y. For both scalar values v in ZMod 2 and every inherited legal tail s<k, f(v,-gridPhase(p,q),s) equals labels(p) if v=0 and labels(q) otherwise. At every phase outside the grid it equals labels(0). The separately observed initial bottom has the unrestricted label f(bottom), which may equal a live label. The target depends on the immutable INITIAL record; the full prior includes all actual complete-block histories and rejected histories. A grid coordinate zero deliberately shares its scalar label with the outside code.

**Theorem 1.3 (Every common preset requires at least 4r-1 paid blocks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_grid_preset_lower`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_grid_preset_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=3, m>=(2^r)^2+2r, either original alphabet, arbitrary label universe Y, injective labels and every GridTarget f, any OriginalPresetFeasible controller with budget d satisfies 4r-1<=d. Its stream is common to all sources and both free-value fibres. Its stop function can depend on the remembered free output and its own entire acquired archive. The correctness premise quantifies every original history, all phases and inherited legal tails, early stops, rejecting attempts and charged waits.

At emitted index 2h the literal charge window is h through h+m; at index 2h+1 it is m+h through T-1 together with zero through h+1. For h<=2r-2 the latter misses the whole grid. The literal increment derivative therefore vanishes there for every word, independently of the word's legality or a chosen controller. These silent odd slots remain complete paid blocks.

The fixed stream defines an offline even-slot profile of length 2r-1 for each grid pair. Equality of profiles gives equality of all scheduled increments below any budget d<=4r-2. For each fixed free value separately, induction transports that equality into equality of the two sources' actual ownCharge arrays. The induction retains the same current scalar, tail and own archive and uses the archive length as the absolute scheduled index. A successful word produces equal next endpoints and equal next archive lengths. An early stop or common rejection retires both arrays and pads them with zero. No unused scheduled coordinate is treated as an acquired endpoint, and arrays at different free values are never equated.

The existing arbitrary-depth charge_separates theorem then forces equal INITIAL labels within each free-value fibre. Actual-history realization and native_fiber supply the required successful executions at every grid pair with tail zero; correctness remains required on the full prior. Applying separation at free value zero identifies the row, and applying it at free value one identifies the column. Injective labels make the one common profile injective on Fin n times Fin n. This injects n^2=2^(2r) pairs into only 2^(2r-1) profiles, a contradiction. The argument uses each source's own executed history and does not construct a controller with access to another source's archive.

This is a repository-derived consequence of original literal execution, physical charge derivatives, common-tail acquisition and finite injection counting. The result is restricted to this near-critical tail-independent row/column family. It makes no external priority claim and does not classify arbitrary tables, other widths or the all-parameter acquisition objective.

**Theorem 1.4 (Paid feedback still needs r informative slots).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_grid_adaptive_lower`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_grid_adaptive_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=3, m>=(2^r)^2+2r, either original alphabet, arbitrary injective labels into Y and any GridTarget f, OriginalAdaptiveFeasible at budget d implies 2r-1<=d. Select actual tail-zero, value-zero histories at phases gridPhase(p,0), one for every p in Fin(2^r). These are witnesses against a controller correct on the entire prior. The existing compress theorem turns any such original selector into a binary protocol with exactly count(2,0,d)=(d+1)/2 potentially informative endpoints. All odd-index increments below the excluded horizon are zero for every literal word; common rejection and early stopping retire a branch. Distinct labels force exact identification of all 2^r rows. The existing exact_identification_card_le_pow bound excludes d<=2r-2. No restriction on paid-feedback action selection, rejecting attempts or waits is introduced.

**Definition 1.5 (A coordinate's little-endian bits).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.coordinateBit`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.coordinateBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coordinateBit(p,a) is the ZMod 2 scalar corresponding to bit a of the pinned BitVec.equivFin inverse of p in Fin(2^r). The bit index a lies in Fin r.

**Definition 1.6 (Exact phase supports at even indices).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At paid index 2h, gridRow(r,h,side,a,i) sums the selected coordinate bit over grid pairs with h+i=2r+pn+q. side=false selects p, and side=true selects q. Uniqueness of the pair makes this a zero/one charge indicator. For h<=2r-1 its first and last vertices are zero, and its complete m+1-vertex sum is zero: summing over the unused coordinate repeats every bit n=2^r times, which is zero in ZMod 2.

**Definition 1.7 (Coding rows and paid silent slots).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridRows`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A schedule of R coding supports, R<=2r, yields 2R-1 rows. At even paid index 2h it uses gridRow for schedule(h); at odd paid indices it uses the zero row. The zero row's prefix word is the literal all-zero m-bit wait. It costs one issued block.

**Definition 1.8 (Physical literal inversion).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridWords`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed word list applies the existing prefixWord inverse to each gridRows entry. Its bit i is the prefix parity of the phase row through i. The short_window_charge_inverse theorem gives exactly the prescribed full charge row, zero first bit and zero last bit. Every word is admitted by either original alphabet because m<k.

**Definition 1.9 (Reconstruction from the own archive).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridDecode`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a map position:Fin r->Fin R selecting the desired coding slots, gridDecode reads only endpointDifferences from the saved free scalar and the supplied archive's own endpoints. It extracts the differences at paid indices 2*position(a), reconstructs a little-endian BitVec from those r Boolean values, applies the pinned BitVec.equivFin and returns the corresponding label. On the grid this is the selected row or column; off-grid all bits are zero, so the result is labels(0).

**Definition 1.10 (Select the scalar coordinate freely).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveSchedule`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remembered INITIAL value zero selects the r row supports in bit order; value one selects the r column supports. Every later literal action is fixed by this initial selection.

**Definition 1.11 (Rows followed by columns).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonSchedule`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common schedule has 2r supports: the r row bits followed by the r column bits. Each is issued at its even paid index, separated by a charged zero wait.

**Definition 1.12 (Select an acquired component).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonPosition`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonPosition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remembered value zero selects coding positions zero through r-1; value one selects r through 2r-1. Both sets belong to that source's actual common-stream archive.

**Definition 1.13 (The 2r-1-block attaining prefix).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveWords`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is gridWords with R=r and the free-value-selected adaptiveSchedule. It contains r coding blocks and r-1 zero waits, all starting and ending zero.

**Definition 1.14 (The 4r-1-block attaining prefix).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonWords`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is gridWords with R=2r and commonSchedule. It contains 2r coding blocks and 2r-1 zero waits, all starting and ending zero.

**Definition 1.15 (Complete words at acquired indices).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.scriptStreams`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.scriptStreams` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each selected finite word list defines a stream by its own issued archive index, followed by literal zero words beyond the list. No source is charged for an unissued suffix.

**Definition 1.16 (Free bottom and final endpoint stops).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.scriptStop`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.scriptStop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Initial bottom returns its unrestricted bottom label immediately. A live source issues the prescribed words until the list ends, then returns decode(saved value,own archive). The stop function receives no INITIAL clock, length, phase or another source's archive.

**Definition 1.17 (Final scalar-coordinate decoding).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveStop`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveStop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After the selected 2r-1-word prefix, the stop returns gridDecode with identity coding positions. Initial bottom stops without issuing a word.

**Definition 1.18 (Final component of the common archive).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonStop`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonStop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After the 4r-1-word prefix, the stop returns gridDecode at commonPosition determined by the remembered free value. Initial bottom stops freely.

**Definition 1.19 (One stream selected by the free reading).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveSelector`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveSelector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the existing selectedSelector applied to adaptiveWords and adaptiveStop. Subsequent paid values affect the returned label but do not choose later actions.

**Definition 1.20 (One literal stream on both fibres).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonStream`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonStream` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same commonWords prefix and subsequent zero words serve both INITIAL scalar values and all running own archives.

**Definition 1.21 (Actual full-word trace fees).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.fee`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.fee` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fee(D,q) is D for a live INITIAL record and zero for initial bottom. In the grid law it equals the length of an actual stopped PaidTrace, rather than a scheduled suffix charge.

**Theorem 1.22 (Exact full-original near-critical grid law).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_near_critical_grid_law`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_near_critical_grid_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every label type Y in an arbitrary universe, r>=3, m>=(2^r)^2+2r, either original alphabet, any injective labels:Fin(2^r)->Y and every GridTarget f on optional LiveRecord(2m-2), the full original GlobalAdaptivePrice is 2r-1 and GlobalPresetPrice is 4r-1. The theorem supplies OriginalAdaptiveFeasible and OriginalPresetFeasible at these respective budgets, and OriginalSelectedPresetFeasible at 2r-1. The independently observed initial-bottom label f(bottom) is arbitrary and may coincide with any live label.

For every actual complete-block history, let q be its immutable OriginalRecord and free its sole free INITIAL reading. There is an actual own PaidTrace of adaptiveSelector returning f(q), with exactly fee(2r-1,q) issued words and m*fee(2r-1,q) emitted bits; there is an actual own PaidTrace of the common presetSelector returning f(q), with exactly fee(4r-1,q) issued words and m*fee(4r-1,q) emitted bits. Neither issued archive contains a bottom endpoint. These assertions include all legal inherited tails, phases and values, and all histories already rejected before INITIAL. The latter stop immediately and have empty paid archives. Every live source issues the whole displayed attaining prefix.

Safety comes from actual_shared_charge_suffix on the original literal interface. Every coding word and wait starts and ends zero. The root zero clears even the maximal inherited tail k-1 within that paid root; subsequent zero seams and short internal runs prevent rejection. The actual literal increments match the full grid support at every phase, not just at witnesses used for the lower bounds. The script_readings and charge_differences results identify only the endpoints that this source acquires. Pinned BitVec bit reconstruction yields p or q on the grid and zero off it, including grid sources whose selected coordinate is zero.

The existing original_final_script and trace_congr results give the actual prescribed complete-word trace and transport its own archive to each original history. execute_paid_trace and archive_length establish the paid word count and exactly m emitted bits per issued word. The existing price_exact theorem combines the two universal lower bounds with these attainments. For each free value v the theorem also supplies an actual AllowedBlock history whose INITIAL record is (v,-gridPhase(0,0),0), and that history's own adaptive and common-preset traces emit exactly m*(2r-1) and m*(4r-1) bits. Thus both complete-word worst fees are attained on actual sources; no scheduled but unissued suffix is counted.

The adaptive attainment selects a literal stream only from the free INITIAL value. The lower bounds allow arbitrary paid-feedback-dependent actions and own-archive stopping, so the price gap establishes no advantage specifically attributable to subsequent paid feedback. This repository-derived synthesis uses the existing native execution, acquisition, physical inverse, compression, own-charge separation, trace and finite-information results. It prices this universal near-critical tail-independent row/column family; it does not settle arbitrary tables, all k and m, or the broader acquisition objective, and makes no external novelty-priority claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.GridTarget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveSchedule`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveSelector`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveStop`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.adaptiveWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonPosition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonSchedule`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonStop`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonStream`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.commonWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.coordinateBit`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.fee`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridDecode`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridPhase`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridRows`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.gridWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_grid_adaptive_lower`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_grid_preset_lower`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.original_near_critical_grid_law`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.scriptStop`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid.scriptStreams`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection](DonorCorrection.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FourLabelPaidFeedback](FourLabelPaidFeedback.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression](OriginalCommonTailCompression.md)
