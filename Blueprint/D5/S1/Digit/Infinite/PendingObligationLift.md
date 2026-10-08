# Transported exclusions and exact finite observations

## Abstract

Transported exclusions and exact finite observations.

**Definition 1.1 (Outstanding endpoint equalities).**

Lean statement: `D5/S1/Digit/Infinite/PendingObligationLift.pending`

*Formalization.* `D5/S1/Digit/Infinite/PendingObligationLift.pending` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let F_j be inverse branch maps, P_j the current pieces, I_j the guard intervals, and Z_j the forbidden points at the successive observation times. Start with S_0 empty. Insert Z_j intersect P_j into S_j, apply F_j to the union, and intersect the image with I_(j+1). Thus only equalities still possible at the next actual guard remain outstanding.

**Theorem 1.2 (Historical avoidance and actual finite records).**

Lean statement: `D5/S1/Digit/Infinite/PendingObligationLift.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/PendingObligationLift.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, every sequence of real maps F_j injective for j<n, and every single trajectory x_(j+1)=F_j(x_j) with x_j in P_j for j<n and in I_j for j<=n, the terminal value x_n avoids S_n if and only if x_j avoids Z_j at every j<n. The assertion includes n=0. A threshold discarded outside a later guard cannot equal that trajectory's later coordinate.

For any actual source whose first n scalar coordinates lie in the prescribed pieces and closed expanded cells, and whose coordinates through n lie in the guard sets, the same terminal avoidance condition is equivalent to the existence of an infinite supported target stream realizing those n colors within budget. This statement also covers the empty prefix; all later errors are zero.

Fix any nonnegative real budget b and any map Q from real targets to six colors. Take a closed observed graph path with color word r and source word w, and append one lawful source edge l from its last vertex v to u. Choose any actual legal terminal address y satisfying the guard of u with kappa(y) in its piece. There exists an actual source x realizing the whole closed path, reading l after w, and equal to y after exactly three times (length(w)+1) deleted bits. The source is eventually zero if and only if that chosen terminal address is eventually zero.

Use the successive graph pieces and guard intervals, the actual inverse branches of x, and Z_j=E_(r_j) minus O_(r_j), where E_i is the closed expanded cell and O_i is the actual attainable closed-budget relation. Then kappa(y) avoids S_(length(w)+1) exactly when a single infinite target stream realizes every specified color, stays in the support, and differs from that same actual source by at most b at every time. After the prescribed prefix the target equals the source scalar, so all subsequent errors are zero.

There are length(r)=length(w)+1 observed departure coordinates and the same number of source edges including l. The chosen terminal coordinate is unobserved. Each component may use its own terminal address, pieces, guard intervals, and outstanding set while sharing the color word.

## References

- Truth anchor: `D5/S1/Digit/Infinite/PendingObligationLift.pending`
- Truth anchor: `D5/S1/Digit/Infinite/PendingObligationLift.result`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth](ClosedObservationCommonTailWidth.md)
- Dependency: [D5/S1/Digit/Infinite/FixedTailClosedBudget](FixedTailClosedBudget.md)
- Dependency: [D5/S1/Digit/Infinite/LateLabelStateBound](LateLabelStateBound.md)
