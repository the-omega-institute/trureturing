# The same literal Robin interpolation attains its minimum

## Abstract

The same literal Robin interpolation attains its minimum

The exponent domain is the closed orthant a_p>=1 in the finite real Pi-space S->R. extend a equals a on S and one outside S. Every objective occurrence is the exact imported phi S (extend a); no surrogate objective or second infimum is defined. eulerNormalization is sum_S log(1-p^(-1)), the normalization already in the actual Euler factors. This finite chart is essential: natural-indexed representatives have arbitrary invisible coordinates outside S. The value of the minimum and its sign are separate questions.

The actual upstream benefit derivative is reused directly from ContinuousPrimeMaximum. Log arguments remain positive because theta>1 gives L>1 and log L>0 on the actual orthant. Each benefit is at most -log(1-p^(-1)), giving Phi>=EulerGamma+log(log L)+eulerNormalization. Thus Phi<=M forces L<=H_M=exp(exp(M-EulerGamma-eulerNormalization)) and 1<=a_p<=H_M/log p. Since log p>=log 2>=1/2, norm(a)<=2H_M on that sublevel, an explicit coercive bound. The orthant and each literal sublevel are closed. A closed bounded sublevel is compact in this finite-dimensional real Pi-space. The all-ones sublevel is nonempty; the extreme-value theorem gives a global minimum there, and all points outside have greater objective. Existence therefore precedes the KKT argument. The original realInfimum is identified using exactly its unchanged realValues image set.

Supplier audit: Real.log_pos is applied to the actual clock>1 before ContinuousOn.log and each log_le_iff_le_exp; clock positivity alone is not treated as log positivity. Finset.sum_coe_sort converts the original supported sums to finite coordinates. IsClosed.isClosed_le consumes closedness of the orthant and continuity within that orthant. IsCompact.of_isClosed_subset places the literal sublevel in a compact finite-Pi closed ball. IsCompact.exists_isMinOn receives a nonempty sublevel and continuity restricted to it. Finally csInf_le and le_csInf use explicit bounded-below and membership witnesses for the original realValues. These image-set witnesses retain the constant-one admissible vector.

**Theorem 1.1 (Finite coordinates are preserved exactly).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.extend_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.extend_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extension agrees with every supported coordinate. This is a consumed coordinate-chart identity, not a new objective.

**Theorem 1.2 (The chart preserves the original domain).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.extend_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.extend_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite orthant vector extends to an admissible original vector. This consumed helper supplies the consumed theta_le_clock_of_naturalSupport helper and the original image-set witness.

**Theorem 1.3 (The original clock in finite coordinates).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.clock_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.clock_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported clock equals sum_(p:S) a_p log p. Finset.sum_coe_sort is reused exactly. The identity is consumed by continuity, coordinate differentiation and the scalar fixed-point bridge.

**Theorem 1.4 (The exact objective in finite coordinates).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported Phi equals EulerGamma+log(log(sum_(p:S) a_p log p))-sum_(p:S) benefit(p,a_p). This consumed identity is used by the literal coordinate derivative, with no change to benefits or normalization.

**Theorem 1.5 (No original objective value is lost).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x:N->R, extending its restriction to S leaves phi S x unchanged. Hence the finite chart retains the complete original realValues set, including every admissible real vector.

**Theorem 1.6 (Continuity on the actual closed orthant).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_continuousOn`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_continuousOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite clock is continuous, its two logarithms have positive arguments because theta>1, and the actual benefit is continuous by its upstream derivative. This proves ContinuousOn of the literal Phi, rather than of an auxiliary bound.

**Theorem 1.7 (A growing lower bound for the literal Phi).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.coercive_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.coercive_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the orthant, EulerGamma+log(log L)+eulerNormalization<=Phi. Only the total benefits are bounded; the exact terminal cost remains free to grow.

**Theorem 1.8 (Every sublevel has an explicit double-exponential box).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.sublevel_box`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.sublevel_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi<=M implies L<=H_M and every 1<=a_p<=H_M/log p. The proof pays positivity of L, log L and every support weight before exponentiating or dividing.

**Theorem 1.9 (Concrete coercivity in the finite-Pi norm).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_coercive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real M, outside radius 2H_M within the orthant the actual Phi is strictly greater than M. The proof uses the actual coordinate masses and the pinned logarithm lower bound, not an assumed norm-equivalence or coercivity premise.

**Theorem 1.10 (Compact literal sublevels).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.compact_sublevel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.compact_sublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orthant is an intersection of closed coordinate halfspaces. ContinuousOn and IsClosed.isClosed_le give closed sublevels; phi_coercive puts each inside a compact finite-dimensional closed ball. Empty sublevels are allowed.

**Theorem 1.11 (A genuine global minimizer exists).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.minimum_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.minimum_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compact sublevel through the all-ones vector is nonempty. IsCompact.exists_isMinOn supplies a minimizer; comparison with the sublevel threshold extends it to the whole unbounded orthant. No stationarity or optimizer existence hypothesis is used.

**Theorem 1.12 (Equality with the unchanged upstream infimum).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.infimum_of_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.infimum_of_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine minimizer bounds every value in the original realValues image, because phi_restrict covers every old representative. Its own value belongs to that image. Conditional infimum inequalities then give realInfimum S=phi S (extend a).

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.clock_coordinates`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.coercive_lower`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.compact_sublevel`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.extend_admissible`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.extend_apply`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.infimum_of_minimum`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.minimum_attained`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_coercive`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_continuousOn`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_coordinates`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.phi_restrict`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.sublevel_box`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/OwnClockContraction](OwnClockContraction.md)
