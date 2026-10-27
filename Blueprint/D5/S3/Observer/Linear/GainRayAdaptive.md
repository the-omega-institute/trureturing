# Sharp native adaptive gain-ray capacity

## Abstract

Sharp native adaptive gain-ray capacity

Fix d and a history length n at most d+1. Evaluation at the full set of original clocks 0 through d is a linear equivalence on the d+1 ordinary coefficients. The fiber coordinates are x,r,delta and the d+1-n remaining gain values at clocks n through d. Thus when n=d+1 there are exactly the three source-and-drift coordinates and no free gain coordinates.

The positive denominator is D=x+r. At a prefix clock i the prescribed numerator gain value is (y_i-delta)D when i is even and (y_i-delta)(1+xr) when i is odd. At each remaining clock it is D times the free gain value. Inverting full-clock evaluation gives the numerator coefficients B. The original whole gain has coefficients B/D, with arbitrary actual degree, signs and roots.

The polynomial substitution sends x,r to themselves, coefficients to B and drift to D delta. Every positive chart point is in its rational image: encode its coefficient vector divided by D and its drift divided by D. This proves nonzero pullback by polynomial identity on the positive x,r chart, rather than using ambient nullity as evidence about a prescribed fiber.

Currying the joint polynomial into fiber variables with polynomial history coefficients yields a nonzero coefficient q(y). If q(y) is nonzero, specialization to that exact history is a nonzero polynomial in the remaining fiber variables.

**Definition 1.1 (Full-clock interpolation equivalence).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.clockEquiv`

*Formalization.* `D5/S3/Observer/Linear/GainRayAdaptive.clockEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary coefficient vector and its values at clocks 0,...,d are linearly equivalent.

**Definition 1.2 (Original whole gain on a fiber).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiberBeta`

*Formalization.* `D5/S3/Observer/Linear/GainRayAdaptive.fiberBeta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator coefficients divided by the evaluated positive denominator x+r.

**Definition 1.3 (Legal compatible whole world).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiberWorld`

*Formalization.* `D5/S3/Observer/Linear/GainRayAdaptive.fiberWorld` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive x,r and a nonzero fiberBeta give the original legal source chart, whole gain and drift.

**Theorem 1.4 (Exact specialization at a prescribed history).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.eval_fiber_specialize`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.eval_fiber_specialize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating fiberSpecialize Q y at f equals evaluating Q at the joint coordinates (f,y).

**Theorem 1.5 (A nonzero coefficient separates exceptional histories).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_nonzero_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.fiber_nonzero_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero joint polynomial Q, some nonzero history polynomial q makes fiberSpecialize Q y nonzero whenever q(y) is nonzero.

**Theorem 1.6 (Nonempty legal fibers at every history).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_beta_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.fiber_beta_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1<=n<=d+1 and positive x,r, choosing a drift different from the initial history value makes the whole fiber gain nonzero. This gives a point in every compatible fiber.

**Theorem 1.7 (Literal pure-J prefix equality).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_world_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.fiber_world_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal fiber point and every i<n, the original read at clock i on J repeated n-1 times equals y_i. No reindexing or skipped observation is used.

**Theorem 1.8 (Coverage of every original chart world).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_coordinates_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.fiber_coordinates_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Encoding every positive-chart source, every whole coefficient vector and every drift reconstructs that same coefficient vector. The tail coordinates are its remaining fixed-clock gain values.

**Theorem 1.9 (Exact denominator-cleared substitution).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.eval_fiber_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.eval_fiber_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial pullback evaluates at the same x,r, numerator coefficient vector B and drift D delta.

**Theorem 1.10 (Dominance of actual history coordinates).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_pullback_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.fiber_pullback_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero chart polynomial p and n<=d+1, its polynomial pullback is nonzero. The proof uses rational coverage of the full positive chart, including n=d+1.

Let s be any countable set of word-matrix pairs, each containing M and taking at most 2(d+1) initial-inclusive reads. For each 1<=n<=d+1, short_history_completion constructs one nonzero history polynomial q_c for every pair c. The exceptional set E_n is the union of their zero sets. Every y outside E_n has one legal original world with exactly that pure-J prefix and no successful pair from s on its own word.

The mixed-word obstruction and the pure-M endpoint obstruction supply a nonzero chart wedge for every pair successful somewhere. A pair successful nowhere uses the constant polynomial one. Simultaneously scaling gain and drift by a nonzero number preserves success, so the denominator-cleared fiber substitution respects every successful world. Both positive and negative success scales remain admitted.

The full compatible fiber has x,r positive and a nonzero numerator coefficient vector. It is open. It is nonempty for every y: set x=r=1 and choose delta different from y_0. Countably many nonzero specialized polynomial zero sets cannot cover this nonempty open fiber. The proof applies the existing polynomial nullity theorem inside this prescribed fiber and positivity of volume on a nonempty open set. It assumes no regularity of a protocol, branch or selector.

**Definition 1.11 (Full legal compatible fiber).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.fiberDomain`

*Formalization.* `D5/S3/Observer/Linear/GainRayAdaptive.fiberDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source coordinates are positive and the whole numerator coefficient vector is nonzero. No individual coefficient or gain sample is constrained.

**Definition 1.12 (Countable algebraic exceptional histories).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.exceptionalHistories`

*Formalization.* `D5/S3/Observer/Linear/GainRayAdaptive.exceptionalHistories` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a countable index family q, this is the union of the zero sets of its history polynomials.

**Theorem 1.13 (Simultaneous avoidance in a nonempty open domain).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.countable_polynomial_avoidance`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.countable_polynomial_avoidance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any countable family of nonzero real polynomials on a finite-dimensional real coordinate space is simultaneously nonzero at some point of every nonempty open set.

**Theorem 1.14 (Full-world completion of each generic prescribed history).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.short_history_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.short_history_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1, every countable eligible family s and every 1<=n<=d+1, there is a nonzero polynomial q_c for each pair. Every y outside their zero-set union has an original World d whose n initial pure-J reads equal y and at which every pair in s fails. The n=d+1 case retains no free gain coordinates.

A Protocol fixes one countable palette of real matrices per word. Its deterministic decision function has the entire actual real history as input, and may select an action or stop with a palette member. No continuity, measurability, finite response alphabet or computability condition is imposed. Every action is one chronological M or J and has its immediate read; the initial identity read counts.

On the identical-row family, the pure-J history map H_n is the ordinary gain evaluation plus drift, independent of the row parameter. Its extension to the full coefficient-and-drift space is onto for n<=d+1. Therefore every nonzero exceptional-history polynomial has a nonzero polynomial pullback. The actual row worlds are selected afterwards in the open domain 0<theta<1 and beta nonzero.

Pairs whose words are pure J, including no actions, or have fewer than d+1 reads at and after their first M admit restricted polynomial success certificates. If their wedge polynomials were all zero, identical_row_annihilation would make their output zero on the entire row family. Together with the history pullbacks these certificates can be avoided simultaneously at one actual legal row world.

Follow the protocol on that world. A pure-J terminal word fails by its restricted certificate. If the first M is at clock n>d+1, the total bound 2(d+1) gives strictly fewer than d+1 suffix reads, so its restricted certificate applies. If the first M is at a clock 1<=n<=d+1, whole-world completion supplies another legal world with the same preceding pure-J history and with every eligible M-containing palette pair unsuccessful. Identical actual history forces the same preceding decisions and that next M. The uniform bound then supplies an actual terminal word containing this forced M, contradicting completion. Subsequent decisions need not match.

The upper protocol executes M exactly 2(d+1) times and then stops. At each word its palette is a fixed singleton. On the reached terminal word its matrix is exactBetaReadout d, which returns beta with scalar one on every original whole-polynomial world. It takes exactly 2d+3 original consecutive reads. The threshold concerns gain rays in this fixed-matrix output model; it makes no numerical stability or physical resource claim.

**Definition 1.15 (A preassigned singleton-palette protocol).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.upperProtocol`

*Formalization.* `D5/S3/Observer/Linear/GainRayAdaptive.upperProtocol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

It selects M before the intended terminal length and stops at that length with the preassigned matrix. All choices are independent of data.

**Theorem 1.16 (Exact attained native upper bound).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.upper_protocol_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.upper_protocol_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every declared degree and every World d, the actual protocol reaches M repeated 2(d+1) times, terminates there after exactly 2d+3 reads and returns its original coefficient vector.

**Theorem 1.17 (Uniform attainment on every original world).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

upperProtocol d is UniformlySuccessful with 2d+3 total reads. The output scale is one.

**Theorem 1.18 (Nonzero pullback by the actual pure-J history map).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.history_pullback_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.history_pullback_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n<=d+1, every nonzero polynomial in n history values remains nonzero after substitution of the original gain values plus drift. Surjectivity is proved on the full linear extension before restricting to legal row worlds.

**Theorem 1.19 (Arbitrary-history adaptive impossibility).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1 and every Protocol d, UniformlySuccessful P (2d+2) is false. Arbitrary actual-history actions, stops and palette selectors and countable preassigned fixed matrices remain in scope.

**Theorem 1.20 (Both halves of the sharp threshold).**

Lean statement: `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1, no native Protocol succeeds uniformly in at most 2d+2 reads, and a native Protocol succeeds uniformly in 2d+3 reads.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_lower`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_threshold`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.adaptive_upper`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.clockEquiv`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.countable_polynomial_avoidance`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.eval_fiber_pullback`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.eval_fiber_specialize`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.exceptionalHistories`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiberBeta`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiberDomain`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiberWorld`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_beta_nonzero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_coordinates_cover`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_nonzero_coefficient`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_pullback_nonzero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.fiber_world_prefix`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.history_pullback_nonzero`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.short_history_completion`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.upperProtocol`
- Truth anchor: `D5/S3/Observer/Linear/GainRayAdaptive.upper_protocol_correct`
- Dependency: [D5/S3/Observer/Linear/GainRayEndpoint](GainRayEndpoint.md)
- Dependency: [D5/S3/Observer/Linear/GainRayIdenticalRows](GainRayIdenticalRows.md)
- Dependency: [D5/S3/Observer/Linear/GainRayJets](GainRayJets.md)
- Dependency: [D5/S3/Observer/Linear/GainRayNuisance](GainRayNuisance.md)
