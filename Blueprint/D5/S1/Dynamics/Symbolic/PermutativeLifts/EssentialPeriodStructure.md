# Essential periods from actual colored skeletons

## Abstract

Essential periods from actual colored skeletons.

**Definition 1.1 (CoordinatePeriodic).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.CoordinatePeriodic`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.CoordinatePeriodic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary alphabet and a two-sided point x, site i is p-periodic exactly when x(i+kp)=x(i) for every signed integer k. The predicate itself permits period zero; positivity is imposed separately in essential periods and period structures.

**Definition 1.2 (sites).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.sites`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.sites` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual period-p skeleton mask is the set of all signed coordinates satisfying the full coordinate periodicity condition. It is not a finite sampled approximation.

**Definition 1.3 (color).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The colored period-p skeleton has the actual letter x(i) at every periodic site and a hole, represented by none, everywhere else. Keeping the letters as well as the mask is necessary for essential-period extraction.

**Theorem 1.4 (coordinate periodic of dvd).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_of_dvd`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_of_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If p divides q, every actual p-periodic coordinate is q-periodic. The integer multiplier in q is absorbed into the signed multiple already quantified in the coordinate condition.

**Theorem 1.5 (coordinate periodic translate).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_translate`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A p-periodic site remains p-periodic after translation by any signed multiple of p. The translated site carries the same actual letter.

**Theorem 1.6 (coordinate periodic translate iff).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_translate_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_translate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by a signed multiple of p preserves and reflects membership in the actual p-skeleton, using both positive and negative translations.

**Theorem 1.7 (color eq some iff).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_eq_some_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_eq_some_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A colored skeleton takes value some a at a coordinate exactly when that coordinate is periodic and its actual letter equals a. This bridge exposes both the mask and the letter content.

**Theorem 1.8 (value eq of color period).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.value_eq_of_color_period`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.value_eq_of_color_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A global signed period q of a colored p-skeleton preserves the actual letters along every q-translate of each p-periodic coordinate. The global colored equality is iterated in both signed directions.

**Theorem 1.9 (coordinate translate of super color period).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_translate_of_super_color_period`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_translate_of_super_color_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When p divides r, a period q of the colored r-skeleton translates every p-periodic site to another p-periodic site. The proof compares actual letters at all p-translates using the larger skeleton; mask nesting alone is insufficient.

**Theorem 1.10 (color periodic of dvd).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_periodic_of_dvd`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_periodic_of_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When p divides r, every global signed period of the colored r-skeleton is also a period of the colored p-skeleton. Both membership and its complement are preserved, and actual letters agree on the mask.

**Theorem 1.11 (iterate unit shift).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.iterate_unit_shift`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.iterate_unit_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n-th iterate of the actual unit shift on a two-sided point is the actual shift by the natural integer n. This connects Mathlib dynamical minimal periods to the concrete signed-coordinate convention.

**Theorem 1.12 (isPeriodicPt unit shift iff).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.isPeriodicPt_unit_shift_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.isPeriodicPt_unit_shift_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n-periodic-point condition under the unit shift is equivalent to ordinary additive periodicity by the integer n. The equivalence respects the actual FullShift action convention.

**Theorem 1.13 (color self periodic).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_self_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_self_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual colored p-skeleton is globally p-periodic, including its holes. Periodicity of each occupied coordinate preserves its letter, while signed translation preserves the skeleton mask.

**Definition 1.14 (leastPeriod).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extracted period is Mathlib minimalPeriod for the colored p-skeleton under the unit shift. It depends on the full colored skeleton, not only on a mask or on a word presentation.

**Theorem 1.15 (leastPeriod pos).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_pos`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive original skeleton period gives a positive extracted minimal period. This follows from the actual periodic-point bridge and Mathlib positivity of minimal periods.

**Theorem 1.16 (leastPeriod dvd).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_dvd`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extracted colored-skeleton minimal period divides the original natural skeleton period. The original colored skeleton is itself globally periodic, so Mathlib minimal-period divisibility applies.

**Theorem 1.17 (color leastPeriod periodic).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_leastPeriod_periodic`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_leastPeriod_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual colored p-skeleton is globally periodic by its extracted minimal natural period. This is an actual coordinate-period statement derived from the dynamical minimal-period API.

**Theorem 1.18 (sites leastPeriod eq).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.sites_leastPeriod_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.sites_leastPeriod_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Passing from p to its colored-skeleton minimal period preserves the entire actual periodic-coordinate set. Divisibility gives one inclusion, while preservation of actual letters under the colored minimal period gives the converse.

**Theorem 1.19 (color leastPeriod eq).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_leastPeriod_eq`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_leastPeriod_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Passing to the extracted minimal period preserves the whole colored skeleton, including actual letters and holes at every signed coordinate. This is stronger than an equality of uncolored masks.

**Definition 1.20 (EssentialPeriod).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.EssentialPeriod`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.EssentialPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source essential period is positive, has a nonempty actual periodic skeleton, and equals the least global period of that colored skeleton. Nonemptiness excludes the initially empty skeleton of a nonconstant point.

**Theorem 1.21 (leastPeriod essential).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_essential`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_essential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive period with nonempty actual skeleton supplies an essential period after least-period extraction. The skeleton and its colors are unchanged; no essentiality hypothesis on the original period is inserted.

**Theorem 1.22 (leastPeriod dvd of dvd).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_dvd_of_dvd`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_dvd_of_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nested original periods give extracted colored-skeleton periods that divide one another. A period of the larger colored skeleton is transported to the smaller colored skeleton and Mathlib minimal-period divisibility is reused.

**Theorem 1.23 (leastPeriods dvd of le).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_dvd_of_le`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_dvd_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a scale in which each period divides the next, extracted least periods at any two ordered levels retain divisibility. This is finite induction over levels, preserving the actual colored-skeleton notion.

**Theorem 1.24 (leastPeriods monotone).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_monotone`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The extracted least-period sequence is monotone for any positive divisibility scale. Each positive later extracted period is a multiple of the preceding one, so divisibility implies numerical order.

**Theorem 1.25 (leastPeriods unbounded).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_unbounded`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an aperiodic two-sided point whose positive skeleton scale covers every coordinate, the extracted least periods are unbounded. If bounded by K, every positive extracted period divides K factorial, and coordinate coverage would make that positive factorial a global shift period.

**Definition 1.26 (PeriodStructure).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.PeriodStructure`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.PeriodStructure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The primary-source period structure consists of strictly increasing positive essential periods, divisibility of each period into the next, and coverage of every signed coordinate by the actual skeletons. Essentiality includes a nonempty skeleton and the colored minimal-period equality.

**Definition 1.27 (PeriodStructure skeletonDensity).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.skeletonDensity`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.skeletonDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Along a genuine period structure of a binary point, the normalized skeleton density is the actual periodic phase count divided by its positive essential period. Positivity is supplied by the structure, not by an extra caller assumption.

**Theorem 1.28 (exists period structure).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.exists_period_structure`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.exists_period_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any aperiodic point with a positive, nonempty, nested and covering skeleton scale admits a genuine source period structure. Least-period extraction preserves colors and divisibility; aperiodicity forces unboundedness; Mathlib supplies a strictly increasing cofinal index subsequence, removing repeated extracted periods. Every source clause is proved, while the hypotheses on the initial scale remain explicit. Public escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; a successful mathematical build does not constitute declared_validated registration evidence.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.CoordinatePeriodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.EssentialPeriod`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.PeriodStructure`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_eq_some_iff`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_leastPeriod_eq`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_leastPeriod_periodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_periodic_of_dvd`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.color_self_periodic`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_of_dvd`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_translate`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_periodic_translate_iff`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.coordinate_translate_of_super_color_period`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.exists_period_structure`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.isPeriodicPt_unit_shift_iff`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.iterate_unit_shift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_dvd`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_dvd_of_dvd`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_essential`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriod_pos`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_dvd_of_le`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_monotone`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.leastPeriods_unbounded`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.sites`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.sites_leastPeriod_eq`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.skeletonDensity`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure.value_eq_of_color_period`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity](PeriodicSkeletonDensity.md)
