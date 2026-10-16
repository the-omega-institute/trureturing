# Measurable Random Control and Actual Complete Records

## Abstract

Joint probability laws for arbitrary independent measurable rank-one controls.

**Theorem 1.1 (The arbitrary-control complete-record supremum).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall U:\operatorname{WaitFamily}(n),\operatorname{UnitarySemigroup}(U)\Rightarrow \forall X,Y:\operatorname{Density}(n),\operatorname{iSup}(R:\operatorname{Control}(\operatorname{unitaryMenu}(U)),\operatorname{measurableTotalVariation}(\operatorname{jointLaw}(\operatorname{unitaryMenu}(U),R,X),\operatorname{jointLaw}(\operatorname{unitaryMenu}(U),R,Y)))=\operatorname{ENNRealOfReal}(\operatorname{FirstReadTVSup}(U,X,Y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/MeasurableRankOneControl.arbitrary_protocol_tv_supremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input domain is all complex positive semidefinite trace-one matrices on an arbitrary finite index type. WaitFamily(n) denotes maps from nonnegative real times to complex n-by-n matrices. UnitarySemigroup(U) means U(0) is the identity, U(t+u) equals U(u) U(t), and U(t)-adjoint times U(t) is the identity for every pair of nonnegative times. unitaryMenu(U) uses these three proofs. The iSup notation binds R over Control of that menu, at any fixed seed universe; ENNRealOfReal is ENNReal.ofReal applied to the real first-read supremum.

A seed is sampled from an arbitrary probability space with one input-independent law. For each seed it selects an actual finite Stop/wait/complete-rank-one-read feedback tree. Tree sizes need not be uniformly bounded; waiting times range over all nonnegative reals.

A terminal record is coded by its finite list of read outcomes. Structural induction proves that this code is injective for each fixed tree. Together with the retained seed, the code determines the original dependent record and all its control decisions and waits. Stop before any read is the empty list. Zero-probability branches remain present and require no conditional-probability division.

For each density and tree, the common record measure is the finite sum of Dirac masses at these codes, weighted by the actual ludersLaw. The original law_nonnegative, law_mass and luders_law_eq establish nonnegativity, normalization and the operational correspondence. Every code outside the selected tree has zero mass.

A measurable random control requires the mass of every fixed outcome word to be a measurable function of the seed, for every input density. This is a condition for the protocol to define a probability law. It is necessary for a measurable record kernel, and is sufficient because finite-alphabet words form a countable discrete space: every event mass is the countable sum of its singleton masses. Neither the seed law nor the selected strategy can depend on the unknown input.

The recordKernel is constructed from these actual finite measures. Its rows are probability measures, hence it is a Markov kernel. jointLaw is Mathlib's compProd of the seed probability law and that kernel; normalization follows from the existing Markov compProd probability instance. Its measurable-event probability is the integral of the actual finite record masses whose codes lie in the corresponding seed section. This establishes a joint measure, including events that depend on both the seed and the record.

Kernel measurability makes every real event-section probability measurable, and normalization bounds it between zero and one. It is therefore integrable on the seed probability space. The existing arbitrary_random_control_event_bound applies to these section events. Taking the measurable-event supremum gives the upper TV bound. Injective coding preserves the finite complete-record TV. Constant strategies on a one-point probability space then recover the deterministic actual_protocol_tv_supremum, giving the reverse bound and the stated equality.

A common measurable coarse output is a measurable map of the joint seed-and-record space, used identically for both input laws. The existing measurable_total_variation_map_le applies directly, so forgetting the seed, discarding outcomes, or retaining any measurable function of the complete record cannot increase total variation. This consequence introduces no additional mathematical declaration.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/MeasurableRankOneControl.arbitrary_protocol_tv_supremum`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](../../Estimation/DataProcessing/MeasurablePostprocessingDefectContraction.md)
- Dependency: [D5/S3/Quantum/Fibers/RankOneFeedbackProtocol](RankOneFeedbackProtocol.md)
