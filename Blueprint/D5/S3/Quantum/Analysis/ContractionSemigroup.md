# Strong Contraction Semigroups and Their Generators

## Abstract

General real strong contraction semigroups have dense generator domains, closed generator graphs and uniqueness from the full generator.

**Definition 1.1 (The actual real semigroup).**

Lean statement: `D5/S3/Quantum/Analysis/ContractionSemigroup.StronglyContinuousContractionSemigroup`

*Formalization.* `D5/S3/Quantum/Analysis/ContractionSemigroup.StronglyContinuousContractionSemigroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let E be any real normed space. A StronglyContinuousContractionSemigroup consists of a bounded real linear operator S(t) for every nonnegative real time t, with S(0) the identity, S(s+t)=S(s) composed with S(t), operator norm at most one and continuity of every orbit t maps to S(t)x. No Hilbert structure, finite dimension, separability or physical oscillator is assumed.

**Definition 1.2 (The domain selected by the actual right limit).**

Lean statement: `D5/S3/Quantum/Analysis/ContractionSemigroup.generatorDomain`

*Formalization.* `D5/S3/Quantum/Analysis/ContractionSemigroup.generatorDomain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same arbitrary real normed space and semigroup S, the generator domain is the real submodule of all vectors f for which t inverse times (S(t)f-f) has a strong limit as positive nonnegative-real times t tend to zero. The limit is unique and the actual linear generator on this domain is defined by that limit. The domain is not assumed to be the whole space.

**Theorem 1.3 (Right increments of any differentiable vector-valued function).**

Lean statement: `D5/S3/Quantum/Analysis/ContractionSemigroup.tendsto_slope_add_of_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContractionSemigroup.tendsto_slope_add_of_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real normed space E, every function F from the reals to E, every vector Fprime and every real a, assume HasDerivAt F Fprime a. Then h inverse times (F(a+h)-F(a)), indexed by nonnegative reals h tending to zero from above, tends strongly to Fprime. Completeness and a semigroup are unnecessary for this statement. Its proof transports the actual punctured real slope limit along a+h. The value of the inverse at h=0 is irrelevant to this right-neighborhood limit.

**Theorem 1.4 (The generator domain is dense in every real Banach space).**

Lean statement: `D5/S3/Quantum/Analysis/ContractionSemigroup.dense_generatorDomain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContractionSemigroup.dense_generatorDomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume in addition that E is complete. For every strongly continuous contraction semigroup S on E, each vector's orbit integral from zero to t lies in the actual generator domain. The positive-time averages converge to that vector, so the generator domain is dense. The integral is the Bochner interval integral of the continuous orbit.

**Theorem 1.5 (Passing to limits in the full generator graph).**

Lean statement: `D5/S3/Quantum/Analysis/ContractionSemigroup.tendsto_differenceQuotient_of_tendsto_generator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContractionSemigroup.tendsto_differenceQuotient_of_tendsto_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any complete real normed space, S any strongly continuous contraction semigroup on E, I any index type and l any nontrivial filter on I. For any family u from I into the actual generator domain and any ambient vectors f and g, assume the underlying vectors u(i) tend along l to f and S.generator(u(i)) tends along l to g. Then the full right difference quotients of f tend to g. In particular f belongs to the actual generator domain and its generator is g.

The fundamental identity S(t)f-f equals the orbit integral of the generator on domain vectors. Contractivity makes the orbit integral continuous in its vector. Passing both graph coordinates to their limits preserves this identity; the time-average limit then recovers the derivative. No coordinate description, preselected eigenbasis or assertion only on a smaller core substitutes for the full graph limits.

**Theorem 1.6 (The full generator determines the semigroup).**

Lean statement: `D5/S3/Quantum/Analysis/ContractionSemigroup.ext_of_generator`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ContractionSemigroup.ext_of_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete real normed space E and every pair S,T of strongly continuous contraction semigroups on E, assume their actual generator domains are equal. For every ambient vector f and every pair of proofs that f belongs to these two domains, assume the two actual generators agree at f. Then S=T as semigroup structures, hence all their operators agree at every nonnegative real time on every vector.

The proof compares the transfer orbit S(t-s)T(s)f on common domain vectors and shows its right derivative vanishes. Continuity and the right-derivative uniqueness argument make this orbit constant; density of the generator domain then extends equality to every vector.

These are Scott Armstrong's selected MarkovProcess proofs at immutable revision dbade0d12c4f84179441a9df7d7147df7a8bcaa0, from Semigroup/Basic, StrongOperatorLimit, Generator, OrbitContinuity, GeneratorClosed and GeneratorUniqueness. Their original public MarkovProcess.Semigroup namespaces are retained. The scalar slope helper is public at its original statement so both the physical and arbitrary-basis applications directly reuse one proof. No mathematical originality is claimed for this source selection.

The donor and receiver use Lean v4.33.0 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Scott Armstrong's 2026 copyright and Apache-2.0 attribution remain in the Lean source; the full license is docs/reports/heat-suppliers/markovprocess-LICENSE.txt. The immutable upstream tree has no NOTICE file. Replace the selection when equivalent declarations at the receiver's actually adopted Mathlib revision validate the real consumers. This module imports Mathlib without a physical-Hermite dependency. Its abstract conclusions alone assert neither self-adjointness nor quantum-state energy bounds nor Gibbs trace summability.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/ContractionSemigroup.StronglyContinuousContractionSemigroup`
- Truth anchor: `D5/S3/Quantum/Analysis/ContractionSemigroup.dense_generatorDomain`
- Truth anchor: `D5/S3/Quantum/Analysis/ContractionSemigroup.ext_of_generator`
- Truth anchor: `D5/S3/Quantum/Analysis/ContractionSemigroup.generatorDomain`
- Truth anchor: `D5/S3/Quantum/Analysis/ContractionSemigroup.tendsto_differenceQuotient_of_tendsto_generator`
- Truth anchor: `D5/S3/Quantum/Analysis/ContractionSemigroup.tendsto_slope_add_of_hasDerivAt`
