# Fair-prefix Samplers and Dyadic Tail Costs

## Abstract

The same output law and the same fair-bit history determine a universal dyadic survival bound.

A prefix sampler observes only the first d fair bits. An emitted label persists at every larger depth, and almost every infinite tape emits a label at some finite depth. The emitted event is the union of its finite stopping cylinders. The active event at depth d consists of prefixes that still emit no label. The bill is the nonnegative extended-real sum of these active indicators; it counts the first stopping depth and is infinite on a tape that never stops.

Write p for the output law, R(p,d)=2^d-sum_i floor(2^d p(i)), and L(p)=sum_d R(p,d)/2^d. Each stopped output occupies an integer number of depth-d cylinders. Its cylinder count is at most floor(2^d p(i)), because every such cylinder lies in the eventual emitted event. The remaining cylinders are therefore at least R(p,d). This comparison uses the joint prefix execution and its eventual output law.

**Theorem 1.1 (Emission is measurable).**

$$(\forall A: Type, (\forall s: \operatorname{PrefixSampler}\left(A\right), (\forall i: A, \operatorname{MeasurableSet}\left(\operatorname{emitted}\left(s, i\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.emitted_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A countable union of finite unions of cylinders gives the emitted event.

**Theorem 1.2 (Distinct labels are disjoint).**

$$(\forall A: Type, (\forall s: \operatorname{PrefixSampler}\left(A\right), \operatorname{PairwiseDisjoint}\left(i \mapsto \operatorname{emitted}\left(s, i\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.emitted_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite emissions on one tape agree after both prefixes are extended to their common maximum depth.

**Theorem 1.3 (The common finite output law).**

$$(\forall m: \mathbb{N}, (\forall s: \operatorname{PrefixSampler}\left(\operatorname{Fin}\left(m\right)\right), ((\forall i: \operatorname{Fin}\left(m\right), 0 \le \operatorname{law}\left(s, i\right)) \land \sum_{i \in \operatorname{Fin}\left(m\right)}\operatorname{law}\left(s, i\right) = 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.law_simplex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Almost-sure termination and disjoint emission events make p a nonnegative probability vector.

**Theorem 1.4 (Every depth pays its dyadic residual).**

$$(\forall m: \mathbb{N}, (\forall s: \operatorname{PrefixSampler}\left(\operatorname{Fin}\left(m\right)\right), (\forall d: \mathbb{N}, \operatorname{ofReal}\left(\frac{\operatorname{R}\left(\operatorname{law}\left(s\right), d\right)}{2^{d}}\right) \le \operatorname{fairTape}\left(\operatorname{active}\left(s, d\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.cylinder_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

The floor bound on every stopped-label cylinder count leaves at least R(p,d) active cylinders, each of mass 2^(-d).

**Theorem 1.5 (The expected bit bill dominates the dyadic cost).**

$$(\forall m: \mathbb{N}, (\forall s: \operatorname{PrefixSampler}\left(\operatorname{Fin}\left(m\right)\right), (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(\operatorname{law}\left(s\right), d\right)}{2^{d}}\right) \to \operatorname{ofReal}\left(\operatorname{L}\left(\operatorname{law}\left(s\right)\right)\right) \le \operatorname{E}\left(\operatorname{bill}\left(s\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.ddg_lower` (`✓ std3`). ∎

*Citation.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

Tonelli identifies the expected bill with the sum of the survival probabilities. Termwise cylinder bounds give the cost inequality when the real dyadic series is summable. This is the classical optimal random-bit cost lower bound recalled in Lumbroso, Section 2.1, equations (1)-(2). Its formalization here connects PrefixSampler, emitted, active, and bill to that cost expression on the same execution and output law.

**Theorem 1.6 (Relabelling the emitted event).**

$$(\forall A: Type, (\forall B: Type, (\forall f: A \to B, (\forall s: \operatorname{PrefixSampler}\left(A\right), (\forall i: B, (\forall t: Tape, t \in \operatorname{emitted}\left(\operatorname{relabel}\left(f, s\right), i\right) \iff (\exists a: A, (t \in \operatorname{emitted}\left(s, a\right) \land \operatorname{f}\left(a\right) = i))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.relabel_emitted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A relabelled output occurs precisely when an original output occurs and maps to that label.

**Theorem 1.7 (Relabelling preserves every charged bit).**

$$(\forall A: Type, (\forall B: Type, (\forall f: A \to B, (\forall s: \operatorname{PrefixSampler}\left(A\right), \operatorname{bill}\left(\operatorname{relabel}\left(f, s\right)\right) = \operatorname{bill}\left(s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.relabel_bill` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping an emitted label preserves exactly the active prefixes, including every exceptional infinite path.

**Theorem 1.8 (A label permutation transports the law).**

$$(\forall m: \mathbb{N}, (\forall s: \operatorname{PrefixSampler}\left(\operatorname{Fin}\left(m\right)\right), (\forall e: \operatorname{Perm}\left(\operatorname{Fin}\left(m\right)\right), (\forall i: \operatorname{Fin}\left(m\right), \operatorname{law}\left(\operatorname{relabel}\left(e, s\right), i\right) = \operatorname{law}\left(s, \operatorname{inverse}\left(e, i\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.relabel_law_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The emission event for a permuted label equals the original event for its inverse image.

**Theorem 1.9 (The extended bit bill is measurable).**

$$(\forall A: Type, (\forall s: \operatorname{PrefixSampler}\left(A\right), \operatorname{Measurable}\left(\operatorname{bill}\left(s\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.bill_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bill is a countable nonnegative sum of measurable active indicators.

**Theorem 1.10 (The finite observer preserves expected code length).**

$$(\forall m: \mathbb{N}, (2 \le m \to (\forall g: Path, (\operatorname{IsRootPath}\left(m, g\right) \to \operatorname{E}\left(\operatorname{bill}\left(\operatorname{fromPath}\left(m, g\right)\right)\right) = \operatorname{ofReal}\left(\operatorname{pathCost}\left(g\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.path_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observer stops at the unique labelled leaf contained in its finite prefix. The public carry-tree stopping-word contract gives its first stopping length and almost-sure return, so its expected charge equals the path cost.

**Theorem 1.11 (The finite observer preserves the digit law).**

$$(\forall m: \mathbb{N}, (2 \le m \to (\forall g: Path, (\operatorname{IsRootPath}\left(m, g\right) \to (\forall i: \operatorname{Fin}\left(m\right), \operatorname{law}\left(\operatorname{fromPath}\left(m, g\right), i\right) = \operatorname{ofDigits}\left(\operatorname{labelDigit}\left(g, i\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.path_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observer emits i exactly on the public carry-tree event of a finite return with label i. Its probability is the fixed-label binary digit series.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.bill_measurable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.cylinder_tail_lower`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.ddg_lower`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.emitted_disjoint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.emitted_measurable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.law_simplex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.path_expectation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.path_law`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.relabel_bill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.relabel_emitted`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail.relabel_law_equiv`
- Dependency: [D5/S0/Naming/GreenClassMeasure](../../../../S0/Naming/GreenClassMeasure.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/CarryGraphRealization](../CarryGraphRealization.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines](../MersenneDyadicSupportLines.md)
