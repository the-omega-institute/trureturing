# Three-tree Paid Batch Phase

## Abstract

A once-paid fair-bit choice of a total tree controller has three exact batch phases.

The evaluated trees are the k=1 family from Scale36ActualEndpointAcquisition, ordered as P0, U1, V1. A Strategy is correct and finitely terminating on every finite labelled source tree, with no promise about prototype identity or size. A sampler chooses this complete strategy before any input arrives. The chosen strategy is shared by every counterfactual tuple and by all N runs, each run starting from an empty real-address cache. Internal computation and address length are unpriced; every consumed fair bit costs lambda and every distinct acquired address in a run costs one. The coarse class requires every emitted policy to factor through the merged-nonleaf history interface.

For a tape t and a tuple q in Fin(N)->Fin(3), paidTuple is lambda times the bit bill plus the sum of the N controller costs on the selected prototypes. G is the maximum over fixed tuples of the expected paidTuple. H takes this maximum separately on each tape before expectation. rawGamma and rawH take infima over all input-independent almost-surely stopping prefix samplers; coarseGamma and coarseH restrict to coarse samplers. Expectations and infima use nonnegative extended reals, so infinite expected bit costs remain included.

$$
(\forall N: \mathbb{N}, (\forall lambda: \mathbb{R}, \operatorname{sharp}\left(N, lambda\right) = \operatorname{min}\left(17 N, \operatorname{min}\left(\frac{67 N}{4} + \frac{3 lambda}{2}, \frac{50 N}{3} + \frac{8 lambda}{3}\right)\right)))
$$

**Theorem 1.1 (Restricting a recipe does not increase excess).**

$$(\forall m: \mathbb{N}, (\forall F: \operatorname{Fin}\left(m\right) \to Source, (\forall S: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), (\forall r: \operatorname{Recipe}\left(F, S\right), (\forall T: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), (\operatorname{Subset}\left(T, S\right) \to (\operatorname{Nonempty}\left(T\right) \to (\exists q: \operatorname{Recipe}\left(F, T\right), (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{Member}\left(i, T\right) \to \operatorname{gain}\left(q, i\right) \le \operatorname{gain}\left(r, i\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.restrict_recipe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing evaluated trees preserves a recipe for every nonempty subfamily with no larger individual excess. At a node that stops separating the restricted family, the common child replaces that node.

**Theorem 1.2 (There is at most one zero-excess member).**

$$(\forall m: \mathbb{N}, (\forall F: \operatorname{Fin}\left(m\right) \to Source, ((\forall i: \operatorname{Fin}\left(m\right), (\forall j: \operatorname{Fin}\left(m\right), \operatorname{Nonconflict}\left(\operatorname{F}\left(i\right), \operatorname{F}\left(j\right)\right))) \to (\forall S: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), (\forall r: \operatorname{Recipe}\left(F, S\right), (\forall i: \operatorname{Fin}\left(m\right), (\forall j: \operatorname{Fin}\left(m\right), ((\operatorname{Member}\left(i, S\right) \land \operatorname{Member}\left(j, S\right) \land \operatorname{gain}\left(r, i\right) = 0 \land \operatorname{gain}\left(r, j\right) = 0) \to i = j))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.zero_gain_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting to two zero-excess trees would contradict the root excess bound for a nonconflicting family.

**Theorem 1.3 (The selected controller is the emitted controller).**

$$(\forall s: \operatorname{PrefixSampler}\left(Strategy\right), (\forall t: Tape, (\forall p: Strategy, (\operatorname{Member}\left(t, \operatorname{emitted}\left(s, p\right)\right) \to \operatorname{selected}\left(s, t\right) = p))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.selected_emitted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Persistence makes distinct controller emission events disjoint, so selection agrees with every emitted controller.

**Theorem 1.4 (Exact values, thresholds, and attained infima).**

$$(\forall N: \mathbb{N}, (1 \le N \to (\forall lambda: \mathbb{R}, (0 < lambda \to (\operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\operatorname{sharp}\left(N, lambda\right)\right) \land \operatorname{coarseGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\operatorname{sharp}\left(N, lambda\right)\right) \land (\exists s: \operatorname{PrefixSampler}\left(Strategy\right), (\operatorname{Coarse}\left(s\right) \land \operatorname{G}\left(s, N, lambda\right) = \operatorname{ofReal}\left(\operatorname{sharp}\left(N, lambda\right)\right))) \land (N \le 6 lambda \to \operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(17 N\right)) \land (6 lambda \le N \to (N \le 14 lambda \to \operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\frac{67 N}{4} + \frac{3 lambda}{2}\right))) \land (14 lambda \le N \to \operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\frac{50 N}{3} + \frac{8 lambda}{3}\right)) \land \operatorname{rawH}\left(N, lambda\right) = \operatorname{ofReal}\left(17 N\right) \land \operatorname{coarseH}\left(N, lambda\right) = \operatorname{ofReal}\left(17 N\right) \land (\exists s: \operatorname{PrefixSampler}\left(Strategy\right), (\operatorname{Coarse}\left(s\right) \land \operatorname{H}\left(s, N, lambda\right) = \operatorname{ofReal}\left(17 N\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

For every N at least one and positive lambda, both interfaces have the displayed sharp value. The deterministic, biased, and uniform laws give its three lines, switching at N=6 lambda and N=14 lambda. The boundary formulas agree, and a coarse sampler attains each infimum. Taking the maximum before expectation instead has sharp attained value 17N.

Every controller dominates one profile with cost 16 at one prototype and 17 at the other two. Restricting a splitting recipe to a nonempty subset preserves an upper bound on its excess, and the existing root-excess theorem excludes two zero-excess members. Relabelling a sampled controller by its dominated profile preserves the full original bit bill. If p is the resulting common profile law and t its smallest coordinate, a constant input tuple gives cost at least N(17-t)+lambda L(p). The universal prefix-cylinder bound connects the actual bill to L(p); the existing Mersenne supporting lines give L(p)>=6t and L(p)>=14t-2.

The point law emits a coarse endpoint at the empty word and pays zero bits. A finite three-leaf code has probabilities 1/2,1/4,1/4 and expected length 3/2. A finite-state two-level repeating code gives equal probabilities 1/3 and expected length 8/3. Their stopping words are realized through the public fixed-label carry-tree contract. On every tape some prototype costs at least 17, while a point endpoint costs at most 17 on each prototype, which proves the value for H.

The dyadic random-bit cost is classical Knuth-Yao theory, as recalled in Lumbroso, Section 2.1. The complete tree-controller optimization and its raw and coarse batch comparison are repository results.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.restrict_recipe`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.selected_emitted`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase.zero_gain_unique`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxDyadicPrefixTail](WhiteboxDyadicPrefixTail.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition](../Scale36ActualEndpointAcquisition.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation](../Scale38NestedCompensation.md)
