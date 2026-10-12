# Five-tree Paid Batch Phase

## Abstract

A once-paid fair-bit choice of a total tree controller has three exact batch phases.

The evaluated trees are the k=2 family from Scale36ActualEndpointAcquisition, ordered as P0, U1, V1, U2, V2. A Strategy is correct and finitely terminating on every finite labelled source tree, with no promise about prototype identity or size. A sampler chooses this complete strategy before any input arrives. The chosen strategy is shared by every counterfactual tuple and by all N runs, each run starting from an empty real-address cache. Internal computation and address length are unpriced; every consumed fair bit costs lambda and every distinct acquired address in a run costs one. The coarse class requires every emitted policy to factor through the merged-nonleaf history interface.

For a tape t and a tuple q in Fin(N)->Fin(5), paidTuple is lambda times the bit bill plus the sum of the N controller costs on the selected prototypes. G is the maximum over fixed tuples of the expected paidTuple. H takes this maximum separately on each tape before expectation. rawGamma and rawH take infima over all input-independent almost-surely stopping prefix samplers; coarseGamma and coarseH restrict to coarse samplers. Expectations and infima use nonnegative extended reals, so infinite expected bit costs remain included.

$$
(\forall N: \mathbb{N}, (\forall lambda: \mathbb{R}, \operatorname{sharp}\left(N, lambda\right) = \operatorname{min}\left(22 N, \operatorname{min}\left(\frac{349 N}{16} + 3 lambda, \frac{109 N}{5} + \frac{18 lambda}{5}\right)\right)))
$$

**Definition 1.1 (Literal attaining codes).**

$$\operatorname{CodeClaim}\left(\right) = (\operatorname{rotateLabels}\left(\operatorname{stopping}\left(5, biasedFive, 1\right), rotate\right) = \operatorname{list}\left(\operatorname{emit}\left(\operatorname{word}\left(00\right), 0\right)\right) \land \operatorname{rotateLabels}\left(\operatorname{stopping}\left(5, biasedFive, 2\right), rotate\right) = \operatorname{list}\left(\operatorname{emit}\left(\operatorname{word}\left(010\right), 1\right), \operatorname{emit}\left(\operatorname{word}\left(011\right), 2\right), \operatorname{emit}\left(\operatorname{word}\left(100\right), 3\right), \operatorname{emit}\left(\operatorname{word}\left(101\right), 4\right)\right) \land \operatorname{rotateLabels}\left(\operatorname{stopping}\left(5, biasedFive, 3\right), rotate\right) = \operatorname{list}\left(\operatorname{emit}\left(\operatorname{word}\left(1100\right), 1\right), \operatorname{emit}\left(\operatorname{word}\left(1101\right), 2\right), \operatorname{emit}\left(\operatorname{word}\left(1110\right), 3\right), \operatorname{emit}\left(\operatorname{word}\left(1111\right), 4\right)\right) \land \operatorname{continuing}\left(5, biasedFive, 4\right) = [] \land \operatorname{stopping}\left(5, uniformFive, 2\right) = \operatorname{list}\left(\operatorname{emit}\left(\operatorname{word}\left(000\right), 0\right), \operatorname{emit}\left(\operatorname{word}\left(001\right), 1\right), \operatorname{emit}\left(\operatorname{word}\left(010\right), 2\right), \operatorname{emit}\left(\operatorname{word}\left(011\right), 3\right), \operatorname{emit}\left(\operatorname{word}\left(100\right), 4\right)\right) \land \operatorname{stopping}\left(5, uniformFive, 3\right) = \operatorname{list}\left(\operatorname{emit}\left(\operatorname{word}\left(1010\right), 0\right), \operatorname{emit}\left(\operatorname{word}\left(1011\right), 1\right), \operatorname{emit}\left(\operatorname{word}\left(1100\right), 2\right), \operatorname{emit}\left(\operatorname{word}\left(1101\right), 3\right), \operatorname{emit}\left(\operatorname{word}\left(1110\right), 4\right)\right) \land \operatorname{continuing}\left(5, uniformFive, 4\right) = \operatorname{list}\left(\operatorname{word}\left(1111\right)\right) \land (\forall d: \mathbb{N}, (\operatorname{state}\left(uniformFive, d + 4\right) = \operatorname{state}\left(uniformFive, d\right) \land \operatorname{action}\left(uniformFive, d + 4\right) = \operatorname{action}\left(uniformFive, d\right))) \land (\forall i: \operatorname{Fin}\left(5\right), \operatorname{law}\left(\operatorname{relabel}\left(rotate, \operatorname{fromPath}\left(5, biasedFive\right)\right), i\right) = \operatorname{if}\left(i = 0, \frac{1}{4}, \frac{3}{16}\right)) \land (\forall i: \operatorname{Fin}\left(5\right), \operatorname{law}\left(\operatorname{fromPath}\left(5, uniformFive\right), i\right) = \frac{1}{5}) \land \operatorname{E}\left(\operatorname{bill}\left(\operatorname{relabel}\left(rotate, \operatorname{fromPath}\left(5, biasedFive\right)\right)\right)\right) = \operatorname{ofReal}\left(3\right) \land \operatorname{E}\left(\operatorname{bill}\left(\operatorname{fromPath}\left(5, uniformFive\right)\right)\right) = \operatorname{ofReal}\left(\frac{18}{5}\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase.CodeClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stopping at depth d returns words of length d+1. The quarter code rotates the carry labels by one modulo five. The uniform path repeats both its state and its action every four depths. Expectations use the common fair-tape measure.

**Theorem 1.2 (Exact values, thresholds, and attained infima).**

$$(\operatorname{CodeClaim}\left(\right) \land (\forall N: \mathbb{N}, (1 \le N \to (\forall lambda: \mathbb{R}, (0 < lambda \to (\operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\operatorname{sharp}\left(N, lambda\right)\right) \land \operatorname{coarseGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\operatorname{sharp}\left(N, lambda\right)\right) \land (\exists s: \operatorname{PrefixSampler}\left(Strategy\right), (\operatorname{Coarse}\left(s\right) \land \operatorname{G}\left(s, N, lambda\right) = \operatorname{ofReal}\left(\operatorname{sharp}\left(N, lambda\right)\right))) \land (N \le 16 lambda \to \operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(22 N\right)) \land (16 lambda \le N \to (N \le 48 lambda \to \operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\frac{349 N}{16} + 3 lambda\right))) \land (48 lambda \le N \to \operatorname{rawGamma}\left(N, lambda\right) = \operatorname{ofReal}\left(\frac{109 N}{5} + \frac{18 lambda}{5}\right)) \land \operatorname{rawH}\left(N, lambda\right) = \operatorname{ofReal}\left(22 N\right) \land \operatorname{coarseH}\left(N, lambda\right) = \operatorname{ofReal}\left(22 N\right) \land (\exists s: \operatorname{PrefixSampler}\left(Strategy\right), (\operatorname{Coarse}\left(s\right) \land \operatorname{H}\left(s, N, lambda\right) = \operatorname{ofReal}\left(22 N\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

For every N at least one and positive lambda, both interfaces have the displayed sharp value. The deterministic, biased, and uniform laws give its three lines, switching at N=16 lambda and N=48 lambda. The boundary formulas agree, and a coarse sampler attains each infimum. Taking the maximum before expectation instead has sharp attained value 22N.

Every controller dominates one profile with cost 21 at one prototype and 22 at the other four. Restricting a splitting recipe to a nonempty subset preserves an upper bound on its excess, and the existing root-excess theorem excludes two zero-excess members. Relabelling a sampled controller by its dominated profile preserves the full original bit bill. If p is the resulting common profile law and t its smallest coordinate, a constant input tuple gives cost at least N(22-t)+lambda L(p). The universal prefix-cylinder bound connects the actual bill to L(p); the existing five-outcome supporting lines give L(p)>=16t and L(p)>=48t-6.

The point law emits a coarse endpoint at the empty word and pays zero bits. A finite five-result code emits 0 on 00, emits 1 through 4 on 010,011,100,101, and again emits 1 through 4 on 1100,1101,1110,1111. Its law is (1/4,3/16,3/16,3/16,3/16), with expected length 3. The uniform code emits 0 through 4 on 000,001,010,011,100 and on 1010,1011,1100,1101,1110, while 1111 repeats the four-level state. Each round assigns mass 3/16 to each result and repeats with mass 1/16. The resulting law is uniform and its expected length is 18/5. Its stopping words use the public fixed-label carry-tree contract. ActualJointResponseCostCore.result supplies a recipe and cost domination for the selected controller. Scale38NestedCompensation.root_excess on the whole prototype family gives a coordinate costing at least 22 on every tape. Repeating that coordinate in all N slots and dropping the nonnegative bit charge gives the H lower bound. Scale36ActualEndpointAcquisition.result supplies a coarse endpoint costing at most 22 on each prototype; its point sampler pays zero bits and attains the H value.

The dyadic random-bit cost is classical Knuth-Yao theory, as recalled in Lumbroso, Section 2.1. The complete tree-controller optimization and its raw and coarse batch comparison are repository results.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase.CodeClaim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxFiveBatchPhase.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Dyadic/WhiteboxThreeBatchPhase](WhiteboxThreeBatchPhase.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](../DyadicSupportLines.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines](../MersenneDyadicSupportLines.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition](../Scale36ActualEndpointAcquisition.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation](../Scale38NestedCompensation.md)
