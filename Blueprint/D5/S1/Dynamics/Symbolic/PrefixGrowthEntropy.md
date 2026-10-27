# Prefix Growth and Symbolic Entropy

## Abstract

Actual prefix counts have a real logarithmic growth limit equal to the covering entropy of any nonempty forward-invariant symbolic set.

Let A be a finite alphabet with discrete uniformity and let S be a nonempty subset of the one-sided full shift A^N. The map T is SymbolicDynamics.FullShift.shift(1): T(x)(j)=x(1+j). Forward invariance means T(S) is contained in S. No closedness, compactness of S, surjectivity, shadowing property or graph presentation is assumed. This is the classical word-growth formula for symbolic entropy; the contribution here is the formal bridge to Mathlib's covering entropy, without a literature novelty claim.

**Definition 1.1 (Count realized prefixes).**

$$\begin{aligned}\forall A: Type,\\\forall S: \operatorname{Set}(\mathbb{N} \to A),\\\forall n: \mathbb{N},\\\operatorname{prefixCount}(S, n) = \operatorname{Nat.card}(\operatorname{Set.range}((x: S \mapsto (i: \operatorname{Fin}(n) \mapsto \operatorname{x}(\operatorname{Fin.val}(i))))))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy.prefixCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

prefixCount(S,n) is Nat.card of the range of x in S mapped to the function i in Fin(n) ↦ x(i.val). It counts prefixes actually realized by elements of S. The empty prefix has one realization class because S is nonempty. Finite alphabet cardinality gives prefixCount(S,n) at most card(A)^n, and forward invariance lets a realized prefix of length m+n split into realized prefixes of lengths m and n.

**Theorem 1.2 (The real growth limit computes covering entropy).**

$$\begin{aligned}\forall A: Type,\\{}[\operatorname{Fintype}(A)] [\operatorname{UniformSpace}(A)] [\operatorname{DiscreteUniformity}(A)],\\\forall S: \operatorname{Set}(\mathbb{N} \to A),\\\operatorname{Nonempty}(S) \land \operatorname{MapsTo}(\operatorname{FullShift.shift}(1), S, S) \Rightarrow\\\exists h: \mathbb{R},\\0 \le h \land h \le \operatorname{Real.log}(\operatorname{Fintype.card}(A)) \land\\\operatorname{Tendsto}((n: \mathbb{N} \mapsto \operatorname{Real.log}(\operatorname{prefixCount}(S, n): \mathbb{R})/n), atTop, \operatorname{nhds}(h)) \land\\\operatorname{coverEntropy}(\operatorname{FullShift.shift}(1), S) = \operatorname{coeEReal}(h)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy.prefix_growth_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rate prefixLogRate(S)(n) is Real.log(prefixCount(S,n))/n; its value at n=0 uses Lean's real division convention. The theorem gives an actual real limit h with 0≤h≤log(card A), and identifies Mathlib Dynamics.coverEntropy(T,S) with h embedded into EReal.

For the entourage U_k of agreement on the first k coordinates, k,n>0, the dynamical entourage over times 0 through n-1 is exactly agreement on n+k-1 coordinates. Its minimum covering cardinality is exactly prefixCount(S,n+k-1). One actual representative per realized prefix supplies a cover. Conversely any ambient center can cover at most one realized prefix class, so choosing a covering center for each class is injective. Mathlib allows centers in the ambient full shift; the lower bound accounts for this convention.

Splitting prefixes proves submultiplicativity of their counts. Taking logarithms and applying Mathlib's Subadditive.tendsto_lim yields the real limit. Adding a fixed prefix width preserves the logarithmic rate. The prefix agreement entourages belong to and are cofinal in the product uniformity, so their common exponential covering growth is the full covering entropy. The proof reuses D5.S1.Dynamics.Shadowing.MetricTracing.shift_one_iterate_apply and Mathlib's dynamical covers, uniformity, exponential growth and Fekete lemma.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy.prefixCount`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy.prefix_growth_entropy`
- Dependency: [D5/S1/Dynamics/Shadowing/MetricTracing](../Shadowing/MetricTracing.md)
