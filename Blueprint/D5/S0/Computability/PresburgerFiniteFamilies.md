# Finite Families of Integer Trace Relations

## Abstract

Finite dependent products and chart unions preserve polynomial finite trace bounds.

Let K and T be finite index types, X(k) arbitrary source carriers and Y(t) arbitrary descriptor carriers. For each k,t, the relation f(k,t) takes one source and one descriptor to Bool. The joint relation evaluates on the disjoint unions Sigma X and Sigma Y using their tags. A finite sample may repeat descriptor values and may use only some types. None of K, T, X(k), or Y(t) is required to be inhabited.

**Theorem 1.1 (Restriction to descriptor types gives a product upper bound).**

$$\operatorname{card}\left(\operatorname{Tr}\left(jointSample\right)\right) \le \operatorname{prod}\left(t, \operatorname{card}\left(\operatorname{Tr}\left(slice\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerFiniteFamilies.trace_card_dependent_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With one common source carrier X, put I(t)={i : sample(i).tag=t}. The descriptor at i transports along this equality into Y(t). Code each source by its tuple of Boolean restrictions to I(t). All restrictions belong to their respective trace families, using the same source. A decoder recovers every coordinate by taking t to be that coordinate's sample tag. The finite source-code bound applies, and the code type has the product of the component cardinalities. This bounds global patterns. It does not assert that arbitrary traces have a common source. Empty Y(t) requires no padding descriptor.

**Theorem 1.2 (A union of source charts has a sum upper bound).**

$$\operatorname{card}\left(\operatorname{Tr}\left(SigmaX\right)\right) \le \operatorname{sum}\left(k, \operatorname{card}\left(\operatorname{Tr}\left(Xk\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerFiniteFamilies.trace_card_chart_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every trace on the disjoint union of source charts has a source in one chart. It therefore lies in the union of that chart's trace family. The cardinality of a finite union is at most the sum of the cardinalities, even when different charts give the same trace. An empty chart index type gives an empty source union.

**Theorem 1.3 (One fixed positive polynomial bounds every finite sample).**

$$0<Ctotal \land \operatorname{card}\left(\operatorname{Tr}\left(jointSample\right)\right) \le Ctotal\cdot(n+1)^{stotal}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerFiniteFamilies.finite_family_polynomial_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Growth(f(k,t),C(k,t),s(k,t)) for every pair of tags. Define C_total=1+sum_k prod_t C(k,t) and s_total=sum_k sum_t s(k,t). For each chart the product bound uses card(I(t))<=n, multiplies coefficients, and adds exponents. The chart sum is bounded using each chart exponent's inequality with s_total and n+1>=1. Adding one to the coefficient makes it positive even when K is empty. These constants depend on the finite family, independently of the size, repetitions, or values of the finite sample.

**Theorem 1.4 (An explicit exponential value exceeds any natural polynomial budget).**

$$\exists n, C\cdot(n+1)^{s} < 2^{n}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerFiniteFamilies.finite_exponential_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural C,s, take k=C*(s+2)^s+1 and n=(s+1)*k. Then n+1<=(s+2)*k and C*(n+1)^s<=C*(s+2)^s*k^s <k^(s+1)<=(2^k)^(s+1)=2^n. The strict step uses C*(s+2)^s<k; the final bound uses Nat.lt_two_pow_self. The construction includes C=0 and s=0.

## References

- Truth anchor: `D5/S0/Computability/PresburgerFiniteFamilies.finite_exponential_domination`
- Truth anchor: `D5/S0/Computability/PresburgerFiniteFamilies.finite_family_polynomial_bound`
- Truth anchor: `D5/S0/Computability/PresburgerFiniteFamilies.trace_card_chart_sum`
- Truth anchor: `D5/S0/Computability/PresburgerFiniteFamilies.trace_card_dependent_product`
- Dependency: [D5/S0/Computability/PresburgerPatternGrowth](PresburgerPatternGrowth.md)
