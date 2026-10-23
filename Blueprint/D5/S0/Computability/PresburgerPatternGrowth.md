# Finite Traces of Separated Integer Atoms

## Abstract

Separated integer thresholds and fixed-modulus atoms have polynomial finite trace growth.

For an arbitrary source carrier X and a finite index carrier I of size n, Tr(f) is the finite set of Boolean functions p on I for which one source x satisfies f(x,i)=p(i) at every index. A sample map I to Y may repeat descriptor values. Neither X nor the map into its numeric coordinates is assumed finite, definable, injective, or inhabited.

**Theorem 1.1 (A trace is realized by one common source).**

$$p in \operatorname{Tr}\left(f\right) \iff \exists x, \operatorname{f}\left(x\right)=p$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.mem_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership in Tr(f) means that one source x realizes the entire Boolean pattern p. Equality of functions enforces every sample coordinate at once. The finite index type may be empty; the source carrier need not have an inhabitant. This equivalence supplies witnesses for the finite-code and dependent-family counting arguments.

**Theorem 1.2 (A finite source code bounds the number of traces).**

$$\operatorname{card}\left(\operatorname{Tr}\left(f\right)\right) \le \operatorname{card}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.trace_card_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose K is finite and every source pattern factors as f(x)=decode(code(x)) for maps code:X to K and decode:K to Bool^I. Every witnessed trace then lies in the image of decode on K. The finite image bound gives at most card(K) traces. The source carrier may be infinite or empty, and code need not be injective or surjective. Residue codes and tuples of descriptor-type restrictions are two applications.

**Theorem 1.3 (Threshold patterns are counted by their number of true coordinates).**

$$\operatorname{card}\left(\operatorname{Tr}\left(\operatorname{threshold}\left(A, B\right)\right)\right) \le n+1$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.trace_card_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The threshold is A(x) <= B(i), with arbitrary integer functions A and B. For any two sources the corresponding truth sets are nested, by total order of their A values. Equal cardinalities force equal nested finsets, using Finset.eq_of_subset_of_card_le. Cardinality therefore injects the realized patterns into the n+1 possible integers from zero through n. This is the substantive counting step; ties, constant functions, and the empty sample remain covered.

**Theorem 1.4 (Divisibility patterns factor through a finite source residue).**

$$\operatorname{card}\left(\operatorname{Tr}\left(\operatorname{dvd}\left(d, A, B\right)\right)\right) \le d$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.trace_card_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed positive natural modulus d, the atom is d divides A(x)+B(i). The source code is the nonnegative integer remainder A(x) modulo d, viewed as Fin d. Existing integer remainder identities and the Finset image cardinality bound supply at most d patterns, independently of the number and values of sample coordinates.

**Theorem 1.5 (Negated divisibility has the same fixed-modulus bound).**

$$\operatorname{card}\left(\operatorname{Tr}\left(\operatorname{ndvd}\left(d, A, B\right)\right)\right) \le d$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.trace_card_ndvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The atom is the negation of d divides A(x)+B(i), still with d positive. Apply Boolean negation to each divisibility pattern. The unary image bound cannot increase its cardinality.

**Theorem 1.6 (A unary Boolean operation does not increase trace count).**

$$\operatorname{card}\left(\operatorname{Tr}\left(\operatorname{unary}\left(u, f\right)\right)\right) \le \operatorname{card}\left(\operatorname{Tr}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.trace_card_unary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every realized unary pattern is the image of the input pattern witnessed by the same source. Finset.card_image_le gives the bound for any Bool to Bool operation, including negation.

**Theorem 1.7 (A binary Boolean operation has a product upper bound).**

$$\operatorname{card}\left(\operatorname{Tr}\left(\operatorname{binary}\left(v, f, g\right)\right)\right) \le \operatorname{card}\left(\operatorname{Tr}\left(f\right)\right)\cdot\operatorname{card}\left(\operatorname{Tr}\left(g\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.trace_card_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Bool to Bool to Bool operation, each realized output uses one pair of input traces. Its image lies in the image of their Cartesian product, so Finset.card_image2_le gives the product bound. The source witness is shared in the actual output trace; forgetting compatibility enlarges only the upper-bound family. There is no assertion that every pair is jointly attainable. Intersection and union are immediate choices of the operation.

**Theorem 1.8 (Finite Boolean compositions have a fixed positive polynomial budget).**

$$\operatorname{Growth}\left(f, C, s\right) \Rightarrow 0<C \land \forall I, y:I\to Y, \operatorname{card}\left(\operatorname{Tr}\left(\operatorname{sample}\left(f, y\right)\right)\right) \le C\cdot(n+1)^{s}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerPatternGrowth.polynomial_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Matthias Aschenbrenner, Alf Dolich, Deirdre Haskell, Dugald Macpherson, Sergei Starchenko (2011). *Vapnik-Chervonenkis density in some theories without the independence property, I*. URL: <https://arxiv.org/abs/1109.5438v1>.

*Commentary.*

Growth(f,C,s) is an exact semantic derivation from constants, separated thresholds, and fixed positive-modulus divisibility or its negation, closed under arbitrary unary and binary Boolean operations. It does not assume a trace bound. Constants have budget (1,0), thresholds (1,1), and modulus-d atoms (d,0). Unary operations preserve the budget; binary operations multiply coefficients and add exponents. Induction proves positivity of C and the uniform C*(n+1)^s bound for every finite sample map.

The hypotheses concern separated integer atoms and their finite Boolean compositions. They do not impose any bound on the source values or on the samples, and do not assert that a quantified formula has such a derivation. The finite trace viewpoint is consistent with the literature context of Aschenbrenner, Dolich, Haskell, Macpherson, and Starchenko, arXiv:1109.5438.

## References

- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.mem_traces`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.polynomial_trace_bound`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.trace_card_binary`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.trace_card_dvd`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.trace_card_factor`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.trace_card_ndvd`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.trace_card_threshold`
- Truth anchor: `D5/S0/Computability/PresburgerPatternGrowth.trace_card_unary`
