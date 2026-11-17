# Alternating Charges of Substitution Prefixes

## Abstract

Complete block charges control all prefixes of iterated substitutions and their intervals.

Let alpha be any alphabet, w an integer weight and f a list-valued substitution. No finiteness of the alphabet, nonerasing condition or parity hypothesis is imposed. image f j a is the actual jth iterate, with the zero iterate [a]. Alternation starts positively at the beginning of each list. A change of starting phase multiplies the charge by a power of -1 and therefore preserves its absolute value.

**Definition 1.1 (Local alternating charge).**

$$\forall alpha \in Type,\; \forall w \in alpha \to \mathbb{Z},\; \forall v \in List\left(alpha\right),\; charge\left(w, v\right) = alternatingSum\left(map\left(w, v\right)\right)$$

*Formalization.* `D5/S1/Words/SubstitutionPrefixEnvelope.charge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty charge is zero. For concatenation uv, the charge is Q(u)+(-1)^length(u) Q(v). Consequently its absolute value is at most |Q(u)|+|Q(v)|, regardless of whether either length is odd.

**Theorem 1.2 (The recursive prefix estimate).**

$$\forall alpha \in Type,\; \forall w \in alpha \to \mathbb{Z},\; \forall f \in alpha \to List\left(alpha\right),\; \forall M \in \mathbb{Z},\; \forall B \in \mathbb{N},\; \forall H \in \mathbb{N} \to \mathbb{Z},\; \left(0 \le M \land \left(\left(\forall a \in alpha,\; abs\left(w\left(a\right)\right) \le M\right) \land \left(\left(\forall a \in alpha,\; length\left(f\left(a\right)\right) \le B\right) \land \left(\left(\forall j \in \mathbb{N},\; 0 \le H\left(j\right)\right) \land \left(\forall j \in \mathbb{N},\; \forall a \in alpha,\; abs\left(charge\left(w, image\left(f, j, a\right)\right)\right) \le H\left(j\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall j \in \mathbb{N},\; \forall a \in alpha,\; \forall t \in \mathbb{N},\; abs\left(charge\left(w, take\left(t, image\left(f, j, a\right)\right)\right)\right) \le M + B \cdot sum\left(range\left(j\right), H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/SubstitutionPrefixEnvelope.prefix_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume M>=0, every |w(a)|<=M, length(f(a))<=B, every H(j)>=0 and every complete jth image has charge at most H(j) in absolute value. Then every take index t satisfies the displayed bound. Here sum(range(j),H) means the sum of H(i) over 0<=i<j. This includes t=0, whole prefixes, indices beyond the end and empty images. Locate the endpoint in the concatenation of level-j children using exists_flatMap_block. Before that endpoint are at most B complete children; the remaining child contributes its recursively controlled prefix. The base image is a singleton. This induction establishes prefix control from complete-block control at all levels.

**Theorem 1.3 (Intervals in two adjacent images).**

$$\forall alpha \in Type,\; \forall w \in alpha \to \mathbb{Z},\; \forall f \in alpha \to List\left(alpha\right),\; \forall M \in \mathbb{Z},\; \forall B \in \mathbb{N},\; \forall H \in \mathbb{N} \to \mathbb{Z},\; \left(0 \le M \land \left(\left(\forall a \in alpha,\; abs\left(w\left(a\right)\right) \le M\right) \land \left(\left(\forall a \in alpha,\; length\left(f\left(a\right)\right) \le B\right) \land \left(\left(\forall j \in \mathbb{N},\; 0 \le H\left(j\right)\right) \land \left(\forall j \in \mathbb{N},\; \forall a \in alpha,\; abs\left(charge\left(w, image\left(f, j, a\right)\right)\right) \le H\left(j\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall j \in \mathbb{N},\; \forall a \in alpha,\; \forall b \in alpha,\; \forall v \in List\left(alpha\right),\; infix\left(v, append\left(image\left(f, j, a\right), image\left(f, j, b\right)\right)\right) \Rightarrow abs\left(charge\left(w, v\right)\right) \le 4 \cdot \left(M + B \cdot sum\left(range\left(j\right), H\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/SubstitutionPrefixEnvelope.two_block_interval_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, every infix of the concatenation of any two jth images has charge at most four times the prefix envelope. Every prefix of this concatenation has charge at most twice the envelope. Subtracting the charge of the prefix preceding the interval, with its exact alternating phase, gives the interval bound. The letters may coincide and the interval may be empty. There is no asserted occurrence in any infinite word.

## References

- Truth anchor: `D5/S1/Words/SubstitutionPrefixEnvelope.charge`
- Truth anchor: `D5/S1/Words/SubstitutionPrefixEnvelope.prefix_envelope`
- Truth anchor: `D5/S1/Words/SubstitutionPrefixEnvelope.two_block_interval_bound`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](RankOneMorphismIterationBoundDefs.md)
