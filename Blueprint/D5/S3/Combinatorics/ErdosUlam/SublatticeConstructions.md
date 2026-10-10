# Diamonds and Boolean interval extensions

## Abstract

A rank arithmetic progression supplies a diamond, and a Boolean interval extends a monochromatic sublattice by every same-coloured prefix outside the interval.

Write P(r) for the initial segment of size r in Fin n, and R(n,g,t) for the number of ranks r between zero and n with g(r)=t. The rank colouring assigns g(|A|) to A. Every family of initial segments is closed under union and intersection.

**Definition 1.1 (Translation into a Boolean interval).**

$$\operatorname{intervalLift}\left(n, b, k, h, A\right) = \operatorname{union}\left(\operatorname{P}\left(b\right), \operatorname{image}\left(\operatorname{translation}\left(b\right), A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.intervalLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b+k≤n, translate every element of A by b and adjoin the initial segment P(b). The resulting set lies between P(b) and P(b+k), has size b+|A|, and the translation preserves both union and intersection.

**Theorem 1.2 (An additional diamond member).**

$$\forall n \in Nat,\; \forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall g \in Nat \to Bool,\; \forall t \in Bool,\; \left(a < b \land \left(b < c \land \left(c \le n \land \left(a + c = b + b \land \left(\operatorname{g}\left(a\right) = t \land \left(\operatorname{g}\left(b\right) = t \land \left(\operatorname{g}\left(c\right) = t \land \left(\forall r \in Nat,\; \left(a < r \land \left(r < c \land \operatorname{g}\left(r\right) = t\right)\right) \Rightarrow r = b\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists M \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{IsSublattice}\left(M\right) \land \left(\operatorname{Monochromatic}\left(\operatorname{rankColouring}\left(g\right), M\right) \land \operatorname{card}\left(\{r \in \operatorname{range}\left(n + 1\right) | \operatorname{g}\left(r\right) = t\}\right) + 1 \le \operatorname{card}\left(M\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.diamond_sublattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a<b<c≤n, a+c=2b, and the three ranks have colour t. They are consecutive occurrences of t: every rank strictly between a and c with colour t equals b. Start with all t-coloured initial segments and add X=P(a) union (P(c) minus P(b)). This set has size b and differs from P(b). Its intersection with P(b) is P(a), while their union is P(c). All remaining selected prefixes lie below P(a) or above P(c), so the enlarged family is a monochromatic sublattice with R(n,g,t)+1 members.

**Theorem 1.3 (Extension by exterior prefixes).**

$$\forall n \in Nat,\; \forall b \in Nat,\; \forall k \in Nat,\; \forall g \in Nat \to Bool,\; \forall t \in Bool,\; \forall L \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)\right),\; \left(b + k \le n \land \left(\operatorname{IsSublattice}\left(L\right) \land \left(\left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{member}\left(A, L\right) \Rightarrow \operatorname{g}\left(b + \operatorname{card}\left(A\right)\right) = t\right) \land \operatorname{card}\left(\{r \in \operatorname{range}\left(k + 1\right) | \operatorname{g}\left(b + r\right) = t\}\right) + 1 \le \operatorname{card}\left(L\right)\right)\right)\right) \Rightarrow \left(\exists M \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{IsSublattice}\left(M\right) \land \left(\operatorname{Monochromatic}\left(\operatorname{rankColouring}\left(g\right), M\right) \land \operatorname{card}\left(\{r \in \operatorname{range}\left(n + 1\right) | \operatorname{g}\left(r\right) = t\}\right) + 1 \le \operatorname{card}\left(M\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.interval_sublattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be a nonempty sublattice of the k-dimensional Boolean lattice whose members all have colour t under A↦g(b+|A|). Suppose it has at least one more member than the number of t-coloured ranks in the interval from b to b+k. Translate L into that interval and adjoin all t-coloured prefixes with ranks less than b or greater than b+k. Each exterior prefix is comparable with every translated member, so lattice closure is preserved. Translation is injective, and the two families are disjoint by cardinality. Their combined size is at least R(n,g,t)+1.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.diamond_sublattice`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.intervalLift`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.interval_sublattice`
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeDefs](SublatticeDefs.md)
