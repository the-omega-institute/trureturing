# The Birkhoff order on convex subhyperlattices need not be a lattice

## Abstract

A five-element strong join hyperlattice has two convex subhyperlattices without a greatest lower bound in Birkhoff order.

**Definition 1.1 (Extension to two sets).**

$$w \in \operatorname{hyperExtend}(j,A,B) \iff \exists (x \in A), \exists (y \in B), w \in \operatorname{j}(x,y)$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.hyperExtend` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

For a hyperoperation j on a carrier, the result on two sets A and B is the union of j(x,y) over all x in A and y in B.

**Definition 1.2 (Strong join hyperlattices).**

Lean statement: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.StrongJoinHyperlattice`

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.StrongJoinHyperlattice` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

The carrier is nonempty. The meet is a binary operation and the hyperjoin assigns a nonempty subset to every pair. The meet is idempotent, associative and commutative. Each diagonal hyperjoin contains its input. The hyperjoin is commutative and associative with the extension to sets, interpreting an element argument as its singleton.

The first absorption law places x in the pointwise meet image of the singleton of x and the hyperjoin of x and y. The second places x in the hyperjoin of x and the meet of x and y. The strong axiom requires the meet of x and y to equal x whenever y belongs to their hyperjoin.

**Definition 1.3 (The induced order).**

$$x \leq y \iff H.\operatorname{meet}(x,y)=x$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.meetOrder` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

Reflexivity, transitivity and antisymmetry follow from the three meet laws. Equivalently, y belongs to the hyperjoin of x and y. Strongness gives one implication. Meet commutativity, hyperjoin absorption and hyperjoin commutativity give the other.

**Definition 1.4 (Convex subhyperlattices).**

$$\operatorname{CS}(H) = \{S:\operatorname{Set}(\alpha) \mid S.Nonempty \land (\forall (x \in S), \forall (y \in S), H.\operatorname{meet}(x,y) \in S \land H.\operatorname{hjoin}(x,y) \subseteq S) \land S.OrdConnected\}$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.CS` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

The subtype uses the induced order in OrdConnected. When two elements belong to S, their meet and every value of their hyperjoin belong to S. OrdConnected includes every element between two members of S.

**Definition 1.5 (The two Birkhoff clauses).**

$$\operatorname{birkhoffLE}(H,A,B) \iff \operatorname{IsCofinalFor}(A.val,B.val) \land \operatorname{IsCoinitialFor}(B.val,A.val)$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.birkhoffLE` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

A and B denote the underlying sets of the two convex subhyperlattices. Every member of A is below some member of B, and every member of B is above some member of A. Both comparisons use the induced order.

**Definition 1.6 (The Birkhoff partial order).**

$$A \leq B \iff \operatorname{birkhoffLE}(H,A,B)$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.birkhoffOrder` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

The two clauses compose to give transitivity. If both comparisons hold, each element of either set lies between two elements of the other set. Order convexity then gives equality of the sets.

**Definition 1.7 (The conjecture at an arbitrary carrier universe).**

$$\forall (\alpha:\operatorname{Type}_{u}), \forall (H:\operatorname{StrongJoinHyperlattice}(\alpha)), \forall (X,Y:\operatorname{CS}(H)), (\exists (M:\operatorname{CS}(H)), \operatorname{IsGLB}(\{X,Y\},M)) \land (\exists (J:\operatorname{CS}(H)), \operatorname{IsLUB}(\{X,Y\},J))$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.claimAt` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

For each carrier and each strong join hyperlattice structure on it, use birkhoffOrder H as the local order on CS H. IsGLB and IsLUB require respectively a greatest common lower bound and a least common upper bound among all convex subhyperlattices. Both must exist for every pair.

**Definition 1.8 (The conjecture for carriers in Type 0).**

$$\forall (\alpha:\operatorname{Type}_{0}), \forall (H:\operatorname{StrongJoinHyperlattice}(\alpha)), \forall (X,Y:\operatorname{CS}(H)), (\exists (M:\operatorname{CS}(H)), \operatorname{IsGLB}(\{X,Y\},M)) \land (\exists (J:\operatorname{CS}(H)), \operatorname{IsLUB}(\{X,Y\},J))$$

*Formalization.* `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.claim` (`✓ std3`).

*Citation.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

This is claimAt at universe zero. It includes all finite carriers and all infinite carriers in Type 0.

**Theorem 1.9 (The universal conjecture is false).**

$$\neg (\forall (\alpha:\operatorname{Type}_{0}), \forall (H:\operatorname{StrongJoinHyperlattice}(\alpha)), \forall (X,Y:\operatorname{CS}(H)), (\exists (M:\operatorname{CS}(H)), \operatorname{IsGLB}(\{X,Y\},M)) \land (\exists (J:\operatorname{CS}(H)), \operatorname{IsLUB}(\{X,Y\},J)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N Aishwarya Nayak, Bhargava K, Pallavi Panjarike, Kuncham Syam Prasad, Tapatee Sahoo, Harikrishnan Panackal (2026). *On the structural aspects of Convex Subhyperlattices under different orders*. DOI: [10.48550/arXiv.2611.10526](https://doi.org/10.48550/arXiv.2611.10526). URL: <https://arxiv.org/abs/2611.10526v1>.

*Commentary.*

Adjoin a new top t to the Boolean square with bottom 0, incomparable atoms a and b, and top c. Use ordinary meet. For inputs x and y, the hyperjoin contains their ordinary join s and contains t additionally exactly when s equals c and x and y differ. The ordinary join of a triple always occurs in either association. An additional t occurs precisely when the total ordinary join equals c and at least one input differs from c. The usual lattice absorptions and the fact that every hyperjoin output is above its inputs give the absorption and strongness laws.

The singleton of c and the whole carrier have the two atom intervals from 0 to a and from 0 to b as common lower bounds. Any greatest lower bound must contain 0 by comparison with the whole carrier. Domination of the intervals provides an element above each atom. Convexity with 0 puts a and b in the bound, and hyperjoin closure puts t there. Comparison with the singleton would require t to be below c. The same countermodel lifts to every carrier universe.

## References

- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.CS`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.StrongJoinHyperlattice`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.birkhoffLE`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.birkhoffOrder`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.claim`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.claimAt`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.hyperExtend`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.meetOrder`
- Truth anchor: `D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.result`
