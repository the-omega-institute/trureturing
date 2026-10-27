# Manabe's restricted amalgamation Nim

## Abstract

Manabe's restricted three-pile amalgamation Nim satisfies Conjecture 1.

**Definition 1.1 (The six kinds of options).**

$$\forall x \in Nat,\; \forall y \in Nat,\; \forall z \in Nat,\; \operatorname{move}\left(x, y, z\right) = \{q : Nat \times (Nat \times Nat) | (\exists u \in Nat,\; (u < x) \land (q = (u, y, z))) \lor ((\exists v \in Nat,\; (v < y) \land (q = (x, v, z))) \lor ((\exists w \in Nat,\; (w < z) \land (q = (x, y, w))) \lor (((2 \le x) \land ((2 \le y) \land ((q = (x + y, 0, z)) \lor (q = (0, x + y, z))))) \lor (((2 \le y) \land ((2 \le z) \land ((q = (x, y + z, 0)) \lor (q = (x, 0, y + z))))) \lor ((2 \le x) \land ((2 \le z) \land ((q = (x + z, y, 0)) \lor (q = (0, y, x + z)))))))))\}$$

*Formalization.* `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.move` (`✓ std3`).

*Citation.* Hikaru Manabe (2024). *An Amalgamation Nim with Restriction*. DOI: [10.48550/arXiv.2411.14488](https://doi.org/10.48550/arXiv.2411.14488). URL: <https://arxiv.org/abs/2411.14488v1>.

*Commentary.*

Definition 4, page 2: “Two players take turns to do one of the following (i) and (ii). (i) A player chooses a pile and removes any number of stones from the pile. (ii) A player can replace two piles with a single pile containing the total number of stones in the original two piles when the numbers of stones in two piles are equal to or more than 2.” Definition 5, pages 2–3: “For x, y, z ∈ Z≥0, we define” move(x, y, z) by sets (1)–(6). The printed equality signs between those sets denote their union. Naturals include zero; each merger includes both placements of the sum and zero.

**Definition 1.2 (A decreasing measure).**

$$\forall x \in Nat,\; \forall y \in Nat,\; \forall z \in Nat,\; \operatorname{size}\left(x, y, z\right) = x + y + z + (if (x = 0) then 0 else 1) + (if (y = 0) then 0 else 1) + (if (z = 0) then 0 else 1)$$

*Formalization.* `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.size` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is the stone total plus the number of nonempty piles. Removing stones decreases it, and a legal merger preserves the stone total while decreasing the latter count.

**Definition 1.3 (The Grundy recursion).**

$$\forall x \in Nat,\; \forall y \in Nat,\; \forall z \in Nat,\; \operatorname{grundy}\left(x, y, z\right) = \operatorname{mex}\left(\{g : Nat | \exists q \in Nat \times (Nat \times Nat),\; (q \in \operatorname{move}\left(x, y, z\right)) \land (g = (if (\operatorname{size}\left(q.1, q.2.1, q.2.2\right) < \operatorname{size}\left(x, y, z\right)) then \operatorname{grundy}\left(q.1, q.2.1, q.2.2\right) else 0))\}\right)$$

*Formalization.* `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.grundy` (`✓ std3`).

*Citation.* Hikaru Manabe (2024). *An Amalgamation Nim with Restriction*. DOI: [10.48550/arXiv.2411.14488](https://doi.org/10.48550/arXiv.2411.14488). URL: <https://arxiv.org/abs/2411.14488v1>.

*Commentary.*

The Grundy number is the least excluded option value. The existing mex is D5.S0.Certificates.Games.AbukuEnforceNimberDomination.mex. Every option has smaller size, so the displayed recursion always takes the recursive branch on options. The product Nat × Nat × Nat is associated to the right; q.1, q.2.1 and q.2.2 are its entries.

**Definition 1.4 (Conjecture 1).**

$$claim = (\forall x \in Nat,\; \forall y \in Nat,\; \forall z \in Nat,\; \forall n \in Nat,\; ((\operatorname{grundy}\left(x, y, z\right) = 2 \cdot n) \Rightarrow ((\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n) \lor (\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n + 1))) \land ((\operatorname{grundy}\left(x, y, z\right) = 2 \cdot n + 1) \Rightarrow ((\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n) \lor (\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n + 1))))$$

*Formalization.* `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.claim` (`✓ std3`).

*Citation.* Hikaru Manabe (2024). *An Amalgamation Nim with Restriction*. DOI: [10.48550/arXiv.2411.14488](https://doi.org/10.48550/arXiv.2411.14488). URL: <https://arxiv.org/abs/2411.14488v1>.

*Commentary.*

Section 3, Conjecture 1, page 14: “For n ∈ Z≥0, we have the following (i) and (ii). (i) If the Grundy number of a position (x, y, z) is 2n, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1. (ii) If the Grundy number of a position (x, y, z) is 2n + 1, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1.” Here Nat.xor is bitwise XOR, the three pile sizes and n range over all naturals, and grundy uses exactly the six option sets.

**Theorem 1.5 (Both parts of the conjecture).**

$$\forall x \in Nat,\; \forall y \in Nat,\; \forall z \in Nat,\; \forall n \in Nat,\; ((\operatorname{grundy}\left(x, y, z\right) = 2 \cdot n) \Rightarrow ((\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n) \lor (\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n + 1))) \land ((\operatorname{grundy}\left(x, y, z\right) = 2 \cdot n + 1) \Rightarrow ((\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n) \lor (\operatorname{Nat}.xor\left(\operatorname{Nat}.xor\left(x, y\right), z\right) = 2 \cdot n + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hikaru Manabe (2024). *An Amalgamation Nim with Restriction*. DOI: [10.48550/arXiv.2411.14488](https://doi.org/10.48550/arXiv.2411.14488). URL: <https://arxiv.org/abs/2411.14488v1>.

*Commentary.*

Strong induction on size determines the exact Grundy value. Write each pile as 2a + e, with e equal to zero or one. Let h be the XOR of the three quotients, p the XOR of the three remainders, B the existence of a positive bitwise-disjoint pair of quotients, and E positivity and pairwise bitwise disjointness of all three quotients. Put δ = 1 exactly when B holds and E fails. The value is 2h + (p XOR δ). Ordinary reductions reach both values in every smaller quotient block. A legal merger preserving h reverses the corrected low bit; if that bit is one, a reduction of an odd pile or a merger of an even disjoint pair reaches 2h. Thus mex gives the formula and both asserted implications.

## References

- Truth anchor: `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.claim`
- Truth anchor: `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.grundy`
- Truth anchor: `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.move`
- Truth anchor: `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.result`
- Truth anchor: `D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.size`
- Dependency: [D5/S0/Certificates/Games/AbukuEnforceNimberDomination](AbukuEnforceNimberDomination.md)
