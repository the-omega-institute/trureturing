# The sharp classical network coherence bound

## Abstract

The coherence merit of a mixture of two binary product laws has attainable maximum one quarter for every n at least two.

**Definition 1.1 (Parity of a binary string).**

$$\forall (n: \mathbb{N}), \forall (a: \operatorname{Fin}\left(n\right) \to \mathrm{Bool}), \operatorname{parity}\left(a\right) = \operatorname{occupationCount}\left(a\right) \bmod (2: \mathbb{N})$$

*Formalization.* `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.parity` (`✓ std3`).

*Citation.* Fatemeh Bibak; Flavio Del Santo; Borivoje Dakić (2024). *Quantum coherence in networks*. DOI: [10.1103/PhysRevLett.133.230201](https://doi.org/10.1103/PhysRevLett.133.230201). URL: <https://arxiv.org/abs/2407.11122v1>.

*Commentary.*

A binary string a assigns a Boolean to each element of Fin n. The occupation count is the natural sum of the values (a i).toNat, where false has value zero and true has value one. Reducing this count modulo two gives parity. The two parity classes are those used in main.tex, lines 263–271, of Quantum coherence in networks.

**Definition 1.2 (A mixture of two product laws).**

$$\forall (n: \mathbb{N}), \forall (\gamma: \mathbb{R}), \forall (p: \operatorname{Fin}\left(n\right) \to \left(\mathrm{Bool} \to \mathbb{R}\right)), \forall (q: \operatorname{Fin}\left(n\right) \to \left(\mathrm{Bool} \to \mathbb{R}\right)), \operatorname{classicalMixture}\left(n, \gamma, p, q\right) = ((a: \operatorname{Fin}\left(n\right) \to \mathrm{Bool})\mapsto ((\gamma) \cdot (\operatorname{windowLaw}\left(p, a\right))) + ((((1: \mathbb{R})) - (\gamma)) \cdot (\operatorname{windowLaw}\left(q, a\right))))$$

*Formalization.* `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.classicalMixture` (`✓ std3`).

*Citation.* Fatemeh Bibak; Flavio Del Santo; Borivoje Dakić (2024). *Quantum coherence in networks*. DOI: [10.1103/PhysRevLett.133.230201](https://doi.org/10.1103/PhysRevLett.133.230201). URL: <https://arxiv.org/abs/2407.11122v1>.

*Commentary.*

For each string a, windowLaw p a is the product of p i (a i) over all i in Fin n. The displayed function combines this product with the corresponding product for q, with weights γ and 1 − γ. This is equation (pncl), main.tex, lines 248–253. The function is defined for all real γ and real local functions p and q. It is a probability law when γ lies in the real interval [0,1] and every local function is a probability distribution.

**Definition 1.3 (The parity coherence merit).**

$$\forall (n: \mathbb{N}), \forall (r: (\operatorname{Fin}\left(n\right) \to \mathrm{Bool}) \to \mathbb{R}), \operatorname{coherenceMerit}\left(n, r\right) = (\frac{(1: \mathbb{R})}{(2: \mathbb{R})}) \cdot (\left|(\sum_{a: \operatorname{Fin}\left(n\right) \to \mathrm{Bool}, \operatorname{parity}\left(a\right) = (0: \mathbb{N})} (\sum_{b: \operatorname{Fin}\left(n\right) \to \mathrm{Bool}, \operatorname{parity}\left(b\right) = (0: \mathbb{N})} (\operatorname{ite}\left(a \ne b, (r\left(a\right)) \cdot (r\left(b\right)), (0: \mathbb{R})\right)))) - (\sum_{a: \operatorname{Fin}\left(n\right) \to \mathrm{Bool}, \operatorname{parity}\left(a\right) = (1: \mathbb{N})} (\sum_{b: \operatorname{Fin}\left(n\right) \to \mathrm{Bool}, \operatorname{parity}\left(b\right) = (1: \mathbb{N})} (\operatorname{ite}\left(a \ne b, (r\left(a\right)) \cdot (r\left(b\right)), (0: \mathbb{R})\right))))\right|)$$

*Formalization.* `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.coherenceMerit` (`✓ std3`).

*Citation.* Fatemeh Bibak; Flavio Del Santo; Borivoje Dakić (2024). *Quantum coherence in networks*. DOI: [10.1103/PhysRevLett.133.230201](https://doi.org/10.1103/PhysRevLett.133.230201). URL: <https://arxiv.org/abs/2407.11122v1>.

*Commentary.*

For an arbitrary real function r on binary strings, sum r a times r b over ordered pairs of distinct even strings, and subtract the same sum over ordered pairs of distinct odd strings. The merit is half the absolute value of this difference. Each conditional makes the diagonal term zero. Both indices in each sum have the indicated parity. This reads equation (cn) and its explanation in main.tex, lines 263–271, with ordered pairs. For n at least two, a uniform law on the even strings gives the value one half minus two to the power minus n stated at lines 272–276.

**Definition 1.4 (The attainable classical maximum).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((2: \mathbb{N}) \le n) \Rightarrow (\operatorname{IsGreatest}\left(\{c: \mathbb{R} \mid \exists (\gamma: \mathbb{R}), (\gamma \in \operatorname{Set.Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \land (\exists (p: \operatorname{Fin}\left(n\right) \to \left(\mathrm{Bool} \to \mathbb{R}\right)), \exists (q: \operatorname{Fin}\left(n\right) \to \left(\mathrm{Bool} \to \mathbb{R}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{Probability}\left(p\left(i\right)\right)) \land ((\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{Probability}\left(q\left(i\right)\right)) \land (c = \operatorname{coherenceMerit}\left(n, \operatorname{classicalMixture}\left(n, \gamma, p, q\right)\right))))\}, \frac{(1: \mathbb{R})}{(4: \mathbb{R})}\right)))$$

*Formalization.* `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fatemeh Bibak; Flavio Del Santo; Borivoje Dakić (2024). *Quantum coherence in networks*. DOI: [10.1103/PhysRevLett.133.230201](https://doi.org/10.1103/PhysRevLett.133.230201). URL: <https://arxiv.org/abs/2407.11122v1>.

*Commentary.*

For every natural n at least two, consider all merits of the displayed mixtures with γ in [0,1] and with p i and q i probability distributions on Bool for every i. Probability means that both values are nonnegative and their sum is one. IsGreatest asserts that one quarter belongs to this set and bounds every member from above. This is the reading of the conjecture at main.tex, lines 277–278, for the ordered pair convention and n at least two. At n equal to one, each parity class has one string and the merit is zero.

**Theorem 1.5 (The sharp bound in every dimension n at least two).**

$$\forall (n: \mathbb{N}), ((2: \mathbb{N}) \le n) \Rightarrow (\operatorname{IsGreatest}\left(\{c: \mathbb{R} \mid \exists (\gamma: \mathbb{R}), (\gamma \in \operatorname{Set.Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \land (\exists (p: \operatorname{Fin}\left(n\right) \to \left(\mathrm{Bool} \to \mathbb{R}\right)), \exists (q: \operatorname{Fin}\left(n\right) \to \left(\mathrm{Bool} \to \mathbb{R}\right)), (\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{Probability}\left(p\left(i\right)\right)) \land ((\forall (i: \operatorname{Fin}\left(n\right)), \operatorname{Probability}\left(q\left(i\right)\right)) \land (c = \operatorname{coherenceMerit}\left(n, \operatorname{classicalMixture}\left(n, \gamma, p, q\right)\right))))\}, \frac{(1: \mathbb{R})}{(4: \mathbb{R})}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/bibak-del-santo-dakic-2024-classical-network-coherence-bound` (proved) by `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bibak-del-santo-dakic-2024-classical-network-coherence-bound","declaration_gid":"D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fatemeh Bibak; Flavio Del Santo; Borivoje Dakić (2024). *Quantum coherence in networks*. DOI: [10.1103/PhysRevLett.133.230201](https://doi.org/10.1103/PhysRevLett.133.230201). URL: <https://arxiv.org/abs/2407.11122v1>.

*Commentary.*

For a finite set s, the sum of r a times r b over its distinct ordered pairs equals the square of the sum of r on s minus the sum of the squares. Indeed, each row is r a times the total sum minus (r a) squared. Apply this identity to the two parity classes. The sign χ(a) = (−1) to the power of the natural sum of (a i).toNat is positive on the even class and negative on the odd class. These classes partition all strings. If r sums to one, their masses e and o satisfy e + o = 1, so e squared minus o squared equals e − o. Thus the merit is half of |T − U|, where T is the sum of χ(a) r a and U is the sum of χ(a) (r a) squared.

For any local functions w, distributing the product over the Boolean choices shows that the signed sum of the product law is the product of w i false − w i true. The mixture sums to one because each of its two product laws does. Put x i = p i false − p i true and y i = q i false − q i true, and let A and B be their respective products. Let D be the product of (x i + y i)/2. The signed sum T is γA + (1 − γ)B. For the square terms, local normalization gives (p i false) squared minus (p i true) squared equal to x i, and the analogous identity for q. The mixed local difference p i false times q i false minus p i true times q i true equals (x i + y i)/2. Expanding the square of the mixture therefore gives U = γ squared times A + (1 − γ) squared times B + 2γ(1 − γ)D. Subtraction and nonnegativity of γ(1 − γ) give the merit as γ(1 − γ)|A + B − 2D|/2.

To bound the last absolute value, take x i and y i in [−1,1] and induct over a finite set of coordinates s. The expression is zero for the empty set. For the products P, Q and D over s, write F = P + Q − 2D. The induction hypothesis gives |F| ≤ 2. Each factor has absolute value at most one, so |P| and |Q| are at most one and |P − Q| and |Q − P| are at most two. On adding a coordinate i, set u = (1 + x i)/2 and v = (1 + y i)/2. The new expression is uvF + u(1 − v)(P − Q) + (1 − u)v(Q − P) + (1 − u)(1 − v)(−F). All four coefficients are nonnegative and sum to one. The triangle inequality bounds its absolute value by two, completing the induction and giving the bound over Fin n.

Nonnegativity and normalization of p i and q i place x i and y i in [−1,1]. The factorization and the preceding bound give a merit at most γ(1 − γ). The nonnegative square of γ − 1/2 then bounds this by one quarter.

To reach the bound, write n = k + 2. Set γ = 1/2, and let p i put all its mass at false. Let q i put all its mass at true when i.val < 2 and at false otherwise. These are probability distributions. The products A and B are both one: the first two factors of B are minus one and all remaining factors are one. The product D is zero because its factor at coordinate zero is zero. Substituting A = B = 1 and D = 0 into the factorization gives exactly one quarter. Hence one quarter is a member of the attainable set; applying the upper bound to any other member proves that it is the greatest member.

## References

- Truth anchor: `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.claim`
- Truth anchor: `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.classicalMixture`
- Truth anchor: `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.coherenceMerit`
- Truth anchor: `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.parity`
- Truth anchor: `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.result`
- Dependency: [D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy](../Entropy/NamingWindow/GreenClassWindowEntropy.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../TotalVariation/CycleSingleCutMinimax.md)
