# Maximal walk entanglement from the symmetric coin

## Abstract

The symmetric localized coin maximizes full-mode geometric entanglement at every time on every finite circle.

**Definition 1.1 (The Hadamard step on a circle).**

$$\forall \left(p: \mathbb{N}\right), \left(\forall \left(\psi: \left(\left(\operatorname{Fin}\left(2\right)\right) \times \left(\operatorname{ZMod}\left(p\right)\right)\right) \to \left(\mathbb{C}\right)\right), \left(\operatorname{hadamardStep}\left(p, \psi\right) = \lambda \left(j: \left(\operatorname{Fin}\left(2\right)\right) \times \left(\operatorname{ZMod}\left(p\right)\right)\right) \mapsto \left(\operatorname{ite}\left(\operatorname{Prod.fst}\left(j\right) = \left(0: \operatorname{Fin}\left(2\right)\right), \frac{\psi\left(\left(\left(0: \operatorname{Fin}\left(2\right)\right), \operatorname{Prod.snd}\left(j\right) + \left(1: \operatorname{ZMod}\left(p\right)\right)\right)\right) + \psi\left(\left(\left(1: \operatorname{Fin}\left(2\right)\right), \operatorname{Prod.snd}\left(j\right) + \left(1: \operatorname{ZMod}\left(p\right)\right)\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(2: \mathbb{R}\right)\right)\right)}, \frac{\psi\left(\left(\left(0: \operatorname{Fin}\left(2\right)\right), \operatorname{Prod.snd}\left(j\right) - \left(1: \operatorname{ZMod}\left(p\right)\right)\right)\right) - \psi\left(\left(\left(1: \operatorname{Fin}\left(2\right)\right), \operatorname{Prod.snd}\left(j\right) - \left(1: \operatorname{ZMod}\left(p\right)\right)\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(2: \mathbb{R}\right)\right)\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.hadamardStep` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

The coin labels zero and one represent the left-moving and right-moving components. A Hadamard coin flip followed by the controlled periodic shift gives the displayed amplitudes: the left-moving amplitude at a position comes from the next position, and the right-moving amplitude comes from the preceding position. Positions are residues in ZMod p. The real square root of two is explicitly included in the complex scalars. This is the walk of arxiv-v1.tex, lines 139–166; the definition also makes sense at p equal to zero.

**Definition 1.2 (Evolution of a localized coin).**

$$\forall \left(p: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right), \left(\operatorname{walkState}\left(p, n, c\right) = \operatorname{Nat.iterate}\left(\operatorname{hadamardStep}\left(p\right), n, \lambda \left(j: \left(\operatorname{Fin}\left(2\right)\right) \times \left(\operatorname{ZMod}\left(p\right)\right)\right) \mapsto \left(\operatorname{ite}\left(\operatorname{Prod.snd}\left(j\right) = \left(0: \operatorname{ZMod}\left(p\right)\right), c\left(\operatorname{Prod.fst}\left(j\right)\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.walkState` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

Initially the two coin amplitudes c are at position zero and every other position has amplitude zero. Iterating the Hadamard step n times gives walkState. The time evolution is specified in arxiv-v1.tex, lines 165–166, and the localized initial states in lines 423–425. The definition allows every complex coin c.

**Definition 1.3 (The symmetric coin).**

$$\left(\operatorname{cStar}: \left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right) = ![\frac{\left(1: \mathbb{C}\right)}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(2: \mathbb{R}\right)\right)\right)}, \frac{\operatorname{Complex.I}}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\left(2: \mathbb{R}\right)\right)\right)}]$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.cStar` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

The entries are one over the square root of two and the imaginary unit over the square root of two. They give the source's angles theta and phi both equal to pi over two in the localized initial state, as in arxiv-v1.tex, lines 423–425 and 652–654.

**Definition 1.4 (The generalized W vector).**

$$\forall \left(\iota: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(\iota\right)] \forall \left(lam: \left(\iota\right) \to \left(\mathbb{C}\right)\right), \left(\operatorname{wState}\left(lam\right) = \lambda \left(s: \left(\iota\right) \to \left(\operatorname{Bool}\right)\right) \mapsto \left(\sum_{k: \iota} \left(\operatorname{ite}\left(s = \operatorname{Function.update}\left(\operatorname{Function.const}\left(\iota, \operatorname{false}\right), k, \operatorname{true}\right), lam\left(k\right), \left(0: \mathbb{C}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.wState` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

A Boolean string s records the occupation of each mode. For each k, updating the constantly false string to true at k gives the string with its sole excitation at k. The coefficient of that string is lam k; all other strings have coefficient zero. This is the generalized W state in arxiv-v1.tex, lines 286–293, expressed for an arbitrary finite mode type and without a normalization condition on lam.

**Definition 1.5 (A product of local two-component vectors).**

$$\forall \left(\iota: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(\iota\right)] \forall \left(z: \left(\iota\right) \to \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right)\right), \left(\operatorname{productState}\left(z\right) = \lambda \left(s: \left(\iota\right) \to \left(\operatorname{Bool}\right)\right) \mapsto \left(\prod_{k: \iota} \left(z\left(k, \operatorname{ite}\left(s\left(k\right) = \operatorname{true}, \left(1: \operatorname{Fin}\left(2\right)\right), \left(0: \operatorname{Fin}\left(2\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.productState` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

The amplitude at a Boolean string is the product of the chosen local coordinates: coordinate one at an occupied mode and coordinate zero at an empty mode. This expresses the product states of arxiv-v1.tex, lines 227–235, for the partition into individual modes. The vectors z need not be normalized in this definition.

**Definition 1.6 (Normalized local factors).**

$$\forall \left(\iota: \operatorname{Type}*\right), \left(\forall \left(z: \left(\iota\right) \to \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right)\right), \left(\operatorname{unitFactors}\left(z\right) = \left(\forall \left(k: \iota\right), \left(\operatorname{D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor}\left(z\left(k\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.unitFactors` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

Each local two-component vector has the sum of its squared complex moduli equal to one. UnitSpinor denotes precisely this unit Hilbert norm condition. These are the normalized factors used in the product-state supremum of arxiv-v1.tex, lines 249–254.

**Definition 1.7 (The product overlap).**

$$\forall \left(\iota: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(\iota\right)] \forall \left(lam: \left(\iota\right) \to \left(\mathbb{C}\right)\right), \left(\forall \left(z: \left(\iota\right) \to \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right)\right), \left(\operatorname{overlap}\left(lam, z\right) = \sum_{s: \left(\iota\right) \to \left(\operatorname{Bool}\right)} \left(\left(\operatorname{starRingEnd}\left(\mathbb{C}\right)\left(\operatorname{productState}\left(z, s\right)\right)\right) \cdot \left(\operatorname{wState}\left(lam, s\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.overlap` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

Sum over all Boolean occupation strings, conjugating the product-state amplitude and multiplying by the W-state amplitude. Thus overlap is the usual complex inner product with the product vector in its conjugate-linear argument. It is the overlap used in arxiv-v1.tex, lines 249–254, for the W states of lines 286–293.

**Definition 1.8 (The maximum squared product overlap).**

$$\forall \left(\iota: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(\iota\right)] \forall \left(lam: \left(\iota\right) \to \left(\mathbb{C}\right)\right), \left(\operatorname{gMax}\left(lam\right) = \operatorname{sSup}\left(\{t: \mathbb{R} \mid \exists \left(z: \left(\iota\right) \to \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right)\right), \left(\left(\operatorname{unitFactors}\left(z\right)\right) \land \left(t = \operatorname{Complex.normSq}\left(\operatorname{overlap}\left(lam, z\right)\right)\right)\right)\}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.gMax` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

Take the real supremum of the squared complex modulus of overlap over all unit local factors. Complex.normSq is the squared modulus, so no square root is taken in this definition. This is the full-partition quantity in arxiv-v1.tex, lines 249–254 and 281–290. The formula defines the functional for every finite amplitude family, including families that are not normalized.

**Definition 1.9 (Full-mode geometric entanglement).**

$$\forall \left(\iota: \operatorname{Type}*\right), \left([\operatorname{Fintype}\left(\iota\right)] \forall \left(lam: \left(\iota\right) \to \left(\mathbb{C}\right)\right), \left(\operatorname{geometricEntanglement}\left(lam\right) = \left(1: \mathbb{R}\right) - \operatorname{gMax}\left(lam\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.geometricEntanglement` (`✓ std3`).

*Citation.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

Subtracting the maximal squared product overlap from one gives the geometric measure in arxiv-v1.tex, lines 253–258. Every individual mode is a separate tensor factor. The definition is extended to arbitrary finite amplitude families; its interpretation as pure-state entanglement uses a normalized state.

**Definition 1.10 (The symmetric coin gives maximal entanglement).**

$$\operatorname{claim} = \left(\forall \left(p: \mathbb{N}\right), \left(\left(\left(1: \mathbb{N}\right) \le p\right) \Rightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor}\left(c\right)\right) \Rightarrow \left(\operatorname{geometricEntanglement}\left(\operatorname{walkState}\left(p, n, c\right)\right) \le \operatorname{geometricEntanglement}\left(\operatorname{walkState}\left(p, n, \operatorname{cStar}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

For every natural p at least one, every natural time n, and every normalized coin c, the geometric entanglement of walkState p n c is at most that of walkState p n cStar. A positive p makes ZMod p a finite position type, giving two p individual modes. This states the expectation of arxiv-v1.tex, lines 652–654, for the circle walk and the full partition. Step zero and the one-position circle are included. The statement asserts maximality without asserting uniqueness.

**Theorem 1.11 (Balancing reflection pairs proves maximality).**

$$\forall \left(p: \mathbb{N}\right), \left(\left(\left(1: \mathbb{N}\right) \le p\right) \Rightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \left(\operatorname{Fin}\left(2\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor}\left(c\right)\right) \Rightarrow \left(\operatorname{geometricEntanglement}\left(\operatorname{walkState}\left(p, n, c\right)\right) \le \operatorname{geometricEntanglement}\left(\operatorname{walkState}\left(p, n, \operatorname{cStar}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.result` (`✓ std3`). ∎

*Resolves.* `Problems/donkersloot-sondenheimer-sperling-2026-symmetric-coin-entanglement` (proved) by `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"donkersloot-sondenheimer-sperling-2026-symmetric-coin-entanglement","declaration_gid":"D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling (2026). *Multipartite entanglement dynamics in quantum walks*. DOI: [10.48550/arXiv.2603.24679](https://doi.org/10.48550/arXiv.2603.24679). URL: <https://arxiv.org/abs/2603.24679v1>.

*Commentary.*

Expand the inner product by the single occupied mode. Its kth summand is lam k times the conjugate of the product of z k 1 with all z l 0 for l different from k. For unit local factors the squared norm of the product vector is one: the sum over occupation strings factors into the product of the local squared norms. Cauchy–Schwarz therefore bounds every squared overlap by the squared norm of the W vector. The local unit sets are closed and bounded, and hence compact; their finite product is compact and contains the constant family with local vector (1,0). The squared overlap is continuous on this product, so its supremum is attained.

Suppose lam and mu have equal squared moduli at every mode. At a mode with nonzero lam k, set rho k to mu k divided by lam k; at a zero coefficient set rho k to one. Then rho k has squared modulus one and mu k equals rho k times lam k. Multiplying the occupied coordinate of each local factor by rho k preserves its norm, and the conjugate phase cancels the coefficient phase in each expanded summand. Transporting factors in both directions gives equal sets of squared overlaps and therefore equal gMax values. For nonnegative real coefficients, the triangle inequality bounds the modulus of every complex overlap by the overlap of the coordinatewise moduli. Those real nonnegative factors remain normalized and attain the bound at a maximizer. Thus a maximum can be chosen with every local coordinate nonnegative and real.

The required two-dimensional optimization starts with the real quadratic form d times y 0 squared plus twice f times y 0 times y 1 plus e times y 1 squared, with f nonnegative. Let t be one half of the sum of d, e, and the square root of the sum of (d minus e) squared and four f squared. Then t is at least both d and e, and (t minus d)(t minus e) equals f squared. If t equals e, f is zero, the form is bounded by t on the unit circle, and (0,1) attains t. Otherwise t minus e is positive; multiplying the gap from t by t minus e expresses it as the square of (t minus e) times y 1 minus f times y 0. The nonnegative unit vector proportional to (t minus e,f) attains t.

Apply this quadratic optimization to d equal to a squared plus b squared r squared, e equal to b squared s squared, and f equal to a b s, where a, b, r, s are nonnegative. For unit real x and y, the squared bilinear expression a x 0 y 0 plus b s x 0 y 1 plus b r x 1 y 0 is bounded first by Cauchy–Schwarz in x and then by that quadratic maximum in y. Write C for a squared plus b squared times (r squared plus s squared). The resulting maximum is one half of the sum of C and the square root of the difference between C squared and four b to the fourth times r squared s squared. For a maximizing y, take the vector v with coordinates a y 0 plus b s y 1 and b r y 0. Its squared norm is the maximum. If that norm is zero, x equal to (1,0) attains zero; otherwise x equal to v divided by the square root of the maximum attains the bound. Both maximizing vectors have nonnegative coordinates.

Now fix two distinct modes i and j and all spectator factors. Let s be the other modes, d the sum of their single-excitation contributions, and e the product of their empty-mode coordinates. Splitting the expanded overlap into excitations in s, at j, and at i leaves d z i 0 z j 0 plus e a j z i 0 z j 1 plus e a i z i 1 z j 0. For nonnegative coefficient families a and b agreeing off i and j, suppose their sums of squares at the pair agree and b i squared times b j squared is at least a i squared times a j squared. Start with nonnegative maximizing factors for b. In the two-factor formula the trace C is unchanged, while the larger product for b decreases the expression under the square root. Replace only the two local factors by maximizing factors for a; the spectator contributions d and e stay the same. This gives gMax b at most gMax a. Replacing arbitrary complex coefficients by their moduli using phase invariance gives the same comparison whenever the squared moduli agree off the pair, their pair sums agree, and their pair products increase.

For the walk, induction on n gives linearity in c: each amplitude is c 0 times the evolution from (1,0) plus c 1 times the evolution from (0,1). A second induction proves that these two basis-coin evolutions are real. At reflected positions their amplitudes satisfy the following signs: the first evolution at (1,−x) is minus (−1) to the power n times the second at (0,x), and the second at (1,−x) is (−1) to the power n times the first at (0,x). The zero-step identities follow from localization; the induction step follows by substituting the Hadamard recurrence, using −x minus one equal to minus (x plus one), and reversing the sign at each step.

Let a and b be the real amplitudes of these two basis-coin evolutions at (0,x). For a unit coin c, linearity and reflection show that the two probabilities at (0,x) and (1,−x) are the squared moduli of c 0 times a plus c 1 times b, and c 1 times a minus c 0 times b. Their sum is a squared plus b squared: the mixed terms cancel and the coin squared norms sum to one. For cStar, each probability is half of a squared plus b squared, since the real and imaginary contributions have no mixed term. Consequently each reflection pair has the same total probability for both coins, and the probabilities for cStar are equal within each pair.

For positive p the pairs (0,x),(1,−x), indexed by ZMod p, partition all modes and have distinct members. Induct over a finite set of positions, using the cStar amplitudes on its pairs and the c amplitudes elsewhere. Adding a position changes only its pair. The pair sum is preserved, and equality of the new probabilities makes their product at least the old product, as follows by expanding the square of the old probability difference. The pair comparison therefore cannot increase gMax. Starting with the empty set and ending with all positions gives gMax of walkState p n cStar at most gMax of walkState p n c. Subtracting this inequality from one proves the stated entanglement comparison for every p, n, and c under the displayed hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.cStar`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.claim`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.gMax`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.geometricEntanglement`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.hadamardStep`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.overlap`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.productState`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.result`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.unitFactors`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.wState`
- Truth anchor: `D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement.walkState`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays](../Entanglement/AbsoluteSeparability/LowRankRays.md)
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry](../Recovery/FiniteLocalLatitudeGeometry.md)
