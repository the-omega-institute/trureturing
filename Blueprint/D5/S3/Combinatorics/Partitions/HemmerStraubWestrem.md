# The Hemmer–Straub–Westrem Ev character identity

## Abstract

The alternating Ev sum over even three-row characters equals the Ev sum of the two-row character for every partition of positive size.

**Definition 1.1 (The power-sum product).**

$$\forall tau \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{powerSumProd}\left(tau\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{MvPolynomial}.\operatorname{psum}\left(\operatorname{Fin}\left(3\right), \operatorname{Int}\right), tau\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.powerSumProd` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

For a list of cycle lengths, multiply the three-variable power sums, retaining every occurrence of a length. Here psum is Mathlib's sum of the powers of the three variables.

**Definition 1.2 (The three-variable alternant).**

$$\operatorname{vandermonde3} = (\operatorname{MvPolynomial}.\operatorname{X}\left(0\right)-\operatorname{MvPolynomial}.\operatorname{X}\left(1\right)) \cdot (\operatorname{MvPolynomial}.\operatorname{X}\left(0\right)-\operatorname{MvPolynomial}.\operatorname{X}\left(2\right)) \cdot (\operatorname{MvPolynomial}.\operatorname{X}\left(1\right)-\operatorname{MvPolynomial}.\operatorname{X}\left(2\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.vandermonde3` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

The Vandermonde factor corresponds to the exponent shift (2,1,0).

**Definition 1.3 (The Frobenius coefficient).**

$$\forall mu \in \operatorname{Fin}\left(3\right) \to \operatorname{Nat},\; \forall tau \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{frobChar}\left(mu, tau\right) = \operatorname{AddMonoidAlgebra}.\operatorname{coeff}\left(\operatorname{vandermonde3} \cdot \operatorname{powerSumProd}\left(tau\right), \operatorname{Finsupp}.\operatorname{equivFunOnFinite}.\operatorname{symm}\left((\operatorname{fun}(i: \operatorname{Fin}\left(3\right)) \mapsto mu\left(i\right)+(2-(i: \operatorname{Nat})))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.frobChar` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Lemma 3.1, page 5, states: “Let µ, λ ⊢ n. We have: χ^µ_λ = ⟨p_λ, s_µ⟩.” The displayed coefficient is the three-variable Frobenius expression for this irreducible character, for partitions with at most three parts padded by zeros. Its identification with the representation-theoretic character is a literature input; it is not formalized here. The index subtraction is truncated subtraction in Nat.

**Definition 1.4 (The multiset of doubled cycle types).**

$$(\operatorname{evTypes}\left([]\right) = [[]]) \land (\forall a \in \operatorname{Nat},\; \forall l \in \operatorname{List}\left(\operatorname{Nat}\right),\; \operatorname{evTypes}\left((a::l)\right) = \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto (2 \cdot a::tau)), \operatorname{evTypes}\left(l\right)\right), \operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto (a::(a::tau))), \operatorname{evTypes}\left(l\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.evTypes` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Page 1 states: “In [Amd23], Amdeberhan defined Ev(λ) to be the set of all partitions of 2n obtained by replacing each λᵢ with either 2λᵢ or two copies of λᵢ, and then reordering the parts to be nonincreasing.” Each occurrence of a part a contributes either (2a) or (a,a). The list retains multiplicity and represents cycle lengths before sorting; frobChar is unchanged by permuting that list. Section 2.1, page 4, gives multiplicities 1,4,6,4,1 for the five cycle types in Ev((1,1,1,1)). The two equations include the empty-list case.

**Definition 1.5 (Even partitions with at most three parts).**

$$\forall m \in \operatorname{Nat},\; \operatorname{R3}\left(m\right) = \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun}(mu: \operatorname{Fin}\left(3\right) \to \operatorname{Nat}) \mapsto (mu\left(1\right) \le mu\left(0\right)) \land ((mu\left(2\right) \le mu\left(1\right)) \land (\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{Even}\left(mu\left(i\right)\right)))), \operatorname{Finset}.\operatorname{Nat}.\operatorname{antidiagonalTuple}\left(3, m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.R3` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Page 3 states: “When N = 1, the set R^c_{2N}(2n) is the single partition (n, n), and the set R_{2N+1}(2n) consists of all partitions of 2n with at most three parts, all even.” antidiagonalTuple enumerates triples with the indicated sum; the filter requires decreasing order and even entries, including zero padding.

**Definition 1.6 (Conjecture 2.3).**

$$(\operatorname{claim}) \Leftrightarrow (\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow (\forall lam \in \operatorname{Nat}.\operatorname{Partition}\left(n\right),\; \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto \sum_{mu \in \operatorname{R3}\left(2 \cdot n\right)} (((-1: \operatorname{Int}))^{\operatorname{List}.\operatorname{length}\left(tau\right)} \cdot \operatorname{frobChar}\left(mu, tau\right))), \operatorname{evTypes}\left(lam.\operatorname{parts}.\operatorname{toList}\right)\right)\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto \operatorname{frobChar}\left(![n,n,0], tau\right)), \operatorname{evTypes}\left(lam.\operatorname{parts}.\operatorname{toList}\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.claim` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Conjecture 2.3 (N = 1 version), page 3, states: “For any partition λ ⊢ n, we have ∑_{λ̃∈Ev(λ)} ∑_{µ∈R₃(2n)} (−1)^{ℓ(λ̃)} χ^µ_{λ̃} = ∑_{λ̃∈Ev(λ)} χ^{(n,n)}_{λ̃}. (2.4)” The encoding takes n ≥ 1 and lam : Nat.Partition n, lists its positive parts, and preserves multiplicities in both Ev sums. τ.length is the number of parts and ![n,n,0] pads the two-row partition by zero.

**Theorem 1.7 (The identity for every partition).**

$$\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow (\forall lam \in \operatorname{Nat}.\operatorname{Partition}\left(n\right),\; \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto \sum_{mu \in \operatorname{R3}\left(2 \cdot n\right)} (((-1: \operatorname{Int}))^{\operatorname{List}.\operatorname{length}\left(tau\right)} \cdot \operatorname{frobChar}\left(mu, tau\right))), \operatorname{evTypes}\left(lam.\operatorname{parts}.\operatorname{toList}\right)\right)\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto \operatorname{frobChar}\left(![n,n,0], tau\right)), \operatorname{evTypes}\left(lam.\operatorname{parts}.\operatorname{toList}\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result` (`✓ std3`). ∎

*Resolves.* `Problems/hemmer-straub-westrem-2025-ev-character-identity` (proved) by `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hemmer-straub-westrem-2025-ev-character-identity","declaration_gid":"D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Both sides equal 2 to the number of parts times the difference between the coefficients of degrees n and n+1 in the product of X^(2a)+X^a+1 over the parts a. The alternating expansion uses p_a²−p_(2a) in three variables; the other expansion uses p_a²+p_(2a) at (X,1,0). The symmetric homogeneous coefficient detector identifies the first sum with that same difference. The argument applies to any ordered list of positive parts with positive sum, so no single-part-size or sorting hypothesis enters the coefficient argument. The identities for N ≥ 2, the closed form of Conjecture 6.1, and explicit bijective proofs remain separate questions.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.R3`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.evTypes`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.frobChar`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.powerSumProd`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.vandermonde3`
