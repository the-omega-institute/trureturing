# Representation

## Abstract

Finite Riesz moments, orthogonal Laurent polynomials and scale-four projection identities.

The CMV blocks use the positive Szego normalization at each real Schur parameter.

$\forall (k : \mathbb{N}) , \rho_{k} = \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} (\alpha_{k} : \mathbb{C}) = \sqrt{1 - \lvert \alpha_{k}\rvert^{2}}$

**Definition 1.1 (R).**

$$\forall (x : \mathbb{N}) , \operatorname{R} x = \operatorname{if} x = 0 \operatorname{then} \begin{pmatrix}\operatorname{alpha} 0&\operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} 0)\right)\\\operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} 0)\right) \cdot \operatorname{alpha} 1&- \operatorname{alpha} 0 \cdot \operatorname{alpha} 1\end{pmatrix} \operatorname{else} \begin{pmatrix}- \operatorname{alpha} (2 \cdot x - 1) \cdot \operatorname{alpha} (2 \cdot x)&- \operatorname{alpha} (2 \cdot x - 1) \cdot \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x))\right)\\\operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x))\right) \cdot \operatorname{alpha} (2 \cdot x + 1)&- \operatorname{alpha} (2 \cdot x) \cdot \operatorname{alpha} (2 \cdot x + 1)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.R` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “From the Verblunsky parameters, the corresponding QW on ℤ≥ is determined by” the displayed block matrix. The diagonal site blocks of the transposed CMV walk, with the boundary block R₀ stated separately, Section 2.

**Definition 1.2 (P).**

$$\forall (x : \mathbb{N}) , \operatorname{P} x = \begin{pmatrix}\operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x))\right) \cdot \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x + 1))\right)&- \operatorname{alpha} (2 \cdot x) \cdot \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x + 1))\right)\\0&0\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.P` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “From the Verblunsky parameters, the corresponding QW on ℤ≥ is determined by” the displayed block matrix. The block carrying amplitudes from site x to site x+1, Section 2.

**Definition 1.3 (Q).**

$$\forall (x : \mathbb{N}) , \operatorname{Q} x = \begin{pmatrix}0&0\\\operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x - 1))\right) \cdot \operatorname{alpha} (2 \cdot x)&\operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x - 1))\right) \cdot \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} \operatorname{Complex.ofReal}\left((\operatorname{alpha} (2 \cdot x))\right)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.Q` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “From the Verblunsky parameters, the corresponding QW on ℤ≥ is determined by” the displayed block matrix. The block carrying amplitudes from site x to site x−1, Section 2.

**Definition 1.4 (step).**

$$\forall (v : \mathbb{N} \to \mathbb{R}) (j : \mathbb{N}) , \operatorname{step} v j = \operatorname{let} x : = \operatorname{Nat.div} j 2 ; \operatorname{let} i : = \operatorname{Fin.ofNat} 2 j ; (\sum (c : Fin 2) , \operatorname{R} x i c \cdot v (2 \cdot x + \operatorname{Fin.val} c)) + (\operatorname{if} x = 0 \operatorname{then} 0 \operatorname{else} \sum (c : Fin 2) , \operatorname{P} (x - 1) i c \cdot v (2 \cdot (x - 1) + \operatorname{Fin.val} c)) + (\sum (c : Fin 2) , \operatorname{Q} (x + 1) i c \cdot v (2 \cdot (x + 1) + \operatorname{Fin.val} c))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.step` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “The evolution is defined by the equation Ψₜ₊₁ = U⁽ˢ⁾Ψₜ, where Ψₜ = [Ψₜ(0), Ψₜ(1), Ψₜ(2), …]ᵀ.” The coordinates 2x and 2x+1 are respectively the left and right components. The boundary omits the term from site −1. Division by 2 is natural-number division rounded down.

**Definition 1.5 (psi).**

$$\begin{aligned}\operatorname{psi} 0 = \operatorname{Pi.single} 0 1\\\forall (t : \mathbb{N}) , \operatorname{psi} (t + 1) = \operatorname{step} (\operatorname{psi} t)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.psi` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “The evolution is defined by the equation Ψₜ₊₁ = U⁽ˢ⁾Ψₜ, where Ψₜ = [Ψₜ(0), Ψₜ(1), Ψₜ(2), …]ᵀ.” The initial flattened amplitude is Pi.single 0 1, representing Ψ₀ = [1, 0]ᵀδ₀.

**Definition 1.6 (mu).**

$$\forall (t x : \mathbb{N}) , \operatorname{mu} t x = (\operatorname{psi} t (2 \cdot x))^{2} + (\operatorname{psi} t (2 \cdot x + 1))^{2}$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.mu` (`✓ std3`).

*Citation.* Ryota Hanaoka, Norio Konno (2021). *Return probability and self-similarity of the Riesz walk*. DOI: [10.26421/QIC21.5-6-5](https://doi.org/10.26421/QIC21.5-6-5). URL: <https://arxiv.org/abs/2010.04518v3>.

*Commentary.*

Section 2, arXiv PDF p. 2: “Then the probability of location x at time t is given by μₜ(x)=‖Ψₜ(x)‖²=|Ψₜᴸ(x)|²+|Ψₜᴿ(x)|².” The two real components are psi t (2*x) and psi t (2*x+1).

**Theorem 1.7 (mu outside).**

$$\forall (t x : \mathbb{N}) , t < x \to \operatorname{mu} t x = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Representation.mu_outside` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For natural time t and site x with t strictly less than x, the walk probability mu t x is zero.

**Definition 1.8 (SpectralBridge).**

$$\forall (chi : \mathbb{N} \to LaurentPolynomial \mathbb{R}) , \operatorname{SpectralBridge} chi \iff (chi 0 = \operatorname{LaurentPolynomial.T} 0) \land (\forall (i j : \mathbb{N}) , \operatorname{sigma} (chi i) (chi j) = \operatorname{if} i = j \operatorname{then} 1 \operatorname{else} 0) \land (\forall (Y : \mathbb{N}) , \operatorname{Submodule.span} \mathbb{R} (\operatorname{Set.image} chi \{j : \mathbb{N} \mid j < 2 \cdot Y + 2\}) = \operatorname{V} Y) \land (\forall (q : LaurentPolynomial \mathbb{R}) (j : \mathbb{N}) , \operatorname{sigma} (chi j) (\operatorname{LaurentPolynomial.T} (- 1) \cdot q) = \operatorname{step} (\operatorname{fun} (k : \mathbb{N}) \mapsto \operatorname{sigma} (chi k) q) j)$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.SpectralBridge` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

A Laurent polynomial sequence satisfies SpectralBridge when its first term is the constant monomial, it is sigma orthonormal, its first twice Y plus two terms span V Y for every natural Y, and pairing with multiplication by the monomial at negative one acts by step on its coefficient sequence.

**Definition 1.9 (cumulative).**

$$\forall (n Y : \mathbb{N}) , \operatorname{cumulative} n Y = \sum y \in \operatorname{Finset.range} (Y + 1) , \operatorname{mu} n y$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.cumulative` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For natural time n and site Y, cumulative n Y is the sum of the walk probabilities over sites zero through Y inclusive.

**Theorem 1.10 (amplitude spectral).**

$$\forall \{chi : \mathbb{N} \to LaurentPolynomial \mathbb{R}\} , \operatorname{SpectralBridge} chi \to \forall (t j : \mathbb{N}) , \operatorname{psi} t j = (\operatorname{sigma} (chi j)) (\operatorname{LaurentPolynomial.T} (- \operatorname{Nat.cast}\left(t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Representation.amplitude_spectral` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a Laurent polynomial sequence satisfies SpectralBridge, then for every natural time t and coordinate j, psi t j equals the sigma pairing of its jth term with the Laurent monomial at negative t.

**Theorem 1.11 (cumulative projection).**

$$\forall \{chi : \mathbb{N} \to LaurentPolynomial \mathbb{R}\} , \operatorname{SpectralBridge} chi \to \forall (n Y : \mathbb{N}) , \exists (h : LaurentPolynomial \mathbb{R}) , \operatorname{IsProjection} \operatorname{sigma} (\operatorname{V} Y) (\operatorname{LaurentPolynomial.T} (- \operatorname{Nat.cast}\left(n\right))) h \land (\operatorname{sigma} h) h = \operatorname{cumulative} n Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Representation.cumulative_projection` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If a Laurent polynomial sequence satisfies SpectralBridge, then for natural n and Y there is a sigma projection of the monomial at negative n onto V Y whose sigma pairing with itself equals cumulative n Y.

**Definition 1.12 (PairRelations).**

$$\forall (chi xi : \mathbb{N} \to LaurentPolynomial \mathbb{R}) , \operatorname{PairRelations} chi xi \iff (chi 0 = xi 0) \land (\forall (x : \mathbb{N}) , chi (2 \cdot x + 1) = \operatorname{alpha} (2 \cdot x + 1) \cdot xi (2 \cdot x + 1) + \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} (\operatorname{Complex.ofReal} (\operatorname{alpha} (2 \cdot x + 1))) \cdot xi (2 \cdot x + 2)) \land (\forall (x : \mathbb{N}) , 1 \leq x \to chi (2 \cdot x) = \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} (\operatorname{Complex.ofReal} (\operatorname{alpha} (2 \cdot x - 1))) \cdot xi (2 \cdot x - 1) - \operatorname{alpha} (2 \cdot x - 1) \cdot xi (2 \cdot x)) \land (\forall (x : \mathbb{N}) , \operatorname{LaurentPolynomial.T} 1 \cdot xi (2 \cdot x) = \operatorname{alpha} (2 \cdot x) \cdot chi (2 \cdot x) + \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} (\operatorname{Complex.ofReal} (\operatorname{alpha} (2 \cdot x))) \cdot chi (2 \cdot x + 1)) \land (\forall (x : \mathbb{N}) , \operatorname{LaurentPolynomial.T} 1 \cdot xi (2 \cdot x + 1) = \operatorname{D5.S3.Weil.Szego.CanonicalTransfer.szegoRho} (\operatorname{Complex.ofReal} (\operatorname{alpha} (2 \cdot x))) \cdot chi (2 \cdot x) - \operatorname{alpha} (2 \cdot x) \cdot chi (2 \cdot x + 1))$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.PairRelations` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

Two Laurent polynomial sequences satisfy PairRelations when their first terms agree, their odd and positive even terms satisfy the displayed relations using alpha and szegoRho at odd indices, and multiplication by the monomial at exponent one satisfies the two displayed relations at even parameter indices.

**Theorem 1.13 (one step of pair relations).**

$$\forall \{chi xi : \mathbb{N} \to LaurentPolynomial \mathbb{R}\} , \operatorname{PairRelations} chi xi \to \forall (q : LaurentPolynomial \mathbb{R}) (j : \mathbb{N}) , (\operatorname{sigma} (chi j)) (\operatorname{LaurentPolynomial.T} (- 1) \cdot q) = \operatorname{step} (\operatorname{fun} (k : \mathbb{N}) \mapsto (\operatorname{sigma} (chi k)) q) j$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Representation.one_step_of_pair_relations` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If chi and xi satisfy PairRelations, then for every real Laurent polynomial q and natural j, pairing chi j with q multiplied by the monomial at negative one equals step applied to the sequence of sigma pairings with q at coordinate j.

**Definition 1.14 (alternate).**

$$\forall (j : \mathbb{N}) , \operatorname{alternate} j = \operatorname{if} j \operatorname{mod} 2 = 0 \operatorname{then} \operatorname{LaurentPolynomial.T} (- \operatorname{Nat.cast}\left((\operatorname{Nat.div} j 2)\right)) \cdot \operatorname{normalizedPhi} j \operatorname{else} \operatorname{LaurentPolynomial.T} (- \operatorname{Nat.cast}\left((\operatorname{Nat.div} j 2)\right) - 1) \cdot \operatorname{normalizedPhiStar} j$$

*Formalization.* `D5/S3/Quantum/Walks/CMV/Representation.alternate` (`✓ std3`).

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

For a natural index j, alternate j shifts normalizedPhi j by negative half of j when j is even, and shifts normalizedPhiStar j by negative half of j minus one when j is odd; division by two is natural-number division rounded down. For natural arguments, mod denotes Nat.mod, the remainder of natural-number division.

**Theorem 1.15 (pair relations of parameters).**

$$(\forall (n : \mathbb{N}) , \operatorname{alpha} n = \operatorname{verblunsky} n) \to \operatorname{PairRelations} \operatorname{chi} \operatorname{alternate}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/CMV/Representation.pair_relations_of_parameters` (`✓ std3`). ∎

*Citation.* Barry Simon (2005). *Orthogonal Polynomials on the Unit Circle, Part 1: Classical Theory*. DOI: [10.1090/coll054.1](https://doi.org/10.1090/coll054.1). URL: <https://doi.org/10.1090/coll054.1>.

*Commentary.*

If alpha n equals verblunsky n for every natural n, the sequences chi and alternate satisfy PairRelations.

## References

- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.P`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.PairRelations`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.Q`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.R`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.SpectralBridge`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.alternate`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.amplitude_spectral`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.cumulative`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.cumulative_projection`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.mu`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.mu_outside`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.one_step_of_pair_relations`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.pair_relations_of_parameters`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.psi`
- Truth anchor: `D5/S3/Quantum/Walks/CMV/Representation.step`
- Dependency: [D5/S3/Quantum/Walks/CMV/Geronimus](Geronimus.md)
