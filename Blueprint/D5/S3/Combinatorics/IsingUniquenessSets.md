# The smallest set of uniqueness for the Ising cone

## Abstract

On the cube of sign vectors, the Walsh functions of degree at most two span the Ising space. A set of points is a set of uniqueness for the nonnegative cone of this space when the only nonnegative function of the space vanishing there is zero; the smallest such set has k + 1 points for every k at least three.

**Definition 1.1 (The sign of a Boolean coordinate).**

$$\forall b \in \operatorname{Bool},\; \operatorname{sgn}\left(b\right) = \operatorname{ite}\left(b, 1, -(1)\right)$$

*Formalization.* `D5/S3/Combinatorics/IsingUniquenessSets.sgn` (`✓ std3`).

*Citation.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

A point of the cube is a function from Fin k to Bool; the value true stands for +1 and false for -1.

**Definition 1.2 (Walsh functions).**

$$\forall k \in \mathbb{N},\; \forall L \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \forall x \in \operatorname{Fin}\left(k\right) \to \operatorname{Bool},\; \operatorname{walsh}\left(L, x\right) = \prod_{j \in L} (\operatorname{sgn}\left(x\left(j\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/IsingUniquenessSets.walsh` (`✓ std3`).

*Citation.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

For a finite set L of coordinates, the Walsh function is the product of the coordinate signs over L; the empty product is the constant function one.

**Definition 1.3 (The space spanned by Walsh functions of bounded degree).**

$$\forall k \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{walshSpace}\left(k, q\right) = \operatorname{Submodule.span}\left(\mathbb{R}, \{\operatorname{walsh}\left(L\right) \mid L \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right), \operatorname{card}\left(L\right) \le q\}\right)$$

*Formalization.* `D5/S3/Combinatorics/IsingUniquenessSets.walshSpace` (`✓ std3`).

*Citation.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

The real linear span of the Walsh functions indexed by sets of at most q coordinates; for q = 2 it is the Ising space of constants, fields and pair couplings.

**Definition 1.4 (Sets of uniqueness for the nonnegative cone).**

$$\forall k \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall U \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; \operatorname{IsSetOfUniqueness}\left(k, q, U\right) \Leftrightarrow (\forall phi \in \operatorname{walshSpace}\left(k, q\right),\; (\forall x \in \operatorname{Fin}\left(k\right) \to \operatorname{Bool},\; 0 \le phi\left(x\right)) \Rightarrow ((\forall x \in U,\; phi\left(x\right) = 0) \Rightarrow (phi = 0)))$$

*Formalization.* `D5/S3/Combinatorics/IsingUniquenessSets.IsSetOfUniqueness` (`✓ std3`).

*Citation.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

A finite set U of points is a set of uniqueness for the nonnegative cone of the Walsh space when every nonnegative function of the space that vanishes on U is the zero function.

**Definition 1.5 (The smallest size of a set of uniqueness).**

$$\forall k \in \mathbb{N},\; \forall q \in \mathbb{N},\; \operatorname{minUniqueness}\left(k, q\right) = \operatorname{sInf}\left(\{n \in \mathbb{N} \mid \exists U \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; (\operatorname{card}\left(U\right) = n) \land (\operatorname{IsSetOfUniqueness}\left(k, q, U\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/IsingUniquenessSets.minUniqueness` (`✓ std3`).

*Citation.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

The infimum of the sizes of the sets of uniqueness; the whole cube is always one, so the infimum is attained.

**Definition 1.6 (The conjecture u(k, 2) = k + 1).**

$$claim \Leftrightarrow ((\forall k \in \mathbb{N},\; \forall U \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; (\operatorname{IsSetOfUniqueness}\left(k, 2, U\right)) \Rightarrow ((k) + (1) \le \operatorname{card}\left(U\right))) \land ((\forall k \in \mathbb{N},\; (3 \le k) \Rightarrow (\operatorname{minUniqueness}\left(k, 2\right) = (k) + (1))) \land (\operatorname{minUniqueness}\left(2, 2\right) = 4)))$$

*Formalization.* `D5/S3/Combinatorics/IsingUniquenessSets.claim` (`✓ std3`).

*Citation.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

The first conjunct is the clause that no set of uniqueness has at most k points, for every k. The second is the equality u(k, 2) = k + 1 for every k at least three. The third records u(2, 2) = 4: for k = 2 the Walsh space of degree two is the whole function space, so only the whole square is a set of uniqueness.

**Theorem 1.7 (No set of uniqueness has at most k points).**

$$(\forall k \in \mathbb{N},\; \forall U \in \operatorname{Finset}\left(\operatorname{Fin}\left(k\right) \to \operatorname{Bool}\right),\; (\operatorname{IsSetOfUniqueness}\left(k, 2, U\right)) \Rightarrow ((k) + (1) \le \operatorname{card}\left(U\right))) \land ((\forall k \in \mathbb{N},\; (3 \le k) \Rightarrow (\operatorname{minUniqueness}\left(k, 2\right) = (k) + (1))) \land (\operatorname{minUniqueness}\left(2, 2\right) = 4))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IsingUniquenessSets.result` (`✓ std3`). ∎

*Resolves.* `Problems/skalski-stroinski-2025-ising-uniqueness-sets` (proved) by `D5/S3/Combinatorics/IsingUniquenessSets.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"skalski-stroinski-2025-ising-uniqueness-sets","declaration_gid":"D5/S3/Combinatorics/IsingUniquenessSets.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Skalski, Tomasz Stroiński (2025). *Level sets and maximum likelihood estimation for the Ising model*. DOI: [10.48550/arXiv.2511.20925](https://doi.org/10.48550/arXiv.2511.20925). URL: <https://arxiv.org/abs/2511.20925v1>.

*Commentary.*

Lower bound: if U has at most k points, the evaluation map sending v in R^(k+1) to the values v_0 + sum_i v_i x_i at the points x of U has a nonzero kernel vector. The square of the affine function v_0 + sum_i v_i x_i lies in the Walsh space of degree two because every coordinate squares to one; it is nonnegative, vanishes on U, and is not identically zero, since comparing the all-plus point with the point where coordinate i is flipped forces v_i = 0 and then v_0 = 0. Upper bound for k at least three: on the Walsh space of degree two the sums over the points e_m with one plus sign, the points f_m with one minus sign, and the two constant points satisfy sum_m phi(f_m) - sum_m phi(e_m) + (k - 2)(phi(-1) - phi(1)) = 0 and sum_m phi(e_m) + sum_m phi(f_m) - (k - 4)(phi(1) + phi(-1)) = 8 2^(-k) sum_x phi(x), as each Walsh function of degree at most two checks directly. If phi is nonnegative and vanishes at the points e_m and at the all-plus point, the first identity forces phi(-1) = 0 and phi(f_m) = 0, the second then gives a zero total sum, and nonnegativity gives phi = 0; these k + 1 points form a set of uniqueness. For k = 2 the indicator of any missing point lies in the space, so only the whole square works.

## References

- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.IsSetOfUniqueness`
- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.claim`
- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.minUniqueness`
- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.result`
- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.sgn`
- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.walsh`
- Truth anchor: `D5/S3/Combinatorics/IsingUniquenessSets.walshSpace`
