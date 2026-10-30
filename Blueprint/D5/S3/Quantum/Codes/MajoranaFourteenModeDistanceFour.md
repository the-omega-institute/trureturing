# The fourteen-mode obstruction for parity Majorana codes

## Abstract

A self-orthogonal binary stabilizer space containing parity on at most fourteen modes has a logical operator of weight below four whenever twice its dimension is less than the number of modes.

**Definition 1.1 (Self-orthogonal binary stabilizer spaces).**

$$\forall (\iota: \operatorname{Type}*), ([\operatorname{Fintype}\left(\iota\right)], \forall (c: \operatorname{Submodule}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), \iota \to \operatorname{ZMod}\left((2: \mathbb{N})\right)\right)), ((\operatorname{D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.IsSelfOrthogonal}\left(c\right)) \Leftrightarrow (\forall (x: \iota \to \operatorname{ZMod}\left((2: \mathbb{N})\right)), ((x \in c) \Rightarrow (\forall (y: \iota \to \operatorname{ZMod}\left((2: \mathbb{N})\right)), ((y \in c) \Rightarrow (\operatorname{dotProduct}\left(x, y\right) = (0: \operatorname{ZMod}\left((2: \mathbb{N})\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.IsSelfOrthogonal` (`✓ std3`).

*Citation.* Mathew B. Hastings (2017). *Small Majorana fermion codes*. DOI: [10.26421/QIC17.13-14-7](https://doi.org/10.26421/QIC17.13-14-7). URL: <https://arxiv.org/abs/1703.00612v1>.

*Commentary.*

For a finite coordinate type ι, c is a binary linear subspace. It is self-orthogonal when the dot product of every x and y in c is zero in ZMod 2, including x equal to y. The dot product is the sum of the coordinate products. Thus every vector of c has even Hamming weight, and every two supports overlap in an even number of coordinates. These are the evenness and commutation conditions for Majorana stabilizers in Hastings, c.tex, lines 86–97.

**Definition 1.2 (A logical operator of weight below four).**

$$(\operatorname{D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((n \le (14: \mathbb{N})) \Rightarrow (\forall (c: \operatorname{Submodule}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left((2: \mathbb{N})\right)\right)), ((\operatorname{D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.IsSelfOrthogonal}\left(c\right)) \Rightarrow ((\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{ZMod}\left((2: \mathbb{N})\right))\right) \in c) \Rightarrow ((((2: \mathbb{N})) \cdot (\operatorname{Module.finrank}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), (c: \operatorname{Type})\right)) < n) \Rightarrow (\exists (v: \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left((2: \mathbb{N})\right)), ((v \in \operatorname{D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality.characterOrthogonalComplement}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), c\right)) \land ((\neg (v \in c)) \land (\operatorname{hammingNorm}\left(v\right) < (4: \mathbb{N})))))))))))$$

*Formalization.* `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mathew B. Hastings (2017). *Small Majorana fermion codes*. DOI: [10.26421/QIC17.13-14-7](https://doi.org/10.26421/QIC17.13-14-7). URL: <https://arxiv.org/abs/1703.00612v1>.

*Commentary.*

For every natural n at most fourteen, take any self-orthogonal binary subspace c on Fin n containing the constant-one vector. If twice its dimension is strictly less than n, there is a vector v in its character orthogonal complement, outside c, with Hamming weight below four. The character orthogonal complement here is precisely the dot-product orthogonal complement over ZMod 2. Hastings identifies the dimension of c with the number of independent stabilizers and gives the logical-qubit count as n/2 minus that dimension in c.tex, lines 91 and 99–105. Logical operators and distance are defined in lines 108–113; the requirement that the constant-one parity vector belong to c is in lines 115–117. This statement expresses the exclusion suggested for fourteen modes in lines 271–273, together with all smaller lengths. It asserts the obstruction below sixteen modes; it does not assert existence at sixteen modes.

**Theorem 1.3 (Proof of the obstruction).**

$$\forall (n: \mathbb{N}), ((n \le (14: \mathbb{N})) \Rightarrow (\forall (c: \operatorname{Submodule}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left((2: \mathbb{N})\right)\right)), ((\operatorname{D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.IsSelfOrthogonal}\left(c\right)) \Rightarrow ((\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \operatorname{ZMod}\left((2: \mathbb{N})\right))\right) \in c) \Rightarrow ((((2: \mathbb{N})) \cdot (\operatorname{Module.finrank}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), (c: \operatorname{Type})\right)) < n) \Rightarrow (\exists (v: \operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left((2: \mathbb{N})\right)), ((v \in \operatorname{D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality.characterOrthogonalComplement}\left(\operatorname{ZMod}\left((2: \mathbb{N})\right), c\right)) \land ((\neg (v \in c)) \land (\operatorname{hammingNorm}\left(v\right) < (4: \mathbb{N}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/hastings-2017-small-majorana-fourteen-mode-distance-four` (proved) by `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hastings-2017-small-majorana-fourteen-mode-distance-four","declaration_gid":"D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mathew B. Hastings (2017). *Small Majorana fermion codes*. DOI: [10.26421/QIC17.13-14-7](https://doi.org/10.26421/QIC17.13-14-7). URL: <https://arxiv.org/abs/1703.00612v1>.

*Commentary.*

Work first with an arbitrary finite coordinate type ι. Membership in the character orthogonal complement is equivalent to having zero dot product with every vector of c; symmetry of the dot product permits either order. Applying self-orthogonality to the constant-one vector twice shows that the number of coordinates is even. For distinct i and j, the vector eᵢ + eⱼ, where eᵢ = Pi.single i 1, has Hamming weight two. If this vector belongs to c, orthogonality against it forces x i = x j for every x in c.

Suppose such a pair belongs to c. Let ev be evaluation at i on c, and let res restrict the kernel of ev to the coordinates other than i and j. Vectors in this kernel vanish at both removed coordinates, so res is injective. Its range d is self-orthogonal. The sum of the constant-one vector and eᵢ + eⱼ lies in the kernel and restricts to the constant-one vector of d. Evaluation is surjective because the constant-one vector evaluates to one, so rank-nullity gives dim d + 1 = dim c. The coordinate count decreases by two. A vector v orthogonal to d but outside d extends by zero at i and j to a vector w of the same Hamming weight. For x in c, adding x i times eᵢ + eⱼ puts x in the evaluation kernel without changing its other coordinates; hence w is orthogonal to x. If w belonged to c it would lie in that kernel and restrict into d, contradicting v outside d. This is the linear-space form of the pair-removal construction in Hastings, c.tex, lines 131–139.

Next suppose that no vector eᵢ + eⱼ with i distinct from j lies in the orthogonal complement. The dimension inequality ensures that ι is nonempty. Choose i₀, evaluate c at i₀, and take a basis b of this evaluation kernel. Write k for its dimension and r a for the underlying vector of b a, with a in Fin k; then k + 1 = dim c. Associate to coordinate i the column whose a-th entry is (r a).val i. If the columns of i and j agree, their evaluations agree on the entire kernel because they agree on b. Every x in c can be moved into the kernel by adding x i₀ times the constant-one vector. Thus x i = x j for all x in c, putting eᵢ + eⱼ in the orthogonal complement. The assumption therefore makes the column map injective.

Let s be the image of this column map in the binary k-dimensional cube. Its cardinality is the number of coordinates. For any subset a of Fin k with cardinality at most two, the sum over s of the monomial consisting of the product of x i for i in a is zero in ZMod 2. Indeed, injectivity transfers that sum to a sum over coordinates. For empty a this is orthogonality of the parity vector with itself; for a singleton it is orthogonality of r b with parity; for a two-element set it is orthogonality of the two corresponding vectors r b and r d.

To use these moment equations, let f be any binary-valued function on the binary k-dimensional cube. For each subset a of Fin k, define q a to be the sum over y of f y times the product of y i over coordinates outside a. Then f x is the sum over all a of q a times the product of x i + 1 over i in a. To prove this expansion, the product over all coordinates of x i + 1 + y i equals one when y = x and zero otherwise. Multiplying by f y, summing over y, expanding the product, and exchanging the finite sums gives the asserted coefficients. If k is at least three and all moments of degrees at most two vanish, q a vanishes whenever the cardinality of a exceeds k − 3: its complementary product then has degree at most two.

If all coefficients of degree greater than one vanish, this expansion makes f affine. Expanding its constant and singleton terms gives f(x + u) + f x = f u + f 0. A constant f has Hamming weight zero or 2ᵏ. Otherwise choose u with f u different from f 0. The displayed identity gives f(x + u) = f x + 1. Translation by u is a bijection exchanging the zero and nonzero values, so twice the Hamming weight of f is 2ᵏ.

If instead all coefficients of degree greater than two vanish, expand the constant, singleton and pair terms to obtain additivity in x of b u x = f(x + u) + f x + f u + f 0. Use the integer-valued additive character χ on ZMod 2 with χ(0) = 1 and χ(1) = −1. For each u the character sum of χ(b u x) over x is zero or 2ᵏ, according as this character is nontrivial or trivial. Squaring the sum of χ(f x) and changing variables from the pair (x,y) to (x,x + u) expresses the square as the sum over u of χ(f u + f 0) times the sum over x of χ(b u x). Consequently 2ᵏ divides this integer square.

At k = 5, write w for the integer sum with summand one when f x = 0 and minus one otherwise. The preceding divisibility is 32 dividing w squared. Passing to the natural absolute value and using prime factorization yields 8 dividing w. Counting the nonzero values gives w = 32 − 2 times the integer cast of the Hamming weight of f. It follows that 4 divides that integer cast, and hence that 4 divides the natural Hamming weight.

Apply these facts to f equal to one on s and zero elsewhere; its Hamming weight is the cardinality of s. The inequalities k ≤ 5, 2(k + 1) < |s| ≤ 14 and |s| ≤ 2ᵏ exclude k at most three, leaving k = 4 or k = 5. The moment expansion has degree at most k − 3. At k = 4 the affine weight alternatives are 0, 8 and 16, all incompatible with 10 < |s| ≤ 14. At k = 5, evenness and 12 < |s| ≤ 14 force |s| = 14, contradicting divisibility by four.

If c contains no weight-two vector but every vector of the orthogonal complement outside c has weight at least four, the orthogonal complement contains no eᵢ + eⱼ with distinct i and j. The injective column construction then gives s with all the preceding properties: k + 1 = dim c and |s| = |ι| supply the dimension and size bounds, while self-orthogonality and parity supply the moments and evenness. The contradiction proves the desired short vector whenever c contains no weight-two vector.

Finally use strong induction on the number of coordinates. If c contains eᵢ + eⱼ for distinct i and j, the space d obtained by removing that pair has two fewer coordinates, one less dimension, and the same strict inequality between twice its dimension and its coordinate count. It remains self-orthogonal and contains parity, so induction gives a short vector orthogonal to d but outside d. Extension by zero gives the required vector for c. If there is no such pair in c, the preceding contradiction applies. Specializing the coordinate type to Fin n, whose cardinality is n, proves the stated assertion for every n at most fourteen.

## References

- Truth anchor: `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.IsSelfOrthogonal`
- Truth anchor: `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.claim`
- Truth anchor: `D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour.result`
- Dependency: [D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality](../../Fourier/CharacterSelection/BinaryCharacterCodeDuality.md)
