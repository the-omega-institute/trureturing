# Exact dual coherence for a rank-two three-column frame

## Abstract

A rank-two frame with three columns has an explicit dual attaining the exact smallest off-diagonal cross-Gram magnitude. Full support of its null vector forces uniqueness over either scalar field.

The cross-Gram convention is C = F*G, with C(i,j) = sum over r of conjugate(F(r,i)) G(r,j). Duality means FG* = I. Taking adjoints gives GF* = I. Thus both column families span the two-dimensional space. With Mathlib's convention, reconstruction uses the coefficient inner(G(i),x), which is linear in x. The frame and coherence terminology is that of Aceska and Kaczanowski; the exact minimization and uniqueness statements below are separate mathematical deductions.

**Definition 1.1 (Actual dual matrices).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall F \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; \forall G \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {Dual}\left(F, G\right)) \Leftrightarrow (F \cdot \operatorname {conjTranspose}\left(G\right) = 1)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.Dual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

The identity includes every entry of the two by two product. No symmetry, canonicality or unit-norm condition is imposed.

**Definition 1.2 (Cross-Gram orientation).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall F \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; \forall G \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; \operatorname {crossGram}\left(F, G\right) = \operatorname {conjTranspose}\left(F\right) \cdot G$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.crossGram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

The first family is conjugated. The matrix has three rows and three columns.

**Definition 1.3 (Six ordered off-diagonal entries).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall C \in \operatorname {Matrix}\left(\operatorname {Fin}\left(3\right), \operatorname {Fin}\left(3\right), K\right),\; \operatorname {coherence}\left(C\right) = \max_{i, j: \operatorname {Fin}\left(3\right), i \ne j} \left\lVert \operatorname {entry}\left(C, i, j\right) \right\rVert$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.coherence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

The finite maximum uses nonnegative norms and is then coerced to the reals. All six ordered off-diagonal entries participate; no diagonal entry or assumed Hermitian symmetry is used.

**Definition 1.4 (Null-vector support).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall u \in \operatorname {Fin}\left(3\right) \to K,\; \operatorname {support}\left(u\right) = \{i: \operatorname {Fin}\left(3\right) \mid \operatorname {apply}\left(u, i\right) \ne 0\}$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.support` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

This is the finite set of indices i with u(i) different from zero.

**Definition 1.5 (Magnitudes away from one coordinate).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall u \in \operatorname {Fin}\left(3\right) \to K,\; \forall i \in \operatorname {Fin}\left(3\right),\; \operatorname {weight}\left(u, i\right) = \max_{j: \operatorname {Fin}\left(3\right), j \ne i} \left\lVert \operatorname {apply}\left(u, j\right) \right\rVert$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

The weight m(i) is the largest magnitude of the other two coordinates. At least two nonzero coordinates make every weight positive.

**Definition 1.6 (The reciprocal denominator).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall u \in \operatorname {Fin}\left(3\right) \to K,\; \operatorname {total}\left(u\right) = \sum_{i: \operatorname {Fin}\left(3\right)} \frac{\left\lVert \operatorname {apply}\left(u, i\right) \right\rVert}{\operatorname {weight}\left(u, i\right)}$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.total` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

A zero numerator contributes zero when at least two coordinates are nonzero. The singleton case is treated separately rather than using division by zero as a minimization argument.

**Definition 1.7 (The rank-one correction).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall u \in \operatorname {Fin}\left(3\right) \to K,\; \forall v \in \operatorname {Fin}\left(3\right) \to K,\; \operatorname {gram}\left(u, v\right) = 1 - \operatorname {vecMulVec}\left(v, \operatorname {star}\left(u\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.gram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

For a normalized parameter v, the cross-Gram matrix is I minus v u*. It is an oblique projection, without a self-adjointness requirement.

**Definition 1.8 (Explicit actual-dual reconstruction).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall F \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; \forall C \in \operatorname {Matrix}\left(\operatorname {Fin}\left(3\right), \operatorname {Fin}\left(3\right), K\right),\; \operatorname {reconstruct}\left(F, C\right) = \operatorname {inv}\left(F \cdot \operatorname {conjTranspose}\left(F\right)\right) \cdot F \cdot C$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Rank two makes FF* nonsingular. The inverse here is the ordinary matrix inverse on that hypothesis.

**Definition 1.9 (An optimizer with the zero convention).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall u \in \operatorname {Fin}\left(3\right) \to K,\; \forall i \in \operatorname {Fin}\left(3\right),\; \operatorname {apply}\left(\operatorname {optimalParameter}\left(u\right), i\right) = \operatorname {ite}\left(\operatorname {apply}\left(u, i\right) = 0, 0, \operatorname {ofReal}\left(\frac{\operatorname {inv}\left(\operatorname {total}\left(u\right)\right)}{\operatorname {weight}\left(u, i\right)}\right) \cdot \frac{\operatorname {apply}\left(u, i\right)}{\operatorname {ofReal}\left(\left\lVert \operatorname {apply}\left(u, i\right) \right\rVert\right)}\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.optimalParameter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

For a nonzero coordinate, v(i) = (T/m(i)) u(i)/norm(u(i)), where T is the inverse of total(u). Real factors are embedded in K. For a zero coordinate, v(i) is zero.

**Theorem 1.10 (All duals and the converse construction).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall F \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {rank}\left(F\right) = 2) \Rightarrow (\forall u \in \operatorname {Fin}\left(3\right) \to K,\; (u \ne 0) \Rightarrow ((\operatorname {mulVec}\left(F, u\right) = 0) \Rightarrow (\forall G \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {Dual}\left(F, G\right)) \Leftrightarrow (\exists v \in \operatorname {Fin}\left(3\right) \to K,\; (\operatorname {dotProduct}\left(\operatorname {star}\left(u\right), v\right) = 1) \land ((\operatorname {crossGram}\left(F, G\right) = \operatorname {gram}\left(u, v\right)) \land (G = \operatorname {reconstruct}\left(F, \operatorname {gram}\left(u, v\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.dual_parameterization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

The kernel of F is the span of any nonzero null vector u, by rank-nullity. For a dual, every column of I minus G*F lies in this kernel. Taking adjoints gives C = I minus v u*, and u*C = 0 gives u*v = 1. Conversely, a normalized v yields the displayed reconstructed matrix, whose cross-Gram is C and whose two reconstruction identities hold. Multiplication by F* is injective, so the cross-Gram determines the actual dual.

**Theorem 1.11 (Attainment and full-support uniqueness).**

$$\forall K \in \operatorname {Type},\; [\operatorname {RCLike}\left(K\right)] \forall F \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {rank}\left(F\right) = 2) \Rightarrow (\forall u \in \operatorname {Fin}\left(3\right) \to K,\; (u \ne 0) \Rightarrow ((\operatorname {mulVec}\left(F, u\right) = 0) \Rightarrow (\exists G \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {Dual}\left(F, G\right)) \land ((\operatorname {span}\left(K, \operatorname {range}\left(\operatorname {col}\left(F\right)\right)\right) = \operatorname {top}) \land ((\operatorname {span}\left(K, \operatorname {range}\left(\operatorname {col}\left(G\right)\right)\right) = \operatorname {top}) \land (((\operatorname {card}\left(\operatorname {support}\left(u\right)\right) = 1) \Rightarrow (\operatorname {coherence}\left(\operatorname {crossGram}\left(F, G\right)\right) = 0)) \land (((2 \le \operatorname {card}\left(\operatorname {support}\left(u\right)\right)) \Rightarrow ((\forall i \in \operatorname {Fin}\left(3\right),\; 0 < \operatorname {weight}\left(u, i\right)) \land ((0 < \operatorname {total}\left(u\right)) \land ((G = \operatorname {reconstruct}\left(F, \operatorname {gram}\left(u, \operatorname {optimalParameter}\left(u\right)\right)\right)) \land (\operatorname {coherence}\left(\operatorname {crossGram}\left(F, G\right)\right) = \operatorname {inv}\left(\operatorname {total}\left(u\right)\right)))))) \land ((\forall H \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {Dual}\left(F, H\right)) \Rightarrow (\operatorname {coherence}\left(\operatorname {crossGram}\left(F, G\right)\right) \le \operatorname {coherence}\left(\operatorname {crossGram}\left(F, H\right)\right))) \land ((\forall i \in \operatorname {Fin}\left(3\right),\; \operatorname {apply}\left(u, i\right) \ne 0) \Rightarrow (\forall H \in \operatorname {Matrix}\left(\operatorname {Fin}\left(2\right), \operatorname {Fin}\left(3\right), K\right),\; (\operatorname {Dual}\left(F, H\right)) \Rightarrow ((\operatorname {coherence}\left(\operatorname {crossGram}\left(F, H\right)\right) \le \operatorname {coherence}\left(\operatorname {crossGram}\left(F, G\right)\right)) \Rightarrow (H = G))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.rank_two_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

For support of size two or three, write a(i) = norm(u(i)), m(i) = weight(u,i), and S = sum a(i)/m(i). The off-diagonal entries are minus v(i) conjugate(u(j)), so each m(i) norm(v(i)) is bounded by coherence. Normalization gives 1 <= sum a(i) norm(v(i)) <= coherence times S, proving the lower bound S inverse. The displayed optimalParameter is normalized and attains that bound. If all coordinates are nonzero, the sum of the gaps between each weighted bound and the real part of conjugate(u(i))v(i) is zero. Each gap is nonnegative, so every gap vanishes. Equality of real part and norm forces a nonnegative real phase, and cancellation of each nonzero conjugate(u(i)) fixes v(i). Injectivity of multiplication by F* then fixes G. If the support is the singleton r, take v(r) = inverse(conjugate(u(r))) and every other coordinate zero. Its cross-Gram is diagonal with entry zero at r and one elsewhere, hence its coherence is zero. A nonzero u excludes empty support. No converse claiming that full support is necessary for uniqueness is asserted.

## Application: real Euclidean unit columns and the full equality case

Let F be any real 2 by 3 matrix of rank two, with columns f(1), f(2), f(3) satisfying sum over r = 1,2 of F(r,i)^2 = 1 for each i. These are Euclidean unit columns in the real plane: in Lean this means EuclideanSpace R (Fin 2), or the explicit sum-of-squares condition, rather than the default supremum norm on raw Fin 2 functions. Let G range over every real 2 by 3 matrix satisfying FGᵀ = I(2). Write mu(F,G) for the maximum of |(FᵀG)(i,j)| over all six ordered pairs i different from j. No norm, symmetry, equal-diagonal, sign or canonicality hypothesis is imposed on G. Transposition gives GFᵀ = I(2), so these are actual dual frames with both reconstruction identities.

For every such F and every such actual dual G, the application gives the sharp bound and the following complete equality characterization:

$$
\frac{1}{3} \le \operatorname {coherence}\left(\operatorname {crossGram}\left(F, G\right)\right)
$$

$$
(\operatorname {coherence}\left(\operatorname {crossGram}\left(F, G\right)\right) = \frac{1}{3}) \Leftrightarrow ((F \cdot \operatorname {transpose}\left(F\right) = \frac{3}{2} \cdot \operatorname {identity}\left(2\right)) \land (G = \frac{2}{3} \cdot F))
$$

The argument applies the existing frozen `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.rank_two_minimum` and `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.dual_parameterization` to K = R. Their source is CrossFrameRankTwoMinimum.lean at revision 7767e9e94e8aece1b1661dc4a9ddad628ad3f55e, source blob dab79b802b7e45d4339fb65ff9b8b966353fc28f, with mathlib pinned to 56a005855ea17e0b0958f73ec801ae140b0a1679. The frozen result supplies exact optimization, actual attainment and full-support uniqueness. The unit-column geometry and equality classification are derived below as a source-level application; they are not a separately declared Lean theorem in this module.

Choose a nonzero real null vector u by rank-nullity; the kernel has dimension one. Singleton support would give u(i) f(i) = 0 for a nonzero u(i), contradicting the unit column condition. Thus support has size two or three. Put w(i) = max over j different from i of |u(j)| and S = sum over i of |u(i)|/w(i), exactly weight and total above. Every w(i) and S are positive. Rescaling u by a nonzero scalar multiplies every magnitude and weight by the same positive factor; S is unchanged. Coordinate signs and a simultaneous relabelling of columns and null coordinates also leave S unchanged. Specializing rank_two_minimum now supplies an actual dual H attaining coherence 1/S and proves mu(F,G) >= 1/S for every actual G. This is a minimum over reconstructed matrices, not merely an infimum over abstract cross-Gram parameters.

If support has size two, say at i and j, then u(i) f(i) = -u(j) f(j). Taking Euclidean norms gives |u(i)| = |u(j)| = t > 0. All three weights equal t, including the weight at the zero coordinate. Hence S = 2 and the attained minimum is exactly 1/2. Conversely, a collinear pair of unit columns gives such a relation; rank two places the remaining column off that line, and nullity one fixes the same support for every nonzero null vector. No uniqueness assertion from the full-support clause is used in this case.

For full support, relabel the magnitudes as 0 < a <= b <= c and set x(i) = sign(u(i)) f(i). The x(i) are real Euclidean unit vectors and a x(1) + b x(2) + c x(3) = 0. Thus c = norm(a x(1) + b x(2)) <= a+b. Equality c = a+b would give (a+b)^2 = a^2+b^2+2ab inner(x(1),x(2)), so inner(x(1),x(2)) = 1. Then norm(x(1)-x(2))^2 = 2-2 = 0, and x(1) = x(2). The dependence forces x(3) = -x(1). Undoing the signs and relabelling makes all columns collinear, contrary to rank two. Consequently c < a+b.

The excluded-coordinate maxima are (c,c,b), also when magnitudes tie. Therefore the exact denominator and rational identity are:

$$
S = \frac{a + b}{c} + \frac{c}{b}
$$

$$
3 - S = \frac{b - a}{b} + \frac{\left(c - b\right) \cdot \left(a + b - c\right)}{b \cdot c}
$$

Both summands in 3-S are nonnegative. Their sum vanishes only if b = a and then c = b, since a+b-c > 0; conversely a = b = c gives S = 3. Together with support two, this proves 0 < S <= 3, with S = 3 exactly when all three magnitudes |u(i)| are equal and positive. The strict triangle is essential: the excluded scalar boundary a = b, c = a+b would also give S = 3. For every actual dual, mu(F,G) >= 1/S >= 1/3. In full support with unequal magnitudes the attained minimum is strictly greater than 1/3; in full support the minimizing actual dual is unique by the frozen result.

Suppose now an actual G has mu(F,G) = 1/3. The preceding inequalities force S = 3. Write u = t s with t > 0 and each s(i) equal to +1 or -1, so Fs = 0. The unit vectors h(i) = s(i) f(i) sum to zero. For distinct i,j and the remaining index k, h(i)+h(j) = -h(k); squaring gives inner(h(i),h(j)) = -1/2. Hence the signed equilateral Gram identity is:

$$
\operatorname {transpose}\left(F\right) \cdot F = \frac{3}{2} \cdot \operatorname {identity}\left(3\right) - \frac{1}{2} \cdot \operatorname {vecMulVec}\left(s, s\right)
$$

Multiplying on the left by F and using Fs = 0 yields (FFᵀ)F = (3/2)F. Rank two makes F surjective onto the real plane, so FFᵀ = (3/2)I(2). Thus C = (2/3)F is an actual dual and is the canonical dual (FFᵀ)⁻¹F. Its cross-Gram is:

$$
\operatorname {transpose}\left(F\right) \cdot \frac{2}{3} \cdot F = \operatorname {identity}\left(3\right) - \frac{1}{3} \cdot \operatorname {vecMulVec}\left(s, s\right)
$$

Every one of its six ordered off-diagonal entries has absolute value 1/3. To identify the given actual matrix G, take the minimizing actual H supplied above. Both C and G have coherence equal to that of H. All coordinates of u are nonzero, so the actual-matrix uniqueness clause of rank_two_minimum gives C = H and G = H. Therefore G = (2/3)F. Uniqueness of a cross-Gram parameter alone is not being substituted for uniqueness of the dual matrix.

Conversely, assume FFᵀ = (3/2)I(2). Then P = (2/3)FᵀF is symmetric, acts as the identity on the two-dimensional range of Fᵀ, and vanishes on ker(F). Indeed P(Fᵀy) = Fᵀy and Pv = 0 whenever Fv = 0. The orthogonal decomposition of the real three-dimensional space as range(Fᵀ) plus ker(F) therefore gives P = I(3)-vvᵀ for a Euclidean unit vector v spanning ker(F). On the diagonal, unit column norms give P(i,i) = 2/3, hence v(i)^2 = 1/3 for every i. Set s = sqrt(3) v. Then s(i) is +1 or -1 and Fs = 0. The signed equilateral calculation above applies again. If G = (2/3)F, it is an actual dual and its cross-Gram is I(3)-(1/3)ssᵀ, so its coherence is exactly 1/3. This proves the other direction of the displayed equivalence. It also shows that tightness, a null vector of equal positive coordinate magnitudes, and a signed equilateral triple are equivalent within this domain. In the tight case the minimizing actual dual is uniquely (2/3)F.

Sharpness is realized exactly by the matrix with rows (1,-1/2,-1/2) and (0,sqrt(3)/2,-sqrt(3)/2). Each squared column norm is 1, the determinant of its first two columns is sqrt(3)/2 and is nonzero, its frame operator is (3/2)I(2), and F(1,1,1)ᵀ = 0. With G = (2/3)F, FGᵀ = I(2) and FᵀG has diagonal entries 2/3 and all six off-diagonal entries -1/3. This is an exact equality pair.

Aceska and Kaczanowski's Cross-Frame Potential supplies the frame, dual and coherence terminology and the equilateral tight-frame illustration in Example 5; see `D5/L/QuantumBounds/aceska2022crossframe`. Their Lemma 33 assumes equal diagonal pairings, which are not assumed for arbitrary G here. This application concerns every real Euclidean unit-column rank-two 2 by 3 frame and all its actual duals. The real inner-product and sign argument does not establish an equality classification for arbitrary complex frames. It neither settles the paper's unrestricted Conjecture 41, already refuted in the separate non-unit example, nor claims priority, a new named conjecture settlement, or any conclusion for the wider 2 by 4 and 3 by 5 residuals.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.Dual`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.coherence`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.crossGram`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.dual_parameterization`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.dual_parameterization`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.gram`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.optimalParameter`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.rank_two_minimum`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.rank_two_minimum`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.reconstruct`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.support`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.total`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.weight`
