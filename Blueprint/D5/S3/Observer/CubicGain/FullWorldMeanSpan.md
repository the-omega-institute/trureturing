# Full Original World Mean Span

## Abstract

The unrestricted original world mean family affinely spans all seventeen real coordinates.

An original world consists of one program matrix P=[[r,b],[c,1-r]], one whole polynomial g(t)=a₀+a₁t+a₂t²+a₃t³, and one real drift d. Its complete domain has 0<r<1, b>0, c>0, bc=r(1-r), and g not identically zero. There are no bounds or history equations. Every degree from zero to three, zero samples, repeated roots and zero drift remain included.

The native carrier OriginalWorld stores (r,b,d,a) in ordinary coefficient order. FullWorld requires precisely the strict r,b conditions and originalPolynomial W≠0. Since b>0, the source equation forces c=r(1-r)/b; conversely this value is positive and satisfies bc=r(1-r). Thus sourceMatrix gives exactly every source program, and Polynomial.ofFn 4 a gives exactly its whole polynomial. The coefficient map is injective, so nonzero means that the four coefficients are not all zero. Gain here names the four-coordinate type; these coordinates are ordinary coefficients, rather than the sample values used in gainPoly.

Column vectorization is vec(X)=(X₁₁,X₂₁,X₁₂,X₂₂). The native mean uses the same sourceMatrix in every coefficient block. Coordinates are numbered 0 through 16: coordinate 0 is d and coordinate 1+4k+j is a_k vec(P)_j, for k,j from 0 through 3. Write P(W), d(W) and a(W,k) for these components, and let the calligraphic W denote this complete domain. Let M be its image under the mean.

$\forall W \in \mathcal{W}, m_{W}=(\operatorname{d}\left(W\right),\operatorname{vec}\left(\operatorname{a}\left(W, 0\right)\operatorname{P}\left(W\right)\right),\operatorname{vec}\left(\operatorname{a}\left(W, 1\right)\operatorname{P}\left(W\right)\right),\operatorname{vec}\left(\operatorname{a}\left(W, 2\right)\operatorname{P}\left(W\right)\right),\operatorname{vec}\left(\operatorname{a}\left(W, 3\right)\operatorname{P}\left(W\right)\right)) \in \mathbb{R}^{17}$

Choose source programs with (r,b,c) equal to (1/4,1/8,3/2), (1/4,1/6,9/8), (1/4,1/4,3/4), and (1/3,1/8,16/9), in that order. All are legal. Let A have their column-vectorizations as columns. Its determinant is 1/768, so its columns span the full four-coordinate block.

$\operatorname{det}\left(A\right)=\frac{1}{768}$

**Theorem 1.1 (Full unrestricted affine span).**

$$\operatorname{aff}_{\mathbb{R}}(M)=\mathbb{R}^{17}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/FullWorldMeanSpan.full_world_mean_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a coefficient index k. The worlds with g(t)=t^k and d=0 give the four program vectors in that block. Differences relative to the first program have trace zero because every program has trace one. The difference between g(t)=2t^k and g(t)=t^k at the first program gives its absolute block vector. Every polynomial in these pairs is nonzero. Adding this vector to the three program differences yields all four columns; invertibility of A therefore places every vector in this block in the direction of the affine hull. This holds separately for all four k, while each individual world still has one common P.

Keeping P and g fixed and changing only d gives an arbitrary drift direction. Any vector in the literal seventeen-coordinate space decomposes into this drift vector and its four four-coordinate blocks. Thus the direction of the nonempty affine hull is the whole space, and the affine hull itself is the whole space. No zero-polynomial world is introduced.

This is an exact statement about the complete deterministic mean family. It asserts no equality of Gaussian laws, instrument realization, observation procedure, statistical limit, physical mode count or optimal carrier dimension.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/FullWorldMeanSpan.full_world_mean_span`
- Dependency: [D5/S3/Observer/CubicGain/OriginalWorld](OriginalWorld.md)
