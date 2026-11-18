# Unit remote delays with arbitrary history length

## Abstract

Unit remote delays turn the spectral radius of a real zero-diagonal block matrix into its square root, independently of unused older history slots.

There are ell positive-sized blocks, with ell positive and size n(i) in block i. The coordinate type Vtx n is the dependent sum of Fin (n(i)) over i in Fin ell; Sigma.fst extracts the block index. N is an arbitrary real matrix on these coordinates. Its entire diagonal blocks vanish: N(p,q)=0 whenever p and q have the same block index. No sign, symmetry, rank or irreducibility hypothesis is imposed on the other blocks.

The natural-valued array delta is constant in time and is indexed from source block to destination block. Every remote entry is a positive integer at most one, hence equals one. Local entries are unrestricted: their coefficients belong to zero diagonal blocks and cannot affect the update. In particular, the convention with every local delay zero is included. For any K at least one, asyncMatrix N delta K acts on all slots in Fin (K+1) times Vtx n, with slot zero newest. Its newest slot is N applied to slot one, and each older slot copies its immediate predecessor. K is not required to equal one.

**Theorem 1.1 (The exact square-root radius for every admissible history).**

$$\forall (ell: \mathbb{N}), ((0 < ell) \to (\forall (n: (\operatorname{Fin}\left(ell\right)) \to (\mathbb{N})), ((\forall (i: \operatorname{Fin}\left(ell\right)), (0 < n\left(i\right))) \to (\forall (N: \operatorname{Matrix}\left(\operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \mathbb{R}\right)), (\forall (delta: (\operatorname{Fin}\left(ell\right)) \to ((\operatorname{Fin}\left(ell\right)) \to (\mathbb{N}))), ((\forall (p: \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right)), (\forall (q: \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right)), ((\operatorname{Sigma.fst}\left(p\right) = \operatorname{Sigma.fst}\left(q\right)) \to (N\left(p, q\right) = 0)))) \to ((\forall (i: \operatorname{Fin}\left(ell\right)), (\forall (j: \operatorname{Fin}\left(ell\right)), ((i \ne j) \to ((1 \le delta\left(i, j\right)) \land (delta\left(i, j\right) \le 1))))) \to (\forall (K: \mathbb{N}), ((1 \le K) \to (\forall (lambda: \mathbb{R}), ((0 < lambda) \to ((lambda < 1) \to ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(N\right) = \operatorname{ENNReal.ofReal}\left(lambda\right)) \to ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.asyncMatrix}\left(N, delta, K\right)\right) = \operatorname{ENNReal.ofReal}\left(\operatorname{Real.sqrt}\left(lambda\right)\right)) \land (\operatorname{ENNReal.ofReal}\left(\operatorname{Real.sqrt}\left(lambda\right)\right) < 1)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AsynchronousUniformOneDelay.whole_uniform_one_delay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here radius is the spectral radius of the complexification of the actual real matrix, valued in the extended nonnegative reals. ENNReal.ofReal embeds the displayed nonnegative real values; Real.sqrt denotes the nonnegative square root. Thus the first conclusion is an exact equality for the actual history matrix, not merely an upper bound or a convergence criterion.

For a nonzero complex spectral value z of the history matrix, the shift rows force slot s of an eigenvector to be z to the negative s power times its newest slot u. The newest slot cannot vanish, since then every history slot would vanish. The update row gives z u = z inverse times N u, so N u = z squared times u. Conversely, any nonzero eigenvector of N with eigenvalue z squared lifts to the actual history by this same formula for every slot from zero through K. This proves the nonzero spectral correspondence for every K, without discarding the older coordinates.

Every history spectral value therefore has squared modulus at most lambda. A spectral value of N attaining its positive spectral radius has a complex square root, which lifts to a history spectral value of modulus square root of lambda. The two bounds give equality. Additional zero spectral values have no effect on this positive radius. Since lambda is strictly between zero and one, its square root is also less than one. No assertion about algebraic multiplicities, nonconstant delay schedules, or minimal block counts is made.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousUniformOneDelay.whole_uniform_one_delay`
- Dependency: [D5/S3/Quantum/Matrix/AsynchronousTwoBlockRadius](AsynchronousTwoBlockRadius.md)
