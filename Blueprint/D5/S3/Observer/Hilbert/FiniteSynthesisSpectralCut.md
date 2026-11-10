# Finite Synthesis Spectral Cut

## Abstract

Finite synthesis into an arbitrary complex Hilbert space admits a data-selected positive spectral cut.

E is any finite-dimensional complex inner-product space, n = dim E, and H is any complete complex Hilbert space, with no dimension or separability restriction. T is continuous and complex-linear. Singular values and right singular vectors are those of T with codomain restricted to its actual finite range. Indexing is zero-based. sourceCut(T,k) spans right singular vectors with index at most k; imageCut(T,k) is its image in the original H. P denotes the canonical orthogonal projection. No column independence, preassigned gap or Gram inverse is assumed.

**Theorem 1.1 (Selected spectral cut).**

$$\forall T:E\to _{\mathbb{C}}H, (\exists z\in E, \Vert z\Vert =1\land 1\le \Vert Tz\Vert )\Rightarrow \forall eta\in \mathbb{R}, 0< eta< 1\Rightarrow \exists k\in \operatorname{Fin}(n), (eta)^{n-1}\le \operatorname{singular}(T, k)\land \operatorname{singular}(T, k+1)\le eta\operatorname{singular}(T, k)\land 1\le \operatorname{dim}(\operatorname{imageCut}(T, k))\le n\land (\forall z\in \operatorname{sourceCut}(T, k), \operatorname{singular}(T, k)\Vert z\Vert \le \Vert Tz\Vert )\land (\forall z\in E, P_{\operatorname{imageCut}(T, k)}Tz=TP_{\operatorname{sourceCut}(T, k)}z)\land (\forall z\in E, \Vert Tz-P_{\operatorname{imageCut}(T, k)}Tz\Vert \le \operatorname{singular}(T, k+1)\Vert z\Vert )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut.exists_spectral_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first geometric singular-value gap is selected by finite search. Preceding failures of the gap inequality yield a positive lower bound. The Gram eigenbasis separates the source cut from its orthogonal complement, giving the exact ambient projection and tail bound.

**Theorem 1.2 (Uniform intertwining leakage).**

$$\forall T:E\to _{\mathbb{C}}H, (\exists z\in E, \Vert z\Vert =1\land 1\le \Vert Tz\Vert )\Rightarrow \forall eta\in \mathbb{R}, 0< eta< 1\Rightarrow \exists k\in \operatorname{Fin}(n), 1\le \operatorname{dim}(\operatorname{imageCut}(T, k))\le n\land \operatorname{Orthonormal}(\operatorname{cutFrame}(T, k))\land \forall U:H\to H, M:E\to E, y\in \operatorname{imageCut}(T, k), \Vert Uy-P_{\operatorname{imageCut}(T, k)}Uy\Vert \le (eta\Vert M\Vert +((eta)^{n-1})^{-1}\Vert UT-TM\Vert )\Vert y\Vert $$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut.exists_cut_intertwining_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U and M are arbitrary continuous complex-linear operators on H and E, respectively. The same cut works for all of them. cutFrame is the normalized ambient image of each selected right singular vector, indexed by the finite interval of indices at most k. The precise splitting UT = TM + (UT − TM) is estimated after projection onto the orthogonal complement. The lower singular bound is applied only on the selected source subspace. This is an operator-norm leakage estimate; it does not by itself establish C117 Lemma 46.2 or its exact braid residual identities.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut.exists_cut_intertwining_bound`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut.exists_spectral_cut`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](FiniteMoorePenroseInverse.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../SpectralTopology/HermitianEigenvaluePerturbation.md)
