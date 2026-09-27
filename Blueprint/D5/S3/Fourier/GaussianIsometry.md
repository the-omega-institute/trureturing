# A common Gaussian realization of a real Hilbert space

## Abstract

Every complete real Hilbert space has an isometric realization by jointly centered Gaussian random variables on one product probability space.

**Theorem 1.1 (The Gaussian isometry).**

$$\forall u \in \operatorname{UniverseLevel}\left(\right),\; \forall H \in \operatorname{Type}\left(u\right),\; \left(\operatorname{NormedAddCommGroup}\left(H\right) \land \left(\operatorname{InnerProductSpace}\left(\mathbb{R}, H\right) \land \operatorname{CompleteSpace}\left(H\right)\right)\right) \Rightarrow \left(\exists iota \in \operatorname{Type}\left(u\right),\; \exists W \in \operatorname{LinearIsometry}\left(\mathbb{R}, H, \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{infinitePi}\left((i:iota\mapsto \operatorname{gaussianReal}\left(0, 1\right))\right)\right)\right),\; \left(\forall h \in H,\; \operatorname{HasLaw}\left((omega:\operatorname{Function}\left(iota, \mathbb{R}\right)\mapsto \operatorname{representative}\left(W(h)\right)(omega)), \operatorname{gaussianReal}\left(0, \operatorname{toNNReal}\left(\operatorname{norm}\left(h\right)^{2}\right)\right), \operatorname{infinitePi}\left((i:iota\mapsto \operatorname{gaussianReal}\left(0, 1\right))\right)\right)\right) \land \left(\operatorname{IsGaussianProcess}\left((h:H\mapsto (omega:\operatorname{Function}\left(iota, \mathbb{R}\right)\mapsto \operatorname{representative}\left(W(h)\right)(omega))), \operatorname{infinitePi}\left((i:iota\mapsto \operatorname{gaussianReal}\left(0, 1\right))\right)\right) \land \left(\forall h \in H,\; \forall k \in H,\; \operatorname{covariance}\left((omega:\operatorname{Function}\left(iota, \mathbb{R}\right)\mapsto \operatorname{representative}\left(W(h)\right)(omega)), (omega:\operatorname{Function}\left(iota, \mathbb{R}\right)\mapsto \operatorname{representative}\left(W(k)\right)(omega)), \operatorname{infinitePi}\left((i:iota\mapsto \operatorname{gaussianReal}\left(0, 1\right))\right)\right) = \operatorname{inner}\left(h, k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GaussianIsometry.exists_gaussian_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be any complete real inner product space. There are an index type of the same universe as H and a real linear isometry W from H into L2 of the product of standard real Gaussian measures indexed by that type. No separability, finite dimension, or nonzero dimension is required.

For every h, the representative of W(h) has centered Gaussian law with variance equal to the squared norm of h. The whole family is a Gaussian process: every finite subfamily has a joint Gaussian law. For all h and k its covariance is their real inner product. All these statements use the same product measure and the same map W. Linearity holds in L2, so identities between representatives hold almost everywhere for each fixed finite relation.

Choose a Hilbert basis and use the independent coordinate variables of the product measure as an orthonormal family in L2. The orthogonal series isometry extends their finite linear combinations to the entire Hilbert space. The centered Gaussian law with variance equal to squared norm is closed under L2 limits, as follows from convergence in distribution and characteristic functions. Finite Gaussian sums therefore give the law of every image vector. Linearity then gives joint Gaussianity, and the L2 inner product gives the covariance.

For a real L2 space with a control measure, this is the common isonormal process acting on all square-integrable real test functions. For a finite control measure, applying that one map to cosine and negative sine tests defines the two components of a complex Fourier coordinate. The theorem concerns L2 random variables and their joint laws; continuous sample versions, differentiability, and convergence of a prescribed data sequence require further results.

## References

- Truth anchor: `D5/S3/Fourier/GaussianIsometry.exists_gaussian_isometry`
