# A dual-frame counterexample to the cross-Gramian Welch bound

## Abstract

A spanning family of three nonzero vectors in the real plane and its dual have cross-Gramian coherence 3/19, below the proposed Welch bound 1/3.

**Definition 1.1 (Finite-dimensional frames).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (\operatorname{IsFrame}\left(F\right)) \Leftrightarrow (\operatorname{span}\left(\mathbb{R}, \operatorname{range}\left(F\right)\right) = \operatorname{top})$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsFrame` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Definition 1 (arXiv:2205.05613v3, p. 3) defines a frame by positive lower and finite upper bounds for the sum of squared analysis coefficients. The source then states verbatim: "In a finite-dimensional space H, frames are simply spanning sets of H." IsFrame uses this characterization: the real linear span of the range of F is the whole Euclidean space. Fin k indexes the k vectors from zero, and EuclideanSpace R (Fin n) is the standard real n-dimensional Hilbert space. The condition k >= n is supplied in claim.

**Definition 1.2 (Both dual reconstruction equations).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (\operatorname{IsDualFrame}\left(F, G\right)) \Leftrightarrow ((\operatorname{IsFrame}\left(G\right)) \land ((\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i: \operatorname{Fin}\left(k\right)} \langle x, \operatorname{G}\left(i\right) \rangle \cdot \operatorname{F}\left(i\right) = x) \land (\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i: \operatorname{Fin}\left(k\right)} \langle x, \operatorname{F}\left(i\right) \rangle \cdot \operatorname{G}\left(i\right) = x)))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsDualFrame` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Definition 3 (p. 3): "Let {f_i}_{i=1}^k be a frame for H. A dual frame for {f_i}_{i=1}^k is a frame {g_i}_{i=1}^k such that for every f ∈ H," followed by f = sum_i <f,g_i> f_i = sum_i <f,f_i> g_i. IsDualFrame includes that G is a frame and both equations, with x denoting the source's f. The assumption that F is a frame appears separately in claim. All inner products and scalar multiplications are over R.

**Definition 1.3 (Maximal off-diagonal magnitude).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \operatorname{coherence}\left(F, G\right) = \operatorname{iSup}\left(\lambda p: \operatorname{Subtype}\left(\lambda q: \operatorname{Fin}\left(k\right) \times \operatorname{Fin}\left(k\right), \operatorname{Prod.fst}\left(q\right) \ne \operatorname{Prod.snd}\left(q\right)\right), \left|\langle \operatorname{F}\left(\operatorname{Prod.fst}\left(\operatorname{val}\left(p\right)\right)\right), \operatorname{G}\left(\operatorname{Prod.snd}\left(\operatorname{val}\left(p\right)\right)\right) \rangle\right|\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.coherence` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Section 4 (p. 12): "Let F = {f₁, …, fₖ} be a frame for Fⁿ, and let H = {h₁, …, hₖ} be a dual frame for F. We denote the cross-Gramian of F and H by Gr(F, H) and we denote the maximal off-diagonal magnitude of Gr(F, H) as" followed by µ(Gr(F, H)) := max_{i≠j} |⟨f_i, h_j⟩|. Here G denotes H. coherence is the supremum over the subtype of pairs (i,j) with i ≠ j. For k >= 2 the finite index set is nonempty, so this is precisely the source's maximum. Subtype takes the displayed predicate on pairs; val extracts the underlying pair, and Prod.fst and Prod.snd are its two projections.

**Definition 1.4 (Conjecture 41).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (n \le k) \Rightarrow ((2 \le k) \Rightarrow ((\operatorname{IsFrame}\left(F\right)) \Rightarrow ((\operatorname{IsDualFrame}\left(F, G\right)) \Rightarrow (\sqrt{\frac{\operatorname{val}\left(n\right) \cdot \operatorname{val}\left(k\right) - \operatorname{val}\left(n\right)^{2}}{\operatorname{val}\left(k\right)^{2} \cdot (\operatorname{val}\left(k\right) - 1)}} \le \operatorname{coherence}\left(F, G\right))))))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.claim` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Conjecture 41 (Section 4.2, p. 17), verbatim: "Let F be a frame for Fⁿ, and let G be one of its dual frames. Then" µ(Gr(F, G)) ≥ √((nk − n²)/(k²(k − 1))). (21) The encoding takes the real case of the source's field R or C. It quantifies all n, k and all vector families F, G, with n <= k and 2 <= k so that the off-diagonal maximum is nonempty. The operator val denotes the natural-to-real cast; every subtraction and the division in the square root are in R.

**Theorem 1.5 (The conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Take n = 2, k = 3 and F = ((-3,-3),(-3,3),(-1,0)), with G = ((-3/19,-1/6),(-3/19,1/6),(-1/19,0)). Both reconstruction equations hold for every x. Each family therefore spans: reconstruction writes every x as a linear combination of its members. The six off-diagonal inner products are -1/38, 3/19, -1/38, 3/19, 3/19, 3/19 in the order (0,1),(0,2),(1,0),(1,2),(2,0),(2,1). Their maximum absolute value is 3/19, strictly below sqrt(1/9) = 1/3. These exact rational computations refute the universally quantified claim.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsDualFrame`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.IsFrame`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.coherence`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation.result`
