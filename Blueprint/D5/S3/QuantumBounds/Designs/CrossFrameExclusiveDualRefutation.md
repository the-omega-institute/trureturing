# An exclusive Grassmannian dual need not be canonical

## Abstract

A frame can have a unique dual minimizing the off-diagonal cross-Gramian magnitude without that dual being canonical.

**Definition 1.1 (Finite real frame).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \operatorname{IsFrame}\left(F\right) \Leftrightarrow (\exists A \in \mathbb{R},\; \exists B \in \mathbb{R},\; (0 < A) \land ((A \le B) \land (\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (A \cdot \left\lVert x \right\rVert^{2} \le \sum_{i: \operatorname{Fin}\left(k\right)} \left|\langle x, F\left(i\right) \rangle\right|^{2}) \land (\sum_{i: \operatorname{Fin}\left(k\right)} \left|\langle x, F\left(i\right) \rangle\right|^{2} \le B \cdot \left\lVert x \right\rVert^{2}))))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.IsFrame` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Definition 1 (p. 3): A sequence of vectors F = {f_i}_{i=1}^k, with k ≥ n, in an n-dimensional Hilbert space H is a frame for H if there exist real constants 0 < A ≤ B < +∞ such that A‖f‖² ≤ ∑_{i=1}^k |⟨f, f_i⟩|² ≤ B‖f‖² for every f ∈ H. The separate hypothesis n <= k imposes the source's size condition; EuclideanSpace over the reals realizes its real Hilbert space. Indices run from 0 through k - 1.

**Definition 1.2 (Dual reconstruction).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \operatorname{IsDualFrame}\left(F, G\right) \Leftrightarrow (\forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i: \operatorname{Fin}\left(k\right)} \langle x, G\left(i\right) \rangle \cdot F\left(i\right) = x)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.IsDualFrame` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Definition 3 (p. 3): Let {f_i}_{i=1}^k be a frame for H. A dual frame for {f_i}_{i=1}^k is a frame {g_i}_{i=1}^k such that for every f ∈ H, f = ∑_{i=1}^k ⟨f, g_i⟩f_i = ∑_{i=1}^k ⟨f, f_i⟩g_i. IsDualFrame records the first operator identity. Over the reals, its transpose gives the second; reconstruction also makes both finite families span the space, so they are frames.

**Definition 1.3 (Off-diagonal magnitude).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \mu\left(F, G\right) = \operatorname{val}\left(\max_{i, j: \operatorname{Fin}\left(k\right), i \ne j} \left\lVert \langle F\left(i\right), G\left(j\right) \rangle \right\rVert_{+}\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.mu` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Section 4 (p. 12) defines: µ(Gr(F, H)) := max_{i≠j} |⟨f_i, h_j⟩|. The finite supremum is taken in the nonnegative reals and val denotes its coercion to the reals. An empty off-diagonal set has supremum zero. For a real scalar the nonnegative norm is its absolute value.

**Definition 1.4 (Frame operator).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \operatorname{frameOperator}\left(F, x\right) = \sum_{i: \operatorname{Fin}\left(k\right)} \langle x, F\left(i\right) \rangle \cdot F\left(i\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.frameOperator` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Page 3 states: The frame operator of F = {f_i}_{i=1}^k is defined as S = θ_F* θ_F. Its action is the displayed reconstruction sum with F in both places.

**Definition 1.5 (Canonical dual).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{canonicalDual}\left(F, i\right) = \operatorname{invFun}\left(\operatorname{frameOperator}\left(F\right)\right)\left(F\left(i\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.canonicalDual` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Page 4 states: The canonical dual frame for a frame F = {f_i}_{i=1}^k for H with frame operator S is the frame F̃ = {S^{-1} f_i}_{i=1}^k. Mathlib's invFun is the inverse function of frameOperator; for a frame its positive lower bound makes this operator invertible in finite dimension.

**Definition 1.6 (Conjecture 42).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall F \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall G \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (n \le k) \Rightarrow ((\operatorname{IsFrame}\left(F\right)) \Rightarrow ((\operatorname{IsDualFrame}\left(F, G\right)) \Rightarrow ((\forall H \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (\operatorname{IsDualFrame}\left(F, H\right)) \Rightarrow (\mu\left(F, G\right) \le \mu\left(F, H\right))) \Rightarrow ((\forall H \in \operatorname{Fin}\left(k\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; (\operatorname{IsDualFrame}\left(F, H\right)) \Rightarrow ((\mu\left(F, H\right) \le \mu\left(F, G\right)) \Rightarrow (H = G))) \Rightarrow (G = \operatorname{canonicalDual}\left(F\right)))))))$$

*Formalization.* `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.claim` (`✓ std3`).

*Citation.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Conjecture 42 (Section 4.2, p. 17): If a frame F for F^n forms an exclusive Grassmannian pair with one of its duals, then that dual must be the canonical dual frame of F. Definition 34 (p. 13): A frame F for F^n forms a Grassmannian pair with its dual frame F̃ if µ(Gr(F, F̃)) = min{µ(Gr(F, H)) | H is a dual frame of F}. (14) The following sentence (p. 14) reads: Some frames form an exclusive Grassmannian pair with their canonical dual (Example 32), while other frames (Example 31) have more than one dual frame which satisfy (14). Section 4.2 (p. 17) further specifies that the canonical dual in Example 32 is the only dual frame that satisfies (14). The encoding quantifies over all dimensions, sizes and real finite families. The first universal condition says G minimizes the magnitude over every dual H; the second says any dual H with no greater magnitude equals G. A real counterexample suffices to disprove the assertion for real or complex Hilbert spaces.

**Theorem 1.7 (A noncanonical unique minimizer and four-column application exposition).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/aceska-kaczanowski-2022-exclusive-grassmannian-dual-refutation` (refuted) by `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"aceska-kaczanowski-2022-exclusive-grassmannian-dual-refutation","declaration_gid":"D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Aceska and M. Kaczanowski (2022). *Cross-Frame Potential*. DOI: [10.1080/01630563.2022.2128818](https://doi.org/10.1080/01630563.2022.2128818). URL: <https://arxiv.org/abs/2205.05613v3>.

*Commentary.*

Take n = 1, k = 3 and F = (3, 2, 1). Its frame bound is 14 and its duals satisfy 3 h_0 + 2 h_1 + h_2 = 1. The off-diagonal bounds imply 2 |h_0| <= mu(F,H), 3 |h_1| <= mu(F,H) and 3 |h_2| <= mu(F,H). Hence 1 <= (5/2) mu(F,H). The dual G = (1/5, 2/15, 2/15) attains mu(F,G) = 2/5. If a dual has magnitude at most 2/5, the reconstruction identity and the three coordinate upper bounds force each coordinate to equal the corresponding coordinate of G. Thus G is the unique minimizer. The frame operator is multiplication by 14, so its canonical dual has first coordinate 3/14, different from 1/5. Owner application exposition (no new declaration): the same existing IsFrame, IsDualFrame, mu, frameOperator, and canonicalDual APIs also expose the following four-column calculation. For any RCLike field K, take the synthesis matrix S = [[1, 0, -1, 0], [0, 1, 0, -1]], whose columns are the four unit vectors e_1, e_2, -e_1, -e_2. Thus S S^* = 2 I and the canonical dual is S/2. Writing an actual dual matrix as H = (h_{rj}), the equation S H^* = I is exactly the four reconstruction equations h_00 - h_02 = 1, h_10 - h_12 = 0, h_01 - h_03 = 0, and h_11 - h_13 = 1. The closed two-parameter family H(b,c) = [[1/2, b, -1/2, b], [c, 1/2, c, -1/2]] satisfies these equations for unrestricted b,c. If norm b <= 1/2 and norm c <= 1/2, every off-diagonal cross-Gram entry has norm at most 1/2 and the entries forced by the opposite columns attain 1/2, so mu(S,H(b,c)) = 1/2. Conversely, for every actual dual H, the off-diagonal entries at (2,0) and (0,2) are -h_00 and h_02; the first reconstruction equation and the norm triangle inequality give 1 <= norm h_00 + norm h_02 <= 2 mu(S,H). Hence 1/2 is the universal lower bound, attained by the whole closed family: over the reals b,c range over the closed interval [-1/2, 1/2], and over the complexes they range over the closed disks of radius 1/2. This is a matrix optimization statement; in the real case its columns are actual Euclidean dual vectors and the existing IsDualFrame and mu definitions provide the reconstruction and coherence bridge. For the canonical pair G = S/2, any two cross-Gram rows, after taking the norm of every entry, agree under an actual Fin 4 permutation (the identity or the zero-based permutation (1,0,3,2)), using all four column positions including the diagonal positions. By symmetry of this canonical cross-Gram matrix, the full-column co-equidistribution predicate holds. The two real duals H(0,0) and H(1/4,0) are distinct (their row-zero, column-one entries differ), both attain the same sharp value 1/2, and both satisfy the actual reconstruction equations; this is the literal reverse-C43 counterexample. It refutes uniqueness of the minimizing dual while leaving the objective value intact. The exposition does not classify all minimizers, does not assert co-equidistribution for every family member, and does not claim that the existing C42 refutation proves this four-column application. The inequalities use only the pinned public Mathlib finite-sup order and norm triangle facts.

## References

- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.IsDualFrame`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.IsFrame`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.canonicalDual`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.frameOperator`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.mu`
- Truth anchor: `D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.result`
