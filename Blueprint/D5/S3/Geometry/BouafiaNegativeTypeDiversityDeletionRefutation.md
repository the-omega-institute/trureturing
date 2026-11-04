# Negative type does not justify irreversible deletion

## Abstract

A five-point scaled Hamming metric refutes irreversible diversity-weight deletion.

**Definition 1.1 (The square-root metric embeds isometrically).**

$$\forall n: \mathbb{N}, [\operatorname{MetricSpace}\left(\operatorname{Fin}\left(n\right)\right)], NegativeType \Leftrightarrow (\exists m: \mathbb{N}, \exists f: \operatorname{Fin}\left(n\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right), (\operatorname{Function}.\operatorname{Injective}(f)) \land (\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), \operatorname{dist}\left(\operatorname{f}\left(i\right), \operatorname{f}\left(j\right)\right) = \operatorname{Real}.\operatorname{sqrt}(\operatorname{dist}\left(i, j\right))))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.NegativeType` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Bouafia, arXiv:2605.03681v1, p. 4, §2.2, verbatim: “A metric space (X,d) is said to be of negative type if (X,√d) admits an isometric embedding into a Hilbert space.” For a finite set Fin n, the image lies in a finite-dimensional real Hilbert space, represented by EuclideanSpace ℝ (Fin m). The formula requires an injective map preserving every square-root distance.

**Definition 1.2 (Exponential similarity).**

$$\forall n: \mathbb{N}, [\operatorname{MetricSpace}\left(\operatorname{Fin}\left(n\right)\right)], \forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), \operatorname{similarity}\left(i, j\right) = \operatorname{Real}.\operatorname{exp}(-(\operatorname{dist}\left(i, j\right)))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.similarity` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Bouafia, p. 3, §2.1, defines the similarity kernel by “Z(x,y) = e⁻ᵈ⁽ˣ,ʸ⁾”. The scale is one, and distances are real-valued. The anonymous bracket denotes a MetricSpace instance on Fin n.

**Definition 1.3 (One inverse solve extended by zero).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right), \forall i: \operatorname{Fin}\left(n\right), \operatorname{weighting}\left(Z, A, i\right) = if hi: i \in A then \operatorname{Matrix}.\operatorname{mulVec}((\operatorname{Matrix}.\operatorname{submatrix}(Z, \operatorname{fun} i: A \mapsto \operatorname{val}\left(i\right), \operatorname{fun} j: A \mapsto \operatorname{val}\left(j\right)))^{-1}, \operatorname{fun} (.:A) \mapsto 1, \langle i, hi \rangle) else 0$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.weighting` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Algorithm 1, p. 16, first sets w to zero on X and then sets its restriction to A to Z restricted to A inverse times the constant-one vector. Matrix.submatrix uses the subtype inclusions. The dot in the constant function is an anonymous argument; hi is the proof that i lies in A.

**Definition 1.4 (The sequence of retained supports).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), (\operatorname{active}\left(Z, 0\right) = \operatorname{Finset}.\operatorname{univ}) \land (\forall k: \mathbb{N}, \operatorname{active}\left(Z, k+1\right) = \operatorname{Finset}.\operatorname{filter}(\operatorname{fun} i: \operatorname{Fin}\left(n\right) \mapsto 0 < \operatorname{weighting}\left(Z, \operatorname{active}\left(Z, k\right), i\right), \operatorname{active}\left(Z, k\right)))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.active` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Algorithm 1, p. 16, starts with all points and retains exactly the strictly positive coordinates after each solve. Indices k begin at zero, so k=1 denotes the second solve. Removed coordinates have zero extended weight.

**Definition 1.5 (The nonnegative stopping condition).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall k: \mathbb{N}, \operatorname{stopped}\left(Z, k\right) \Leftrightarrow (\forall i: \operatorname{Fin}\left(n\right), 0 \le \operatorname{weighting}\left(Z, \operatorname{active}\left(Z, k\right), i\right))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.stopped` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Theorem 4's proof, p. 16, states verbatim: “At the end of the repeat loop, the vector w is non-zero and non-negative.” This is the stopping condition used here. The printed Algorithm 1 instead has the reversed test w ≱ 0. The counterexample uses the nonnegative condition from the proof.

**Definition 1.6 (The first valid nonnegative solve).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall k: \mathbb{N}, \operatorname{FirstStop}\left(Z, k\right) \Leftrightarrow ((\forall l: \mathbb{N}, (l \le k) \Rightarrow ((\operatorname{Finset}.\operatorname{Nonempty}(\operatorname{active}\left(Z, l\right))) \land (\operatorname{Matrix}.\operatorname{det}(\operatorname{Matrix}.\operatorname{submatrix}(Z, \operatorname{fun} i: \operatorname{active}\left(Z, l\right) \mapsto \operatorname{val}\left(i\right), \operatorname{fun} j: \operatorname{active}\left(Z, l\right) \mapsto \operatorname{val}\left(j\right))) \ne 0))) \land ((\forall l: \mathbb{N}, (l < k) \Rightarrow (\neg (\operatorname{stopped}\left(Z, l\right)))) \land (\operatorname{stopped}\left(Z, k\right))))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.FirstStop` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Every visited active set is nonempty, and its principal similarity matrix has nonzero determinant. No earlier solve is nonnegative, and the solve at k is nonnegative. These conditions ensure that the total matrix inverse describes a genuine inverse at every visited step.

**Definition 1.7 (Total weight).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall k: \mathbb{N}, \operatorname{mass}\left(Z, k\right) = \sum_{i:\operatorname{Fin}\left(n\right)} \operatorname{weighting}\left(Z, \operatorname{active}\left(Z, k\right), i\right)$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.mass` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Algorithm 1, p. 16, sums the extended weighting over the original finite set. At a nonzero nonnegative solve this is the positive denominator for the returned probability.

**Definition 1.8 (The returned normalized vector).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall k: \mathbb{N}, \forall i: \operatorname{Fin}\left(n\right), \operatorname{output}\left(Z, k, i\right) = \frac{\operatorname{weighting}\left(Z, \operatorname{active}\left(Z, k\right), i\right)}{\operatorname{mass}\left(Z, k\right)}$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.output` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Algorithm 1, p. 16, returns the weighting divided by its total mass. The universal assertion below requires this denominator to be positive, in addition to requiring a first stop to exist.

**Definition 1.9 (Minimum energy over the probability simplex).**

$$\forall n: \mathbb{N}, \forall Z: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall p: \operatorname{Fin}\left(n\right) \to \mathbb{R}, \operatorname{DiversityMaximizing}\left(Z, p\right) \Leftrightarrow ((\exists mu: \operatorname{Convexity}.\operatorname{StdSimplex}(\mathbb{R}, \operatorname{Fin}\left(n\right)), \forall i: \operatorname{Fin}\left(n\right), mu.weights(i) = \operatorname{p}\left(i\right)) \land (\forall nu: \operatorname{Convexity}.\operatorname{StdSimplex}(\mathbb{R}, \operatorname{Fin}\left(n\right)), \sum_{i:\operatorname{Fin}\left(n\right)} \sum_{j:\operatorname{Fin}\left(n\right)} ((\operatorname{Z}\left(i, j\right) \cdot p(j)) \cdot p(i)) \le \sum_{i:\operatorname{Fin}\left(n\right)} \sum_{j:\operatorname{Fin}\left(n\right)} ((\operatorname{Z}\left(i, j\right) \cdot nu.weights(j)) \cdot nu.weights(i))))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.DiversityMaximizing` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Bouafia, p. 2, introduction, verbatim: “A probability measure μ : X → [0, 1] is said to be diversity-maximizing if it minimizes the quantity” μᵀ Z μ = ∑ₓ,ᵧ∈X e⁻ᵈ⁽ˣ,ʸ⁾ μ(x)μ(y), “which represents the average similarity between two independent samples drawn according to μ.” Convexity.StdSimplex represents precisely the nonnegative finite probabilities of total mass one. Both the feasibility conjunct and the comparison with every probability on the original space are displayed; the summand order is the Lean expression Z i j * p j * p i.

**Definition 1.10 (The negative-type extension question).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, (0 < n) \Rightarrow (\forall metric: \operatorname{MetricSpace}\left(\operatorname{Fin}\left(n\right)\right), letI := metric; (NegativeType(n:=n)) \Rightarrow ((\exists k: \mathbb{N}, \operatorname{FirstStop}\left(similarity(n:=n), k\right)) \land (\forall k: \mathbb{N}, (\operatorname{FirstStop}\left(similarity(n:=n), k\right)) \Rightarrow ((0 < \operatorname{mass}\left(similarity(n:=n), k\right)) \land (\operatorname{DiversityMaximizing}\left(similarity(n:=n), \operatorname{output}\left(similarity(n:=n), k\right)\right)))))))$$

*Formalization.* `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.claim` (`✓ std3`).

*Citation.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Bouafia, arXiv:2605.03681v1, p. 18, §4.1, immediately after Theorem 4, verbatim: “Does DiversityMaximizingMeasure correctly compute the maximizing-diversity measure of all finite subsets of ℝⁿ? Of all finite metric spaces of negative type?” Only the second question is asserted: n is positive, metric ranges over all MetricSpace structures on Fin n, and letI selects that structure. The assertion includes existence of a first stop and requires every first-stop output to have positive mass and minimize energy. Finite labeling covers every nonempty finite metric space. The zero-size space is excluded because it has no probability measure.

**Theorem 1.11 (Five points give a strict counterexample).**

$$\neg (\forall n: \mathbb{N}, (0 < n) \Rightarrow (\forall metric: \operatorname{MetricSpace}\left(\operatorname{Fin}\left(n\right)\right), letI := metric; (NegativeType(n:=n)) \Rightarrow ((\exists k: \mathbb{N}, \operatorname{FirstStop}\left(similarity(n:=n), k\right)) \land (\forall k: \mathbb{N}, (\operatorname{FirstStop}\left(similarity(n:=n), k\right)) \Rightarrow ((0 < \operatorname{mass}\left(similarity(n:=n), k\right)) \land (\operatorname{DiversityMaximizing}\left(similarity(n:=n), \operatorname{output}\left(similarity(n:=n), k\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bouafia-diversity-negative-type` (refuted) by `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bouafia-diversity-negative-type","declaration_gid":"D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Philippe Bouafia (2026). *Magnitude and diversity of trees*. DOI: [10.48550/arXiv.2605.03681](https://doi.org/10.48550/arXiv.2605.03681). URL: <https://arxiv.org/abs/2605.03681v1>.

*Commentary.*

Take the binary points (0,0,0,0,0), (1,1,0,0,1), (0,0,1,0,1), (0,1,0,1,1), (0,0,1,1,1). Scale Hamming distance by log(20/19). Multiplying their binary coordinates by √log(20/19) gives the required square-root isometric embedding. The similarity entries are (19/20) raised to their Hamming distances. The first weighting has signs (+,+,−,−,+), so the second solve uses {0,1,4}. Both principal matrices are nonsingular. The second solve is nonnegative, with mass 12320200/11018319 and normalized vector (15961,22820,0,0,22820)/61601. Mixing this probability with weight 1/1000 of the point mass at index 3 yields a feasible probability of strictly smaller energy; the exact energy decrease is 1707687919/246404000000000. This refutes the negative-type extension of Algorithm 1. The weighted-tree theorem remains within its stated hypotheses. The separate Euclidean-distance question, minimality of five points and correctness of a general re-entry algorithm remain unresolved here.

## References

- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.DiversityMaximizing`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.FirstStop`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.NegativeType`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.active`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.claim`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.mass`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.output`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.result`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.similarity`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.stopped`
- Truth anchor: `D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.weighting`
