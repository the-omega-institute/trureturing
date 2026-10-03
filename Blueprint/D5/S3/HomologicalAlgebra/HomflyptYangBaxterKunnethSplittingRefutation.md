# The Künneth subcomplex need not split

## Abstract

The HOMFLYPT Yang-Baxter Kunneth subcomplex has no chain retraction for the two-letter decomposition A = {2}, B = {1}.

**Definition 1.1 (The normalized crossing).**

$$\forall m: \mathbb{N}, \forall a: \operatorname{Fin}\left(m\right), \forall b: \operatorname{Fin}\left(m\right), \operatorname{normalizedR}\left(m, a, b\right) = \operatorname{ite}\left(b \le a, \operatorname{Finsupp.single}\left((b, a), 1\right), \operatorname{Finsupp.single}\left((a, b), 1 - t\right) + \operatorname{Finsupp.single}\left((b, a), t\right)\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.normalizedR` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

The coefficient ring is Polynomial Z, written Z[t] with t = Polynomial.X = y². Fin m represents the paper's letters v_1, ..., v_m by 0, ..., m - 1; the free word module is (Fin n → Fin m) →₀ Polynomial Z. Definition 1.5 (v1 PDF, pp. 3–4) gives coefficients 1 if d = a ≥ b = c; y² if d = a < b = c; 1 - y² if c = a < b = d; and 0 otherwise. The displayed map gives its action on a basis pair; linear extension is Finsupp.linearCombination. Both face maps use this same operator.

**Definition 1.2 (Left traveller recursion).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(m\right), (\forall z: 0 < n + 1, \operatorname{leftMove}\left(m, n, w, \operatorname{Fin.mk}\left(0, z\right)\right) = \operatorname{Finsupp.single}\left(\operatorname{Matrix.vecTail}\left(w\right), 1\right)) \land (\forall k: \mathbb{N}, \forall h: k + 1 < n + 1, \operatorname{leftMove}\left(m, n, w, \operatorname{Fin.mk}\left(k + 1, h\right)\right) = \operatorname{let} j: \operatorname{Fin}\left(n\right) = (\operatorname{Fin.mk}\left(k, \operatorname{Nat.{{{{lt}_{of}}_{succ}}_{lt}}_{succ}}\left(h\right)\right): \operatorname{Fin}\left(n\right)); \operatorname{let} jp: \operatorname{Fin}\left(n + 1\right) = \operatorname{Fin.castSucc}\left(j\right); \operatorname{let} jq: \operatorname{Fin}\left(n + 1\right) = \operatorname{Fin.succ}\left(j\right); \operatorname{Finsupp.linearCombination}\left(\mathbb{Z}[t], (\lambda (ab: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(m\right)), \operatorname{leftMove}\left(m, n, \operatorname{Function.update}\left(\operatorname{Function.update}\left(w, \operatorname{Fin.castSucc}\left(j\right), ab.1\right), \operatorname{Fin.succ}\left(j\right), ab.2\right), \operatorname{Fin.castSucc}\left(j\right)\right)), \operatorname{normalizedR}\left(m, w\left(jp\right), w\left(jq\right)\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.leftMove` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

The equations give both cases of leftMove. The local index j has value k, castSucc preserves that value in Fin(n + 1), and succ has value k + 1. The updated word substitutes both outputs of normalizedR before continuing at j.castSucc. At zero, Matrix.vecTail deletes the first letter. The proof arguments certify the displayed Fin bounds.

**Definition 1.3 (Right traveller recursion).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(m\right), (\forall z: 0 < n + 1, \operatorname{rightMove}\left(m, n, w, \operatorname{Fin.mk}\left(0, z\right)\right) = \operatorname{Finsupp.single}\left(\operatorname{Fin.init}\left(w\right), 1\right)) \land (\forall k: \mathbb{N}, \forall h: k + 1 < n + 1, \operatorname{rightMove}\left(m, n, w, \operatorname{Fin.mk}\left(k + 1, h\right)\right) = \operatorname{let} j: \operatorname{Fin}\left(n\right) = \operatorname{Fin.rev}\left((\operatorname{Fin.mk}\left(k, \operatorname{Nat.{{{{lt}_{of}}_{succ}}_{lt}}_{succ}}\left(h\right)\right): \operatorname{Fin}\left(n\right))\right); \operatorname{let} jp: \operatorname{Fin}\left(n + 1\right) = \operatorname{Fin.castSucc}\left(j\right); \operatorname{let} jq: \operatorname{Fin}\left(n + 1\right) = \operatorname{Fin.succ}\left(j\right); \operatorname{let} next: \operatorname{Fin}\left(n + 1\right) = \operatorname{Fin.mk}\left(k, \operatorname{by} \operatorname{omega}\right); \operatorname{Finsupp.linearCombination}\left(\mathbb{Z}[t], (\lambda (ab: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(m\right)), \operatorname{rightMove}\left(m, n, \operatorname{Function.update}\left(\operatorname{Function.update}\left(w, \operatorname{Fin.castSucc}\left(j\right), ab.1\right), \operatorname{Fin.succ}\left(j\right), ab.2\right), next\right)), \operatorname{normalizedR}\left(m, w\left(jp\right), w\left(jq\right)\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.rightMove` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

The equations give both cases of rightMove. The local index j is the reversal in Fin n of the index with value k, so val(j) = n - 1 - k; its castSucc and succ address the adjacent pair. The index next has value k in Fin(n + 1), with its bound discharged by omega in Lean. The updated word substitutes both outputs before continuing at next. At zero, Fin.init deletes the last letter.

**Definition 1.4 (The left wall).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{leftFace}\left(m, n, i\right) = \operatorname{Finsupp.linearCombination}\left(\mathbb{Z}[t], (\lambda (w: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(m\right)), \operatorname{leftMove}\left(m, n, w, i\right))\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.leftFace` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

Definition 1.7 (p. 4): “More precisely, whenever we see a crossing, we apply the Yang-Baxter operator, and for straight lines, we apply the identity map. When hitting the left wall, we delete the first tensor element of each basis in the linear combination, and when hitting the right wall, we delete the last tensor element of each basis in the linear combination.” In the left face, leftMove moves the zero-based position i left according to its complete recursive equations. The traveller is the left output.

**Definition 1.5 (The right wall).**

$$\forall m: \mathbb{N}, \forall n: \mathbb{N}, \forall i: \operatorname{Fin}\left(n + 1\right), \operatorname{rightFace}\left(m, n, i\right) = \operatorname{Finsupp.linearCombination}\left(\mathbb{Z}[t], (\lambda (w: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(m\right)), \operatorname{rightMove}\left(m, n, w, \operatorname{Fin.rev}\left(i\right)\right))\right)$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.rightFace` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

The right face uses the same crossing and takes its right output as traveller. rightMove has val(i) remaining crossings to the right wall and follows its complete recursive equations. The face at original position i uses rightMove at Fin.rev i. Its value on Fin(n + 1) is n minus val(i), using natural-number subtraction.

**Definition 1.6 (The boundary).**

$$\forall m: \mathbb{N}, (\operatorname{differential}\left(m, 0\right) = 0) \land (\forall n: \mathbb{N}, \operatorname{differential}\left(m, n + 1\right) = \sum_{i: \operatorname{Fin}\left(n + 1\right)} (-1)^{\operatorname{Fin.val}\left(i\right) + 1} \cdot (\operatorname{leftFace}\left(m, n, i\right) - \operatorname{rightFace}\left(m, n, i\right)))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.differential` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

The boundary is the alternating difference of the left and right faces. The Lean index i is zero-based, so its sign is (-1)^(val(i) + 1), exactly the paper's one-based (-1)^i. The degree-zero boundary is zero. The display specifies every degree through its zero and successor cases.

**Definition 1.7 (Ordered-block words).**

$$\forall m: \mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \forall B: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right), \operatorname{blockWord}\left(m, A, B, n, w\right) \Leftrightarrow (\exists i: \operatorname{Fin}\left(n + 1\right), (\forall j: \operatorname{Fin}\left(n\right), (\operatorname{Fin.val}\left(j\right) < \operatorname{Fin.val}\left(i\right)) \Rightarrow w\left(j\right) \in A) \land (\forall j: \operatorname{Fin}\left(n\right), (\operatorname{Fin.val}\left(i\right) \le \operatorname{Fin.val}\left(j\right)) \Rightarrow w\left(j\right) \in B))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.blockWord` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

Definition 5.4 (p. 18): “Fix a decomposition of letters X_(m) = A ∪ B and consider a submodule C_n^(m,A,B) of C_n^m generated by sequences in X_(m)^n which start with letters from A and end with letters in B. More formally: X_(n,m,A,B) = {(a_1,a_2,...,a_n) | there is i such that a_1,...,a_i ∈ A; a_(i+1),...,a_n ∈ B}.” A cutoff in Fin(n + 1) ranges over every integer from 0 to n, so either block may be empty. Word positions in Lean start at zero. No disjointness assumption is added.

**Definition 1.8 (Splitting as a chain retraction).**

$$\forall m: \mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \forall B: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \operatorname{splits}\left(m, A, B\right) \Leftrightarrow (\exists p: (\forall n: \mathbb{N}, ((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right)) \Rightarrow_{0} \mathbb{Z}[t]) \Rightarrow_{\mathbb{Z}[t]} \operatorname{Finsupp.supported}\left(\mathbb{Z}[t], \mathbb{Z}[t], \{w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right) \mid \operatorname{blockWord}\left(m, A, B, n, w\right)\}\right)), (\forall n: \mathbb{N}, p\left(n\right) \circ \operatorname{Submodule.subtype}\left(\operatorname{Finsupp.supported}\left(\mathbb{Z}[t], \mathbb{Z}[t], \{w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right) \mid \operatorname{blockWord}\left(m, A, B, n, w\right)\}\right)\right) = \operatorname{LinearMap.id}) \land (\forall n: \mathbb{N}, \forall c: ((\operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(m\right)) \Rightarrow_{0} \mathbb{Z}[t]), \operatorname{Submodule.subtype}\left(\operatorname{Finsupp.supported}\left(\mathbb{Z}[t], \mathbb{Z}[t], \{w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(m\right) \mid \operatorname{blockWord}\left(m, A, B, n, w\right)\}\right)\right)\left(p\left(n\right)\left(\operatorname{differential}\left(m, n + 1, c\right)\right)\right) = \operatorname{differential}\left(m, n + 1, \operatorname{Submodule.subtype}\left(\operatorname{Finsupp.supported}\left(\mathbb{Z}[t], \mathbb{Z}[t], \{w: \operatorname{Fin}\left(n + 1\right) \to \operatorname{Fin}\left(m\right) \mid \operatorname{blockWord}\left(m, A, B, n + 1, w\right)\}\right)\right)\left(p\left(n + 1\right)\left(c\right)\right)\right)))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.splits` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

Finsupp.supported (Polynomial Z) (Polynomial Z) on the displayed block-word set is exactly the span of its single basis vectors, by the existing Finsupp.supported_eq_span_single. This is the submodule of Definition 5.4. A splitting of the short exact sequence of chain complexes means a linear retraction p in every degree with p composed with the inclusion equal to the identity, and p commuting with the differential. The second equation writes that equality after the injective Submodule.subtype map. For the subcomplex of Proposition 5.5, partial composed with inclusion equals inclusion composed with partial_D, so this is exactly the chain-map retraction equation. A degreewise module retraction alone does not yield the paper's stated homology splitting. The assertion needs only these necessary equations; a construction of the entire homology theory is unnecessary.

**Definition 1.9 (Conjecture 5.6).**

$$claim \Leftrightarrow (\forall m: \mathbb{N}, \forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \forall B: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), (A \cup B = \operatorname{univ}\left(\operatorname{Fin}\left(m\right)\right)) \Rightarrow \left((\forall a: \operatorname{Fin}\left(m\right), (a \in A) \Rightarrow \forall b: \operatorname{Fin}\left(m\right), (b \in B) \Rightarrow b \le a) \Rightarrow \operatorname{splits}\left(m, A, B\right)\right))$$

*Formalization.* `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.claim` (`✓ std3`).

*Citation.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

Conjecture 5.6 (p. 18): “The short exact sequence of chain complexes 0 → C_•^(m,A,B) → C_•^m → C_n^m/C_•^(m,A,B) → 0, splits. Thus homology H_n(C_•^m) splits.” The universal parameters are the alphabet size m and the decompositions A ∪ B = X_(m). The hypothesis A ≥ B is that every letter of B is at most every letter of A, as in Proposition 5.5. The quotient is quoted with the paper's printed n index. The formal proposition asserts the chain retraction, the meaning of the sequence splitting, for every such decomposition.

**Theorem 1.10 (The universal chain splitting is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Christiana; B. Clingenpeel; H. Guo; J. Oh; J. H. Przytycki; X. Wang; H. Yun (2025). *Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*. URL: <https://arxiv.org/abs/2502.20659v1>.

*Commentary.*

Take m = 2, A = {2}, B = {1}, encoded in Fin 2 by A = {1}, B = {0}. These blocks are disjoint and strictly ordered. In degree five the six block generators 2^i 1^(5-i), for 0 ≤ i ≤ 5, have zero boundary. Linearity therefore makes the boundary zero on their entire span. The chain c = t(t+1)11112 + (t³+t²+t+1)11121 + t11212 - t12112 + t³12211 + t²12221 has boundary q(2221 - 2111), where q = t³(t² - 1). Both four-letter words belong to the block submodule. A chain retraction would fix this boundary and also make it zero by the degree-five chain-map equation. Its coefficient at 2221 is q, whose coefficient of t^5 is 1, a contradiction. This settles the chain-splitting assertion. The argument does not determine every possible abstract decomposition of the homology groups and does not contradict the subcomplex or tensor-product statements of Proposition 5.5.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.blockWord`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.claim`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.differential`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.leftFace`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.leftMove`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.normalizedR`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.result`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.rightFace`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.rightMove`
- Truth anchor: `D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.splits`
