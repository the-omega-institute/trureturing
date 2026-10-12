# Fekete Lemniscate Area Refutation

## Abstract

A degree-four Fekete polynomial on the connected interval [−20,20] has larger unit-lemniscate area than a monic competitor with zeros in the same interval.

**Definition 1.1 (The Vandermonde product).**

$$\forall n: \mathbb{N}, \forall a: \operatorname{Fin}\left(n\right)\to \mathbb{C}, \operatorname{vandermonde}\left(a\right) = \prod_{i \in \operatorname{Fin}\left(n\right)} (\prod_{j \in \operatorname{Ioi}\left(i\right)} (\Vert a\left(i\right) - a\left(j\right)\Vert))$$

*Formalization.* `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.vandermonde` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

The product of pairwise distances is taken once for each ordered index pair i<j. The tuple is indexed by Fin n, so repeated entries are permitted and give a zero product.

**Definition 1.2 (Fekete tuples).**

$$\forall K: \operatorname{Set}\left(\mathbb{C}\right), \forall n: \mathbb{N}, \forall a: \operatorname{Fin}\left(n\right)\to \mathbb{C}, \operatorname{IsFeketeTuple}\left(K, a\right) \Leftrightarrow ((\forall i: \operatorname{Fin}\left(n\right), a\left(i\right) \in K) \land (\forall b: \operatorname{Fin}\left(n\right)\to \mathbb{C}, (\forall i: \operatorname{Fin}\left(n\right), b\left(i\right) \in K) \Rightarrow (\operatorname{vandermonde}\left(b\right) \le \operatorname{vandermonde}\left(a\right))))$$

*Formalization.* `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.IsFeketeTuple` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

A tuple in K is Fekete when its Vandermonde product is at least that of every other n-tuple in K. This definition does not assume compactness or connectedness; those hypotheses occur in the minimization claim.

**Definition 1.3 (The admissible polynomial class).**

$$\forall K: \operatorname{Set}\left(\mathbb{C}\right), \forall n: \mathbb{N}, \forall p: \operatorname{Polynomial}\left(\mathbb{C}\right), \operatorname{InP}\left(K, n, p\right) \Leftrightarrow ((\operatorname{Monic}\left(p\right)) \land ((\operatorname{natDegree}\left(p\right) = n) \land (\forall z: \mathbb{C}, (\operatorname{IsRoot}\left(p, z\right)) \Rightarrow (z \in K))))$$

*Formalization.* `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.InP` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

Section 1 defines P_n(K) as the monic degree-n polynomials with all zeros in K. The Lean predicate uses natDegree and requires membership in K for every complex root.

**Definition 1.4 (Unit-lemniscate area).**

$$\forall p: \operatorname{Polynomial}\left(\mathbb{C}\right), \operatorname{lemniscateArea}\left(p\right) = \operatorname{volume}\left(\left\{z: \mathbb{C} \mid \Vert \operatorname{eval}\left(p, z\right)\Vert < 1\right\}\right)$$

*Formalization.* `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.lemniscateArea` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

Section 1 defines Λ_p={z:|p(z)|<1}. Its area is planar Lebesgue measure, represented by volume on ℂ and valued in the extended non-negative reals. The source's A_n(K) is the infimum of these areas over P_n(K).

**Definition 1.5 (The connected-set minimization claim).**

$$claim \Leftrightarrow (\forall K: \operatorname{Set}\left(\mathbb{C}\right), \forall n: \mathbb{N}, (1 \le n) \Rightarrow (\forall a: \operatorname{Fin}\left(n\right)\to \mathbb{C}, (\operatorname{IsConnected}\left(K\right)) \Rightarrow ((\operatorname{IsCompact}\left(K\right)) \Rightarrow ((\operatorname{IsFeketeTuple}\left(K, a\right)) \Rightarrow (\forall p: \operatorname{Polynomial}\left(\mathbb{C}\right), (\operatorname{InP}\left(K, n, p\right)) \Rightarrow (\operatorname{lemniscateArea}\left(\prod_{i \in \operatorname{Fin}\left(n\right)} (X - \operatorname{C}\left(a\left(i\right)\right))\right) \le \operatorname{lemniscateArea}\left(p\right)))))))$$

*Formalization.* `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.claim` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

Immediately after Proposition 3.6, verbatim: “While the above proposition proves that Fekete polynomials are not area minimizers in general, it would be of interest to know if they are minimzers when the set $K$ is connected. We leave this as an open question.”

For compact connected K and n≥1, every Fekete tuple defines a monic polynomial with all roots in K. The pairwise comparison against every polynomial in P_n(K) expresses exact minimization of the unit-lemniscate area, whose infimum is A_n(K).

**Theorem 1.6 (An inner-disc certificate).**

$$\forall n: \mathbb{N}, \forall c: \operatorname{Fin}\left(n\right)\to \mathbb{C}, \forall k: \operatorname{Fin}\left(n\right), \forall r: \mathbb{R}, (0 < r) \Rightarrow ((r \cdot \prod_{j \in \operatorname{erase}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), k\right)} (\Vert c\left(k\right) - c\left(j\right)\Vert + r) < 1) \Rightarrow (\operatorname{ball}\left(c\left(k\right), r\right) \subseteq \left\{z: \mathbb{C} \mid \Vert \operatorname{eval}\left(\prod_{i \in \operatorname{Fin}\left(n\right)} (X - \operatorname{C}\left(c\left(i\right)\right)), z\right)\Vert < 1\right\}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.ball_subset_lemniscate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

For any finite complex root family, the triangle inequality bounds each other factor on a disc about the selected root. If the displayed product bound is less than one, the entire open disc lies inside the unit lemniscate. No root separation hypothesis is needed.

**Theorem 1.7 (A three-regime disc cover).**

$$\forall n: \mathbb{N}, (0 < n) \Rightarrow (\forall c: \operatorname{Fin}\left(n\right)\to \mathbb{C}, \forall r: \operatorname{Fin}\left(n\right)\to \mathbb{R}, \forall e: \mathbb{R}, \forall t: \mathbb{R}, (0 < e) \Rightarrow ((0 < t) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (i\neq j) \Rightarrow (2 \cdot t \le \Vert c\left(i\right) - c\left(j\right)\Vert)) \Rightarrow ((\forall k: \operatorname{Fin}\left(n\right), 1 \le r\left(k\right) \cdot \prod_{j \in \operatorname{erase}\left(\operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), k\right)} (\Vert c\left(k\right) - c\left(j\right)\Vert - e)) \Rightarrow ((\forall i: \operatorname{Fin}\left(n\right), \forall j: \operatorname{Fin}\left(n\right), (i\neq j) \Rightarrow (e \le \Vert c\left(i\right) - c\left(j\right)\Vert)) \Rightarrow ((1 \le e \cdot t^{n - 1}) \Rightarrow ((1 \le t^{n}) \Rightarrow (\left\{z: \mathbb{C} \mid \Vert \operatorname{eval}\left(\prod_{i \in \operatorname{Fin}\left(n\right)} (X - \operatorname{C}\left(c\left(i\right)\right)), z\right)\Vert < 1\right\} \subseteq \operatorname{iUnion}\left(i: \operatorname{Fin}\left(n\right) \mapsto \operatorname{ball}\left(c\left(i\right), r\left(i\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.lemniscate_subset_balls` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

The root family is nonempty. Separation by 2t permits three cases for the distance to a nearest root: less than e, between e and t, and at least t. The near, middle and far product bounds exclude any point outside the proposed discs from the unit lemniscate. The radii r_i are arbitrary real numbers subject to the displayed bounds; the theorem does not add a positivity assumption on them.

**Theorem 1.8 (Four Fekete points on an interval).**

$$\forall R: \mathbb{R}, \forall u: \mathbb{R}, (0 < R) \Rightarrow ((0 < u) \Rightarrow ((5 \cdot u^{2} = R^{2}) \Rightarrow (\operatorname{IsFeketeTuple}\left(\operatorname{image}\left(\operatorname{Complex}.\operatorname{ofReal}, \operatorname{Icc}\left(-R, R\right)\right), (i: \operatorname{Fin}\left(4\right) \mapsto ((-R,-u,u,R)\left(i\right): \mathbb{C}))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.isFeketeTuple_interval_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

For R>0 and u>0 with 5u²=R², the tuple (−R,−u,u,R) is Fekete on the real interval embedded in ℂ. The proof bounds every Vandermonde product by 4Ru(R²−u²)², attained by this tuple. With u=R/√5 the value is 64R⁶/(25√5). This exhibits a maximizing tuple without asserting uniqueness.

**Theorem 1.9 (Connectedness does not ensure exact minimization).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ghosh-ramachandran-2026-fekete-lemniscate-area` (refuted) by `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ghosh-ramachandran-2026-fekete-lemniscate-area","declaration_gid":"D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

Take K=[−20,20] embedded in ℂ and n=4. The Fekete polynomial is F(z)=(z²−400)(z²−80); the competitor is G(z)=(z²−400)(z²−100). Disjoint discs inside Λ_F have radii 97/1250000 at ±20 and 217/1250000 at ±√80. A cover of Λ_G has radii 53/625000 at ±20 and 849/5000000 at ±10, certified with e=1/10 and t=5. Hence area(Λ_F) ≥ π·7231744/10¹⁴ > π·7204616/10¹⁴ ≥ area(Λ_G). The interval is compact and connected, and G is monic of degree four with all roots in K. The contradiction concerns exact optimality; the paper's logarithmic asymptotic optimality in Theorem 3.1 is unaffected.

## References

- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.InP`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.IsFeketeTuple`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.ball_subset_lemniscate`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.isFeketeTuple_interval_four`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.lemniscateArea`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.lemniscate_subset_balls`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result`
- Truth anchor: `D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.vandermonde`
