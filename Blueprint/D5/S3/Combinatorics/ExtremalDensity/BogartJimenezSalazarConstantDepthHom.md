# Constant depth with a growing degree function

## Abstract

Strongly polynomial graph families have constant depth one and growing degree.

**Definition 1.1 (Numerical polynomials).**

$$\forall g: \operatorname{Polynomial}\left(\mathbb{Q}\right), \operatorname{Numerical}\left(g\right) = \forall z: \mathbb{Z}, \exists k: \mathbb{Z}, (g).\operatorname{eval}\left((z: \mathbb{Q})\right) = (k: \mathbb{Q})$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.Numerical` (`✓ std3`).

*Citation.* Tristram Bogart and Santiago Jiménez-Salazar (2026). *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*. DOI: [10.48550/arXiv.2609.32077](https://doi.org/10.48550/arXiv.2609.32077). URL: <https://arxiv.org/abs/2609.32077v1>.

*Commentary.*

Definition 1.1, p. 2: “A numerical polynomial is a polynomial g(x) ∈ ℚ[x] such that g(q) ∈ ℤ for every q ∈ ℤ.” Integer inputs include negative integers.

**Definition 1.2 (Two-level polynomials).**

$$\forall f: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right), \forall g: \operatorname{Polynomial}\left(\mathbb{Q}\right), \forall e: \mathbb{N} \to \operatorname{WithTop}\left(\mathbb{Z}\right), \operatorname{TwoLevel}\left(f, g, e\right) = \left((\operatorname{Numerical}\left(g\right)) \land ((\exists b: \mathbb{N}, \forall q: \mathbb{N}, (b \le q) \Rightarrow (0 \le (g).\operatorname{eval}\left((q: \mathbb{Q})\right))) \land ((\forall q: \mathbb{N}, (0 \le (g).\operatorname{eval}\left((q: \mathbb{Q})\right)) \Rightarrow (((-1: \mathbb{Z}): \operatorname{WithTop}\left(\mathbb{Z}\right)) \le e\left(q\right))) \land ((\forall q: \mathbb{N}, (0 \le (g).\operatorname{eval}\left((q: \mathbb{Q})\right)) \Rightarrow ((f\left(q\right) \ne 0) \land (((f\left(q\right)).\operatorname{natDegree}: \mathbb{Q}) = (g).\operatorname{eval}\left((q: \mathbb{Q})\right)))) \land ((\forall q: \mathbb{N}, ((g).\operatorname{eval}\left((q: \mathbb{Q})\right) < 0) \Rightarrow ((f\left(q\right) = 0) \land (e\left(q\right) = ((-1: \mathbb{Z}): \operatorname{WithTop}\left(\mathbb{Z}\right))))) \land (\exists phi: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right), \forall q: \mathbb{N}, \forall r: \mathbb{N}, (0 \le (g).\operatorname{eval}\left((q: \mathbb{Q})\right)) \Rightarrow (((r: \operatorname{WithTop}\left(\mathbb{Z}\right)) \le e\left(q\right)) \Rightarrow (ite\left((r \le (f\left(q\right)).\operatorname{natDegree}), ((f\left(q\right)).\operatorname{coeff}\left((f\left(q\right)).\operatorname{natDegree} - r\right)), (0)\right) = (phi\left(r\right)).\operatorname{eval}\left((q: \mathbb{Q})\right))))))))\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.TwoLevel` (`✓ std3`).

*Citation.* Tristram Bogart and Santiago Jiménez-Salazar (2026). *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*. DOI: [10.48550/arXiv.2609.32077](https://doi.org/10.48550/arXiv.2609.32077). URL: <https://arxiv.org/abs/2609.32077v1>.

*Commentary.*

Definition 1.2, p. 2: “Let g be an eventually nonnegative numerical polynomial, let S={q∈ℕ: g(q)≥0}, and let e:S → ℕ ∪ {−1,∞}.” Definition 1.2(a): “A two-level polynomial of degree function g=g(q) and depth function e=e(q) is an infinite sequence of polynomials {f_q}_{q∈S}, with f_q(n) of degree g(q), that has the following property: writing f_q(n) = ∑_{r=0}^{∞}c_r(q)n^{g(q)−r}, where c_r(q)=0 if r>g(q), there exist polynomials {φ_r(q)}_{r≥0} such that, for every q∈S and every r ≤ e(q), we have c_r(q) = φ_r(q).” Definition 1.2(b): “For q∈ℕ∖S, define f_q(n)=0 and e(q)=−1, extending the definition of f_q(n) to all q∈ℕ.” WithTop ℤ with the lower bound −1 represents the permitted depth values; φ is indexed by natural codegrees.

**Definition 1.3 (Constant depth on the nonnegative locus).**

$$\forall g: \operatorname{Polynomial}\left(\mathbb{Q}\right), \forall d: \mathbb{Z}, \forall q: \mathbb{N}, \operatorname{constantDepth}\left(g, d, q\right) = ite\left((0 \le (g).\operatorname{eval}\left((q: \mathbb{Q})\right)), ((d: \operatorname{WithTop}\left(\mathbb{Z}\right))), (((-1: \mathbb{Z}): \operatorname{WithTop}\left(\mathbb{Z}\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.constantDepth` (`✓ std3`).

*Citation.* Tristram Bogart and Santiago Jiménez-Salazar (2026). *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*. DOI: [10.48550/arXiv.2609.32077](https://doi.org/10.48550/arXiv.2609.32077). URL: <https://arxiv.org/abs/2609.32077v1>.

*Commentary.*

Definition 1.2(b), p. 2: “For q∈ℕ∖S, define f_q(n)=0 and e(q)=−1, extending the definition of f_q(n) to all q∈ℕ.” On S, the integer d is viewed in WithTop ℤ.

**Definition 1.4 (Strongly polynomial graph sequences).**

$$\forall v: \mathbb{N} \to \mathbb{N}, \forall G: (q: \mathbb{N}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\left(q\right)\right)\right), \operatorname{StronglyPolynomial}\left(v, G\right) = \forall a: \mathbb{N}, \forall F: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(a\right)\right), \exists p: \operatorname{Polynomial}\left(\mathbb{Q}\right), \forall q: \mathbb{N}, (\operatorname{ThreeClassHomomorphismLimit}.\operatorname{homCount}\left(F, G\left(q\right)\right): \mathbb{Q}) = (p).\operatorname{eval}\left((q: \mathbb{Q})\right)$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.StronglyPolynomial` (`✓ std3`).

*Citation.* Tristram Bogart and Santiago Jiménez-Salazar (2026). *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*. DOI: [10.48550/arXiv.2609.32077](https://doi.org/10.48550/arXiv.2609.32077). URL: <https://arxiv.org/abs/2609.32077v1>.

*Commentary.*

Definition 3.2, p. 9: “A sequence {G_n}_{n≥0} of graphs is strongly polynomial if, for every fixed graph F, there exists a polynomial p_F(n) such that hom(F,G_n)=p_F(n).” The finite simple graphs have Fin-labelled vertices. The count is the cardinality of all adjacency-preserving maps; injectivity is not required. The quantifiers include a=0 and q=0. Rational polynomials represent integer-valued polynomial count functions.

**Definition 1.5 (Question 3.19).**

$$claim = \exists v: \mathbb{N} \to \mathbb{N}, \exists w: \mathbb{N} \to \mathbb{N}, \exists G: (q: \mathbb{N}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\left(q\right)\right)\right), \exists H: (n: \mathbb{N}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(w\left(n\right)\right)\right), \exists f: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right), \exists g: \operatorname{Polynomial}\left(\mathbb{Q}\right), \exists d: \mathbb{Z}, (-1 \le d) \land ((\operatorname{StronglyPolynomial}\left(v, G\right)) \land ((\operatorname{StronglyPolynomial}\left(w, H\right)) \land ((\forall q: \mathbb{N}, \forall n: \mathbb{N}, (\operatorname{ThreeClassHomomorphismLimit}.\operatorname{homCount}\left(G\left(q\right), H\left(n\right)\right): \mathbb{Q}) = (f\left(q\right)).\operatorname{eval}\left((n: \mathbb{Q})\right)) \land ((0 < (g).\operatorname{natDegree}) \land ((\operatorname{TwoLevel}\left(f, g, \operatorname{constantDepth}\left(g, d\right)\right)) \land (\forall b: \mathbb{Z}, (d < b) \Rightarrow (\neg (\operatorname{TwoLevel}\left(f, g, \operatorname{constantDepth}\left(g, b\right)\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.claim` (`✓ std3`).

*Citation.* Tristram Bogart and Santiago Jiménez-Salazar (2026). *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*. DOI: [10.48550/arXiv.2609.32077](https://doi.org/10.48550/arXiv.2609.32077). URL: <https://arxiv.org/abs/2609.32077v1>.

*Commentary.*

Question 3.19, p. 14, verbatim: “More dramatically, do there exist strongly polynomial families G_q, H_n such that the depth function of hom(G_q, H_n) is constant while the degree function is a polynomial of positive degree?” The assertion quantifies over arbitrary finite simple graph sequences. Depth means maximal uniform integer constant depth: some d≥−1 works for all nonnegative parameters, and every larger integer constant fails. This does not assert a pointwise greatest depth function.

**Theorem 1.6 (An affirmative answer to Question 3.19).**

$$\exists v: \mathbb{N} \to \mathbb{N}, \exists w: \mathbb{N} \to \mathbb{N}, \exists G: (q: \mathbb{N}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\left(q\right)\right)\right), \exists H: (n: \mathbb{N}) \to \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(w\left(n\right)\right)\right), \exists f: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{Q}\right), \exists g: \operatorname{Polynomial}\left(\mathbb{Q}\right), \exists d: \mathbb{Z}, (-1 \le d) \land ((\operatorname{StronglyPolynomial}\left(v, G\right)) \land ((\operatorname{StronglyPolynomial}\left(w, H\right)) \land ((\forall q: \mathbb{N}, \forall n: \mathbb{N}, (\operatorname{ThreeClassHomomorphismLimit}.\operatorname{homCount}\left(G\left(q\right), H\left(n\right)\right): \mathbb{Q}) = (f\left(q\right)).\operatorname{eval}\left((n: \mathbb{Q})\right)) \land ((0 < (g).\operatorname{natDegree}) \land ((\operatorname{TwoLevel}\left(f, g, \operatorname{constantDepth}\left(g, d\right)\right)) \land (\forall b: \mathbb{Z}, (d < b) \Rightarrow (\neg (\operatorname{TwoLevel}\left(f, g, \operatorname{constantDepth}\left(g, b\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.result` (`✓ std3`). ∎

*Resolves.* `Problems/bogart-jimenez-salazar-2026-strongly-polynomial-question-3-19` (proved) by `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bogart-jimenez-salazar-2026-strongly-polynomial-question-3-19","declaration_gid":"D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tristram Bogart and Santiago Jiménez-Salazar (2026). *Strongly regular graphs, strongly polynomial sequences, and two-level polynomials*. DOI: [10.48550/arXiv.2609.32077](https://doi.org/10.48550/arXiv.2609.32077). URL: <https://arxiv.org/abs/2609.32077v1>.

*Commentary.*

Take G_q=K_{q+3,2} and H_n=K_{1,n,n}. Their homomorphism count is 2n²(n+1)^(q+3)+4n^(q+4)+2^(q+3)n^(q+3)+2n². Its degree is q+5. The first three codegree coefficients are 2, 2q+10, and (q+3)(q+2)+2^(q+3). The first two are polynomial in q; the third cannot be polynomial, since sufficiently many forward differences annihilate a polynomial and preserve the exponential 2^(q+3). Fixed finite proper colourings and independent choices inside each target part give strong polynomiality of both sequences. The formula and the colouring argument include parameter zero and the empty fixed graph.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.Numerical`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.StronglyPolynomial`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.TwoLevel`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.claim`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.constantDepth`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom.result`
- Dependency: [D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit](ThreeClassHomomorphismLimit.md)
