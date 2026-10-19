# A uniform reduced-coordinate cube family

## Abstract

One uniform autonomous degree-three rational family has cube sums for the actual positive reduced pairs of every positive rational orbit.

The information-escape audit remains unfinished. The eight same-author registration attempts remain declared_unresolved with null certificates; the missing compiler source bindings are disclosed in https://github.com/the-omega-institute/trureturing/issues/18969. The linked issue does not validate the registrations. Mathematical proof, canonical admission, independent acceptance and solve credit are distinct; no native acceptance or solve credit is claimed here.

N includes zero, Q is the rational field, and Z the integers. orbit(t,x,n) starts at n=0 and iterates the single map step(t). For a rational y, num(y) is its intrinsic integer numerator and den(y) its positive natural denominator, already coprime. natAbs is the natural absolute value of an integer; all cross-type arithmetic uses the canonical casts. tsub is truncated natural subtraction. In the projective clauses C, OnePoint(C), PGL, GL, mk, finite, projectivePoint, homogeneousImage, rationalMap and mobius have the meanings given by CubeRecursionProjective. The coordinate formulas use every invertible matrix and every complex point, including poles and infinity.

Section 7 question 2 of arXiv:2610.00765v1 leaves natural undefined. Here it means an explicit uniform family of autonomous rational maps over Q with one nonnegative integer parameter, fixed degree, one formula and a constant independent of parameter, start and index. The constant is c=1. The theorem strengthens the inherited positive-integer starts and n>=2 to all positive rational starts and every n>=1. It makes no n=0 cube-sum or classification claim. A stricter unstated author intent is unresolved. The construction is repository-derived. The supplied bounded comparison identified no equivalent whole answer, but global priority is UNDETERMINED and the companion works were unlocated; no new-solve credit follows here.

**Definition 1.1 (step).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{Q}, \operatorname{step}\left(t, x\right) = \frac{x + t}{(x + t + 1)^{3} - \left(x + t\right)}$$

*Formalization.* `D5/S3/Arith/CubeRecursionFamily.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The map is autonomous. Division is rational division; positivity of the denominator on positive inputs is proved below.

**Definition 1.2 (nextA).**

$$\forall t: \mathbb{N}, \forall a: \mathbb{N}, \forall b: \mathbb{N}, \operatorname{nextA}\left(t, a, b\right) = \left(a + t \cdot b\right) \cdot (b)^{2}$$

*Formalization.* `D5/S3/Arith/CubeRecursionFamily.nextA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

For positive coprime a,b this is the exact next reduced numerator.

**Definition 1.3 (nextB).**

$$\forall t: \mathbb{N}, \forall a: \mathbb{N}, \forall b: \mathbb{N}, \operatorname{nextB}\left(t, a, b\right) = (a + t \cdot b)^{3} + 3 \cdot (a + t \cdot b)^{2} \cdot b + 2 \cdot \left(a + t \cdot b\right) \cdot (b)^{2} + (b)^{3}$$

*Formalization.* `D5/S3/Arith/CubeRecursionFamily.nextB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The expanded natural-valued denominator is visibly positive on positive inputs.

**Definition 1.4 (orbit).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{Q}, \forall n: \mathbb{N}, \operatorname{orbit}\left(t, x, n\right) = \operatorname{iterate}\left(\operatorname{step}\left(t\right), n, x\right)$$

*Formalization.* `D5/S3/Arith/CubeRecursionFamily.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

iterate(f,n,x) is f iterated n times at x, with the zeroth iterate equal to x.

**Theorem 1.5 (reduced step).**

$$\forall t: \mathbb{N}, \forall a: \mathbb{N}, \forall b: \mathbb{N}, (0 < a) \implies ((0 < b) \implies ((\operatorname{Coprime}\left(a, b\right)) \implies ((0 < \operatorname{step}\left(t, \frac{a}{b}\right)) \land ((\operatorname{num}\left(\operatorname{step}\left(t, \frac{a}{b}\right)\right) = \operatorname{nextA}\left(t, a, b\right)) \land ((\operatorname{den}\left(\operatorname{step}\left(t, \frac{a}{b}\right)\right) = \operatorname{nextB}\left(t, a, b\right)) \land ((\operatorname{Coprime}\left(\operatorname{nextA}\left(t, a, b\right), \operatorname{nextB}\left(t, a, b\right)\right)) \land (\operatorname{nextA}\left(t, a, b\right) + \operatorname{nextB}\left(t, a, b\right) = (a + \left(t + 1\right) \cdot b)^{3})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionFamily.reduced_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

Put u=a+t*b. The next numerator is u times b squared and the denominator is (u+b) cubed minus that numerator. The denominator expands as u cubed plus 3*u squared*b plus 2*u*b squared plus b cubed, so both entries are positive. Coprimality of a,b gives coprimality of u,b and of u+b with both. Thus the numerator is coprime to (u+b) cubed, and hence to the denominator. Canonical Rat numerator and denominator lemmas identify this pair with the actual reduced pair.

**Theorem 1.6 (positive orbit cube).**

$$\forall t: \mathbb{N}, \forall x: \mathbb{Q}, (0 < x) \implies ((\forall n: \mathbb{N}, 0 < \operatorname{orbit}\left(t, x, n\right)) \land (\forall n: \mathbb{N}, \operatorname{num}\left(\operatorname{orbit}\left(t, x, n + 1\right)\right) + \operatorname{den}\left(\operatorname{orbit}\left(t, x, n + 1\right)\right) = (\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right) + \left(t + 1\right) \cdot \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right))^{3}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionFamily.positive_orbit_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

Every positive rational is its canonical reduced numerator divided by denominator. Apply reduced_step to that pair; induction preserves positivity and gives the integer cube identity for every next step. There is no finite index bound or conditional no-cancellation assumption.

**Definition 1.7 (originalClaim).**

$$\operatorname{originalClaim} \iff (\forall t: \mathbb{N}, (\operatorname{mapDegree}\left(\operatorname{rationalMap}\left(t\right)\right) = 3) \land ((\forall x: \mathbb{C}, \forall y: \mathbb{C}, ((x \neq 0) \lor (y \neq 0)) \implies (\operatorname{projectiveMap}\left(t, \operatorname{projectivePoint}\left(x, y\right)\right) = \operatorname{homogeneousImage}\left(t, x, y\right))) \land (((\forall g: \operatorname{PGL}\left(2, \mathbb{C}\right), \exists m: \operatorname{GL}\left(2, \mathbb{C}\right), \operatorname{mk}\left(m\right) = g) \land (\forall m: \operatorname{GL}\left(2, \mathbb{C}\right), (\operatorname{mobius}\left(\operatorname{mk}\left(m\right), \infty\right) = \operatorname{ite}\left(\operatorname{entry}\left(m, 1, 0\right) = 0, \infty, \operatorname{finite}\left(\frac{\operatorname{entry}\left(m, 0, 0\right)}{\operatorname{entry}\left(m, 1, 0\right)}\right)\right)) \land (\forall z: \mathbb{C}, \operatorname{mobius}\left(\operatorname{mk}\left(m\right), \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{entry}\left(m, 1, 0\right) \cdot z + \operatorname{entry}\left(m, 1, 1\right) = 0, \infty, \operatorname{finite}\left(\frac{\operatorname{entry}\left(m, 0, 0\right) \cdot z + \operatorname{entry}\left(m, 0, 1\right)}{\operatorname{entry}\left(m, 1, 0\right) \cdot z + \operatorname{entry}\left(m, 1, 1\right)}\right)\right)))) \land (((\operatorname{projectiveMap}\left(t, \infty\right) = \operatorname{finite}\left(0\right)) \land (\forall z: \mathbb{C}, \operatorname{projectiveMap}\left(t, \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{eval}\left(\operatorname{denom}\left(\operatorname{rationalMap}\left(t\right)\right), z\right) = 0, \infty, \operatorname{finite}\left(\operatorname{eval}\left(\operatorname{rationalMap}\left(t\right), z\right)\right)\right))) \land ((\forall g: \operatorname{PGL}\left(2, \mathbb{C}\right), \neg (\forall p: \operatorname{OnePoint}\left(\mathbb{C}\right), \operatorname{mobius}\left(g, \operatorname{projectiveMap}\left(t, \operatorname{mobius}\left(\operatorname{inv}\left(g\right), p\right)\right)\right) = \operatorname{powerMap}\left(p\right))) \land (\forall x: \mathbb{Q}, (0 < x) \implies ((\forall n: \mathbb{N}, (0 < \operatorname{orbit}\left(t, x, n\right)) \land ((0 < \operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right)) \land ((0 < \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right)) \land ((\operatorname{Coprime}\left(\operatorname{natAbs}\left(\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right)\right), \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right)\right)) \land (\frac{\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right)}{\operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right)} = \operatorname{orbit}\left(t, x, n\right)))))) \land ((\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right) + \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right) = (\operatorname{num}\left(\operatorname{orbit}\left(t, x, \operatorname{tsub}\left(n, 1\right)\right)\right) + \left(t + 1\right) \cdot \operatorname{den}\left(\operatorname{orbit}\left(t, x, \operatorname{tsub}\left(n, 1\right)\right)\right))^{3})) \land (\forall n: \mathbb{N}, \operatorname{projectiveMap}\left(t, \operatorname{finite}\left(\operatorname{toComplex}\left(\operatorname{orbit}\left(t, x, n\right)\right)\right)\right) = \operatorname{finite}\left(\operatorname{toComplex}\left(\operatorname{orbit}\left(t, x, n + 1\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/Arith/CubeRecursionFamily.originalClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

This closed proposition states the whole source endpoint together with the semantic bridges. In each n>=1 cube equality the displayed num and den are intrinsic to the actual iterate. All projective clauses are conjoined, including the full quotient and action correspondence.

**Theorem 1.8 (result).**

$$\forall t: \mathbb{N}, (\operatorname{mapDegree}\left(\operatorname{rationalMap}\left(t\right)\right) = 3) \land ((\forall x: \mathbb{C}, \forall y: \mathbb{C}, ((x \neq 0) \lor (y \neq 0)) \implies (\operatorname{projectiveMap}\left(t, \operatorname{projectivePoint}\left(x, y\right)\right) = \operatorname{homogeneousImage}\left(t, x, y\right))) \land (((\forall g: \operatorname{PGL}\left(2, \mathbb{C}\right), \exists m: \operatorname{GL}\left(2, \mathbb{C}\right), \operatorname{mk}\left(m\right) = g) \land (\forall m: \operatorname{GL}\left(2, \mathbb{C}\right), (\operatorname{mobius}\left(\operatorname{mk}\left(m\right), \infty\right) = \operatorname{ite}\left(\operatorname{entry}\left(m, 1, 0\right) = 0, \infty, \operatorname{finite}\left(\frac{\operatorname{entry}\left(m, 0, 0\right)}{\operatorname{entry}\left(m, 1, 0\right)}\right)\right)) \land (\forall z: \mathbb{C}, \operatorname{mobius}\left(\operatorname{mk}\left(m\right), \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{entry}\left(m, 1, 0\right) \cdot z + \operatorname{entry}\left(m, 1, 1\right) = 0, \infty, \operatorname{finite}\left(\frac{\operatorname{entry}\left(m, 0, 0\right) \cdot z + \operatorname{entry}\left(m, 0, 1\right)}{\operatorname{entry}\left(m, 1, 0\right) \cdot z + \operatorname{entry}\left(m, 1, 1\right)}\right)\right)))) \land (((\operatorname{projectiveMap}\left(t, \infty\right) = \operatorname{finite}\left(0\right)) \land (\forall z: \mathbb{C}, \operatorname{projectiveMap}\left(t, \operatorname{finite}\left(z\right)\right) = \operatorname{ite}\left(\operatorname{eval}\left(\operatorname{denom}\left(\operatorname{rationalMap}\left(t\right)\right), z\right) = 0, \infty, \operatorname{finite}\left(\operatorname{eval}\left(\operatorname{rationalMap}\left(t\right), z\right)\right)\right))) \land ((\forall g: \operatorname{PGL}\left(2, \mathbb{C}\right), \neg (\forall p: \operatorname{OnePoint}\left(\mathbb{C}\right), \operatorname{mobius}\left(g, \operatorname{projectiveMap}\left(t, \operatorname{mobius}\left(\operatorname{inv}\left(g\right), p\right)\right)\right) = \operatorname{powerMap}\left(p\right))) \land (\forall x: \mathbb{Q}, (0 < x) \implies ((\forall n: \mathbb{N}, (0 < \operatorname{orbit}\left(t, x, n\right)) \land ((0 < \operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right)) \land ((0 < \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right)) \land ((\operatorname{Coprime}\left(\operatorname{natAbs}\left(\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right)\right), \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right)\right)) \land (\frac{\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right)}{\operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right)} = \operatorname{orbit}\left(t, x, n\right)))))) \land ((\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{num}\left(\operatorname{orbit}\left(t, x, n\right)\right) + \operatorname{den}\left(\operatorname{orbit}\left(t, x, n\right)\right) = (\operatorname{num}\left(\operatorname{orbit}\left(t, x, \operatorname{tsub}\left(n, 1\right)\right)\right) + \left(t + 1\right) \cdot \operatorname{den}\left(\operatorname{orbit}\left(t, x, \operatorname{tsub}\left(n, 1\right)\right)\right))^{3})) \land (\forall n: \mathbb{N}, \operatorname{projectiveMap}\left(t, \operatorname{finite}\left(\operatorname{toComplex}\left(\operatorname{orbit}\left(t, x, n\right)\right)\right)\right) = \operatorname{finite}\left(\operatorname{toComplex}\left(\operatorname{orbit}\left(t, x, n + 1\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CubeRecursionFamily.result` (`✓ std3`). ∎

*Resolves.* `Problems/arxiv-2610-00765-cube-recursion-family` (proved) by `D5/S3/Arith/CubeRecursionFamily.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arxiv-2610-00765-cube-recursion-family","declaration_gid":"D5/S3/Arith/CubeRecursionFamily.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick and Santiago Rodriguez and Gregorio Salazar (2026). *Perfect squares in reciprocal-sum sequences and primes that are inert in quadratic fields*. DOI: [10.48550/arXiv.2610.00765](https://doi.org/10.48550/arXiv.2610.00765). URL: <https://arxiv.org/abs/2610.00765v1>.

*Commentary.*

The single result combines reduced_step and orbit induction with the complex rational-map degree, homogeneous coordinates, affine/pole/infinity evaluation, the full PGL quotient and action, and nonconjugacy. The rational orbit and complex projective map agree at every positive rational iterate. The reduced polynomial degrees are one and three. The fibre obstruction excludes every complex Möbius conjugacy to z cubed. Positivity and coprimality are conclusions, not extra orbit hypotheses. Under the declared minimal reading this provides the requested family with c=1; it does not settle a stronger unstated definition of natural or claim global originality.

## References

- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.nextA`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.nextB`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.orbit`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.originalClaim`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.positive_orbit_cube`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.reduced_step`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.result`
- Truth anchor: `D5/S3/Arith/CubeRecursionFamily.step`
- Dependency: [D5/S3/Arith/CubeRecursionProjective](CubeRecursionProjective.md)
