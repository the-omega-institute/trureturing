# A twisted Schur Newton polytope with two competing dominant vertices

## Abstract

A twisted Schur Newton polytope need not be a single signed-permutation orbit.

**Definition 1.1 (The alphabet size).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \operatorname{N}\left(t, r\right) = t + 2 \cdot r$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.N` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, §1.1, p. 1: “Fix t ≥ 1 and r ≥ 1, put N = t + 2r”. The finite alphabet has t frozen roots and r reciprocal pairs.

**Definition 1.2 (The order of the alphabet).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, (\forall a: \operatorname{Fin}\left(t\right), \operatorname{sourceIndex}\left(\operatorname{Sum}.\operatorname{inl}\left(a\right)\right) = \operatorname{val}\left(a\right)) \land (\forall k: \operatorname{Fin}\left(r\right), (\operatorname{sourceIndex}\left(\operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inl}\left(k\right)\right)\right) = t + 2 \cdot \operatorname{val}\left(k\right)) \land (\operatorname{sourceIndex}\left(\operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(k\right)\right)\right) = t + 2 \cdot \operatorname{val}\left(k\right) + 1))$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.sourceIndex` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

The source alphabet, §1.1, p. 1, is x=(1,ζ,…,ζ^(t−1),z₁,z₁⁻¹,…,zᵣ,zᵣ⁻¹). Sum.inl indexes the frozen roots; Sum.inr (Sum.inl k) and Sum.inr (Sum.inr k) index a variable and its reciprocal. sourceIndex gives their zero-based position.

**Definition 1.3 (The denominator exponents).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \forall j: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right), \operatorname{delta}\left(t, r, j\right) = (\operatorname{N}\left(t, r\right): \mathbb{Z}) - 1 - (\operatorname{sourceIndex}\left(j\right): \mathbb{Z})$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.delta` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, §1.1, p. 1: “write δ=(N−1,N−2,…,0) and λ=β−δ, so that λ is a partition”. Integer subtraction here is in ℤ.

**Definition 1.4 (Strict decrease and zero final exponent).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \forall beta: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \to \mathbb{Z}, \operatorname{NormalizedBeta}\left(t, r, beta\right) = \left((\forall i: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right), \forall j: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right), (\operatorname{sourceIndex}\left(i\right) < \operatorname{sourceIndex}\left(j\right)) \Rightarrow (\operatorname{beta}\left(j\right) < \operatorname{beta}\left(i\right))) \land (\forall j: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right), (\operatorname{sourceIndex}\left(j\right) + 1 = \operatorname{N}\left(t, r\right)) \Rightarrow (\operatorname{beta}\left(j\right) = 0))\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.NormalizedBeta` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, §1.1, p. 1: “For a strictly decreasing β∈ℤᴺ normalised by β_N=0”. The order is the zero-based sourceIndex order, and the last position is characterized by sourceIndex j+1=N t r.

**Definition 1.5 (Powers in the reciprocal Laurent alphabet).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \forall b: \mathbb{Z}, (\forall a: \operatorname{Fin}\left(t\right), \operatorname{alphabetPower}\left(t, r, b, \operatorname{Sum}.\operatorname{inl}\left(a\right)\right) = \operatorname{AddMonoidAlgebra}.\operatorname{single}\left(0, \operatorname{Complex}.\operatorname{exp}\left((\frac{2 \cdot \operatorname{Real}.\operatorname{pi}}{(t: \mathbb{R})}: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right)^{(\operatorname{val}\left(a\right): \mathbb{Z}) \cdot b}\right)) \land (\forall k: \operatorname{Fin}\left(r\right), (\operatorname{alphabetPower}\left(t, r, b, \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inl}\left(k\right)\right)\right) = \operatorname{AddMonoidAlgebra}.\operatorname{single}\left(\operatorname{Pi}.\operatorname{single}\left(k, b\right), 1\right)) \land (\operatorname{alphabetPower}\left(t, r, b, \operatorname{Sum}.\operatorname{inr}\left(\operatorname{Sum}.\operatorname{inr}\left(k\right)\right)\right) = \operatorname{AddMonoidAlgebra}.\operatorname{single}\left(\operatorname{Pi}.\operatorname{single}\left(k, -b\right), 1\right)))$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.alphabetPower` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, §1.1, p. 1: “let ζ=e^{2πi/t} and μ_t={1,ζ,…,ζ^(t−1)}”. The source defines x=(1,ζ,…,ζ^(t−1),z₁,z₁⁻¹,…,zᵣ,zᵣ⁻¹). The displayed three cases give x_i^b. AddMonoidAlgebra.single stores a complex coefficient at an integral exponent function; Pi.single inserts b in one coordinate. The exponential uses real division followed by the inclusion ℝ→ℂ, and the power exponent is an integer.

**Definition 1.6 (The numerator alternant).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \forall beta: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \to \mathbb{Z}, \operatorname{numerator}\left(t, r, beta\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{fun} i: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \mapsto \operatorname{fun} j: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \mapsto \operatorname{alphabetPower}\left(t, r, \operatorname{beta}\left(j\right), i\right)\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.numerator` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

The numerator in equation (1), §1.1, p. 1, is det(x_i^{β_j}) for i,j=1,…,N. Both determinant indices use the same finite alphabet order.

**Definition 1.7 (The denominator alternant).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \operatorname{denominator}\left(t, r\right) = \operatorname{Matrix}.\operatorname{det}\left(\operatorname{fun} i: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \mapsto \operatorname{fun} j: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \mapsto \operatorname{alphabetPower}\left(t, r, \operatorname{delta}\left(t, r, j\right), i\right)\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.denominator` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

The denominator in equation (1), §1.1, p. 1, is det(x_i^{δ_j}) for i,j=1,…,N. It is the same determinant construction at delta.

**Definition 1.8 (The literal alternant quotient).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, \forall beta: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \to \mathbb{Z}, \forall f: \operatorname{AddMonoidAlgebra}\left(\mathbb{C}, (\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right), \operatorname{IsPhi}\left(t, r, beta, f\right) = \left((\operatorname{denominator}\left(t, r\right) \ne 0) \land (f \cdot \operatorname{denominator}\left(t, r\right) = \operatorname{numerator}\left(t, r, beta\right))\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.IsPhi` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, equation (1), §1.1, p. 1: “Φ_{t,r}(β)=det(x_i^{β_j})/det(x_i^{δ_j})”. In the Laurent ring IsPhi requires the denominator to be nonzero and the cross-multiplied equality f·denominator=numerator. Thus no division is performed at a zero denominator.

**Definition 1.9 (The Newton polytope).**

$$\forall r: \mathbb{N}, \forall f: \operatorname{AddMonoidAlgebra}\left(\mathbb{C}, (\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right), \operatorname{newtonPolytope}\left(f\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{Set}.\operatorname{image}\left(\operatorname{fun} a: \operatorname{Fin}\left(r\right) \to \mathbb{Z} \mapsto \operatorname{fun} k: \operatorname{Fin}\left(r\right) \mapsto (\operatorname{a}\left(k\right): \mathbb{R}), (f.\operatorname{coeff}.\operatorname{support}: \operatorname{Set}\left((\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right))\right)\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.newtonPolytope` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, §7, p. 47: “Let N_β denote the numerator of (1) and Newt(N_β) its Newton polytope.” For a Laurent polynomial the Newton polytope is the real convex hull of integral exponent functions with nonzero complex coefficient. The inclusion of integral coordinates into real coordinates is explicit.

**Definition 1.10 (The signed-permutation orbit).**

$$\forall r: \mathbb{N}, \forall mu: \operatorname{Fin}\left(r\right) \to \mathbb{Z}, \operatorname{signedOrbit}\left(mu\right) = \{x: \operatorname{Fin}\left(r\right) \to \mathbb{R}\mid\exists sigma: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(r\right)\right), \exists epsilon: \operatorname{Fin}\left(r\right) \to \mathbb{Z}, (\forall k: \operatorname{Fin}\left(r\right), (\operatorname{epsilon}\left(k\right) = 1) \lor (\operatorname{epsilon}\left(k\right) = -1)) \land (\forall k: \operatorname{Fin}\left(r\right), \operatorname{x}\left(k\right) = (\operatorname{epsilon}\left(k\right): \mathbb{R}) \cdot (\operatorname{mu}\left(\operatorname{sigma}\left(k\right)\right): \mathbb{R}))\}$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.signedOrbit` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

The W(C_r) orbit appearing in Conjecture 8.1, §8, p. 49, consists of all coordinate permutations and independent sign choices. sigma is a permutation of Fin r; each epsilon k is the integer 1 or −1.

**Definition 1.11 (The convex hull of one orbit).**

$$\forall r: \mathbb{N}, \forall mu: \operatorname{Fin}\left(r\right) \to \mathbb{Z}, \operatorname{orbitPolytope}\left(mu\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{signedOrbit}\left(mu\right)\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.orbitPolytope` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Conjecture 8.1, §8, p. 49, uses conv(W(C_r) μ). orbitPolytope takes the real convex hull of the signedOrbit of an integral weight.

**Definition 1.12 (Dominant integral weights).**

$$\forall r: \mathbb{N}, \forall mu: \operatorname{Fin}\left(r\right) \to \mathbb{Z}, \operatorname{Dominant}\left(mu\right) = \left((\forall k: \operatorname{Fin}\left(r\right), 0 \le \operatorname{mu}\left(k\right)) \land (\operatorname{Antitone}\left(mu\right))\right)$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.Dominant` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

The dominant integral weights for W(C_r) are the nonnegative weakly decreasing integer vectors. Antitone uses the natural order on Fin r.

**Definition 1.13 (Marín Conjecture 8.1).**

$$\forall t: \mathbb{N}, \forall r: \mathbb{N}, (1 \le t) \Rightarrow ((1 \le r) \Rightarrow (\forall beta: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \to \mathbb{Z}, (\operatorname{NormalizedBeta}\left(t, r, beta\right)) \Rightarrow ((\exists f: \operatorname{AddMonoidAlgebra}\left(\mathbb{C}, (\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right), \operatorname{IsPhi}\left(t, r, beta, f\right)) \land (\forall f: \operatorname{AddMonoidAlgebra}\left(\mathbb{C}, (\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right), (\operatorname{IsPhi}\left(t, r, beta, f\right)) \Rightarrow ((f \ne 0) \Rightarrow (\exists mu: \operatorname{Fin}\left(r\right) \to \mathbb{Z}, (\operatorname{Dominant}\left(mu\right)) \land (\operatorname{newtonPolytope}\left(f\right) = \operatorname{orbitPolytope}\left(mu\right))))))))$$

*Formalization.* `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.claim` (`✓ std3`).

*Citation.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

Marín, Conjecture 8.1, §8, p. 49, verbatim: “If Φ_{t,r}≠0 then {μ:A_μ≠0} has a unique maximal element μ_max for the Weyl majorisation order μ≼μ′⇔μ∈conv(W(C_r) μ′); equivalently, Newt(Φ_{t,r}) is the orbit polytope conv(W(C_r) μ_max).” Here A_mu is the folded coefficient support specified immediately before the conjecture. The formula states the explicitly equivalent Newton-polytope assertion for every t,r≥1 and every strictly decreasing normalized beta. It also requires a Laurent quotient to exist; the counterexample has such a quotient.

**Theorem 1.14 (The universal single-orbit assertion is false).**

$$\neg(\forall t: \mathbb{N}, \forall r: \mathbb{N}, (1 \le t) \Rightarrow ((1 \le r) \Rightarrow (\forall beta: \operatorname{Sum}\left(\operatorname{Fin}\left(t\right), \operatorname{Sum}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right)\right)\right) \to \mathbb{Z}, (\operatorname{NormalizedBeta}\left(t, r, beta\right)) \Rightarrow ((\exists f: \operatorname{AddMonoidAlgebra}\left(\mathbb{C}, (\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right), \operatorname{IsPhi}\left(t, r, beta, f\right)) \land (\forall f: \operatorname{AddMonoidAlgebra}\left(\mathbb{C}, (\operatorname{Fin}\left(r\right) \to \mathbb{Z})\right), (\operatorname{IsPhi}\left(t, r, beta, f\right)) \Rightarrow ((f \ne 0) \Rightarrow (\exists mu: \operatorname{Fin}\left(r\right) \to \mathbb{Z}, (\operatorname{Dominant}\left(mu\right)) \land (\operatorname{newtonPolytope}\left(f\right) = \operatorname{orbitPolytope}\left(mu\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/marin-conjecture-8-1` (refuted) by `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marin-conjecture-8-1","declaration_gid":"D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Carles Marín (2026). *Schur polynomials twisted by roots of unity and reciprocal pairs: torsion filters, fusion quotients, and total unimodularity at odd order*. DOI: [10.48550/arXiv.2608.18302](https://doi.org/10.48550/arXiv.2608.18302). URL: <https://arxiv.org/abs/2608.18302v2>.

*Commentary.*

At t=3, r=2 and beta=(10,9,5,4,2,1,0), the alternant quotient has 33 nonzero Laurent monomials. Its support contains (4,0) and (3,3). Every point x in its Newton polytope satisfies x₀≤4, x₀+x₁≤6 and 3x₀+x₁≤12. If the polytope were one signed-permutation orbit hull with dominant generator mu, the first two maxima would force mu=(4,2). The third bound would then give 14≤12. Exact determinant identities establish the quotient and a nonzero denominator. This refutes the universal assertion with the full reciprocal alphabet. The denominator's single-orbit property and Conjecture 8.2 are not refuted here; no infinite-family theorem is asserted.

## References

- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.Dominant`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.IsPhi`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.N`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.NormalizedBeta`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.alphabetPower`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.claim`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.delta`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.denominator`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.newtonPolytope`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.numerator`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.orbitPolytope`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.result`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.signedOrbit`
- Truth anchor: `D5/S3/Geometry/NewtonPolytopes/TwistedSchurSingleOrbitRefutation.sourceIndex`
- Dependency: [D5/S3/Arith/InterlaceFan/Cyclotomic](../../Arith/InterlaceFan/Cyclotomic.md)
