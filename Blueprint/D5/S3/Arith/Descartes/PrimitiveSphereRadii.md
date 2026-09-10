# The 3-adic clause of A390148

## Abstract

The 3-adic orders of primitive spherical Descartes radii.

**Theorem 1.1 (One zero order and three equal positive orders).**

$$\forall r:\operatorname{Fin}(4)\to\mathbb{N},((\forall i,0<r_i) \land \gcd(r)=1 \land (\sum_i\frac{1}{r_i})^{2}=3\sum_i(\frac{1}{r_i})^{2}) \implies \exists e\in\mathbb{N},0<e \land \lvert\{i:v_3(r_i)=e\}\rvert=3 \land \forall i,(v_3(r_i)=0 \lor v_3(r_i)=e)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Descartes/PrimitiveSphereRadii.primitive_sphere_radii_v3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Charles L. Hohn (2025). *A390148 — primitive radii of four mutually tangent spheres and a plane*. URL: <https://oeis.org/A390148>.

*Commentary.*

The index i ranges over four coordinates. The radii are positive natural numbers, and gcd means their common gcd, without pairwise coprimality. The reciprocal equation is interpreted over the rationals. The function v with subscript 3 is the natural 3-adic valuation. No ordering is assumed.

Let L be the least common multiple of the radii and put b(i)=L/r(i). These are positive integers with common gcd one. Indeed, if d divides every b(i), then every radius divides L/d. Minimality of L forces d=1. Multiplying the reciprocal equation by L squared gives the same coefficient-three equation for the integer curvatures b.

The equation first makes the sum of b divisible by three, and then makes the sum of its squares divisible by three. A nonzero residue modulo three has square one. Consequently the number of unit coordinates is a positive multiple of three at most four, hence three.

The product b(i)r(i)=L gives v3(b(i))+v3(r(i))=v3(L). Thus the three unit curvatures correspond to three radii of the largest order e. Order e cannot be zero, since that would give four such radii. Primitivity supplies a radius of order zero, which occupies the single remaining coordinate. The OEIS entry states this clause as a conjecture; its other prime conditions, repetition formula and chain conjecture are separate.

## References

- Truth anchor: `D5/S3/Arith/Descartes/PrimitiveSphereRadii.primitive_sphere_radii_v3`
