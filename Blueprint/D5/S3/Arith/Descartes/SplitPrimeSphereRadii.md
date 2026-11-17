# The split-prime clause of A390148

## Abstract

Shared split-prime powers in primitive spherical Descartes radii.

**Theorem 1.1 (One or two other coordinates at every positive threshold).**

$$\forall r:\operatorname{Fin}(4)\to\mathbb{N},((\forall i,0<r_i) \land \gcd(r)=1 \land (\sum_i\frac{1}{r_i})^{2}=3\sum_i(\frac{1}{r_i})^{2}) \implies \forall p\in\mathbb{N},(\operatorname{Prime}(p) \land p\operatorname{mod}3=1) \implies \forall k\in\mathbb{N},0<k \implies \forall i\in\operatorname{Fin}(4),p^{k}\mid r_i \implies (\lvert\{j\in\operatorname{Fin}(4):j\neq i \land p^{k}\mid r_j\}\rvert=1 \lor \lvert\{j\in\operatorname{Fin}(4):j\neq i \land p^{k}\mid r_j\}\rvert=2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Descartes/SplitPrimeSphereRadii.result` (`✓ std3`). ∎

*Resolves.* `Problems/hohn-a390148-split-prime-shared-divisibility` (proved) by `D5/S3/Arith/Descartes/SplitPrimeSphereRadii.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hohn-a390148-split-prime-shared-divisibility","declaration_gid":"D5/S3/Arith/Descartes/SplitPrimeSphereRadii.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Charles L. Hohn (2025). *A390148 — primitive radii of four mutually tangent spheres and a plane*. URL: <https://oeis.org/A390148>.

*Commentary.*

The four radii are positive natural numbers with common gcd one. The reciprocal equation is over the rationals. Both i and j range over Fin(4), so equal radii count as separate coordinates. No ordering or pairwise coprimality is assumed. The exponent k is any positive natural number.

Use the least common multiple L and the integer curvatures b(i)=L/r(i) from PrimitiveSphereRadii. Their common gcd is one, and their sum squared equals three times the sum of their squares. If all coordinates other than i vanished modulo an odd prime p, primitivity would make b(i) nonzero. The equation would make twice the square of b(i) zero modulo p, a contradiction.

There is therefore a coordinate j distinct from i whose curvature is coprime to p. The identity b(a)r(a)=L gives v_p(b(a))+v_p(r(a))=v_p(L). Thus r(j) has at least the valuation of r(i), so it is divisible by p to the k. Common gcd one excludes divisibility of all four radii by this positive power. The number of other coordinates is consequently one or two. The separate inert-prime valuation, 3-adic valuation, repetition and chain assertions are outside this statement.

## References

- Truth anchor: `D5/S3/Arith/Descartes/SplitPrimeSphereRadii.result`
- Dependency: [D5/S3/Arith/Descartes/PrimitiveSphereRadii](PrimitiveSphereRadii.md)
