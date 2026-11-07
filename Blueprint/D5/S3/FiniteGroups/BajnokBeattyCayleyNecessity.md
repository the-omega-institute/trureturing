# An affine odd square detects the necessary congruences

## Abstract

Necessary congruences for arbitrary signed covering pairs in the even-radius top strip.

**Theorem 1.1 (Every covering pair forces an even deficit).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity.top_strip_necessity`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity.top_strip_necessity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bela Bajnok and W. Kyle Beatty (2025). *On the diameter of undirected Cayley graphs of finite abelian groups*. DOI: [10.2140/cnt.2025.14.1](https://doi.org/10.2140/cnt.2025.14.1). URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let t,r be integers and k a natural number with t ≥ 1, 0 ≤ r < t and k=2t²−r. For any a,b in Z/2 × Z/(2k), suppose every g can be written as x•a+y•b for integers x,y with |x|+|y| ≤ 2t. Then 2 divides r; if t is odd, 4 divides r. No distinctness assumption or prescribed form of the pair is needed.

Write f(x,y)=x•a+y•b. Coverage makes f surjective, and reduction to the two-dimensional quotient modulo 2 forces every relation in ker f to have even coordinates. The odd affine coefficient class is a torsor: its sum-and-difference coordinates give an exact square of side 2t after translation. Its relation lattice is ker(f composed with (u,v)↦(u+v,u−v)), whose actual quotient index is 2k=(2t)²−2r. The strict top-strip bound permits near-square rigidity with n=2t and δ=2r.

The resulting basis has displacement parameters a₀,b₀ with a₀b₀=2r. Relation parity makes both parameters even, so r is even. If t is odd and r is not divisible by 4, both half-displacements are odd. The sum-and-difference images of the basis then force all of ker f into 4Z². This contradicts 2-primary primitivity: a preimage of (1,0) has a double in ker f, and divisibility of that double by 4 would make the preimage even, impossible in the first Z/2 coordinate.

This supplies the necessary congruences for arbitrary pairs in the stated top strip of Bajnok–Beatty Conjecture 4.1. The source comparison is arXiv:2406.04045v1, Theorems 4.2–4.4; the revised paper has not been read. The theorem alone is not the full conjecture or a classification outside this range, and it makes no claim of literature novelty.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity.top_strip_necessity`
- Dependency: [D5/S3/FiniteGroups/NearSquareLatticeRigidity](NearSquareLatticeRigidity.md)
