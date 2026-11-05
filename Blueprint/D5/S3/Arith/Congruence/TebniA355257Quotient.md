# Tebni's prime quotient congruence

## Abstract

For even n and prime p, the quotient A(n,p)/(p-1) is an integer congruent to one modulo p.

**Definition 1.1 (The source quotient conjecture).**

$$claim = (\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (\exists q \in \mathbb{Z},\; ((q: \mathbb{Q}) = \frac{\operatorname{TebniA355257Divisibility}.\operatorname{A}\left(n, p\right)}{((p: \mathbb{Q}) - 1)}) \land (\operatorname{Int}.\operatorname{ModEq}\left((p: \mathbb{Z}), q, 1\right)))))$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA355257Quotient.claim` (`✓ std3`).

*Citation.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

OEIS A355257, revision 37, COMMENTS (unpaginated): "Conjecture: For p prime and n even, (A(n, p) / (p - 1)) == 1 (mod p)." The quotient is taken in Q. An integer q equal to that quotient expresses its integrality; Int.ModEq has integer modulus p. The row index is a natural number, including zero.

**Theorem 1.2 (The quotient congruence holds).**

$$\forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Even}\left(n\right)) \Rightarrow (\exists q \in \mathbb{Z},\; ((q: \mathbb{Q}) = \frac{\operatorname{TebniA355257Divisibility}.\operatorname{A}\left(n, p\right)}{((p: \mathbb{Q}) - 1)}) \land (\operatorname{Int}.\operatorname{ModEq}\left((p: \mathbb{Z}), q, 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA355257Quotient.result` (`✓ std3`). ∎

*Resolves.* `Problems/tebni355257-quotient` (proved) by `D5/S3/Arith/Congruence/TebniA355257Quotient.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tebni355257-quotient","declaration_gid":"D5/S3/Arith/Congruence/TebniA355257Quotient.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny and Mélika Tebni (2022). *OEIS A355257, logarithmic coefficient array and congruence conjectures*. URL: <https://oeis.org/A355257>.

*Commentary.*

The shared coefficient sum is divisible by p-1 for even n. Its residue modulo p is minus one. Writing that integer as (p-1)q and reducing modulo p gives -q=-1, hence q=1 modulo p.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Quotient.claim`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA355257Quotient.result`
- Dependency: [D5/S3/Arith/Congruence/TebniA355257Divisibility](TebniA355257Divisibility.md)
