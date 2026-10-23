# Granvik's Möbius and Mertens identities

## Abstract

The diagonal and first row of the Granvik Mertens array.

**Definition 1.1 (Somos's rational array).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{T}\left(n, k\right) \in \mathbb{Q}$$

*Formalization.* `D5/S3/Arith/GranvikMertensArray.T` (`✓ std3`).

*Citation.* Mats Granvik; Philippe Gérard; Michael Somos (2011). *OEIS A192763 and the Granvik Mertens array*. URL: <https://oeis.org/A192763>.

*Commentary.*

Indices are natural numbers; a cell with either index zero is zero. On positive indices, T(1,1)=1, T(2,1)=2, and symmetry gives T(n,k)=T(k,n) when k>n. For n at least three, the border update is T(n,1)=(-T(n-1,1)-sum over 2<=i<=n-1 of T(n,i))/(n+1)+T(n-1,1). For n>k>=2, T(n,k)=T(k,((n-1) mod k)+1). For n>=2, T(n,n) is the negative sum of T(n,i) over 1<=i<=n-1. All sums are finite and division is rational. A well-founded measure orders these recursive calls. This is Somos's program in OEIS A192763, with its corner normalization one.

**Theorem 1.2 (The diagonal and the Mertens row).**

$$(\forall n: \mathbb{N}, (1 \le n) \implies \operatorname{T}\left(n, n\right) = n \cdot \operatorname{mu}\left(n\right)) \land (\forall k: \mathbb{N}, (2 \le k) \implies \operatorname{T}\left(1, k\right) = 2 + \sum_{j \in \operatorname{Icc}\left(1, k\right)} \operatorname{mu}\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GranvikMertensArray.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a192763-granvik-mertens-array` (proved) by `D5/S3/Arith/GranvikMertensArray.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a192763-granvik-mertens-array","declaration_gid":"D5/S3/Arith/GranvikMertensArray.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mats Granvik; Philippe Gérard; Michael Somos (2011). *OEIS A192763 and the Granvik Mertens array*. URL: <https://oeis.org/A192763>.

*Commentary.*

Here mu is ArithmeticFunction.moebius, cast from integers to rationals. The first assertion includes the corner n=1; the second begins at k=2, exactly as in the two COMMENTS conjectures in OEIS A192763.

The proof constructs a symmetric model. A noncoprime interior cell has value gcd(n,k)*mu(gcd(n,k)); a coprime interior cell has the border value at the last Euclidean quotient. Signed Bézout identities identify that quotient with floor((n-1)/min(u,n-u)), where u is the inverse residue of k modulo n. Inversion and reflection permute the reduced residues. Möbius convolution evaluates their summed border values, and a gcd multiplicity identity supplies the other cells. The resulting row sum gives the required diagonal and border equations.

The proof also defines the first Granvik/Gérard Mathematica program literally, including its reverse-window sums. Periodicity and the zero diagonal row sum show that Somos's array satisfies this program. Well-founded uniqueness identifies both arrays and the arithmetic model. The companion Math.SE 50719 question prints a different corner; the theorem uses the OEIS programs' value one. No Mertens growth estimate follows from these identities.

## References

- Truth anchor: `D5/S3/Arith/GranvikMertensArray.T`
- Truth anchor: `D5/S3/Arith/GranvikMertensArray.result`
- Dependency: [D5/S3/Arith/RoldanCirculantEnergyP2Q3](RoldanCirculantEnergyP2Q3.md)
