# Spezia’s second exterior trace

## Abstract

The second exterior trace of the serpentine matrix has Spezia’s magnitude.

**Definition 1.1 (Signed characteristic coefficient).**

$$\forall (R: \operatorname{Type}), [\operatorname{CommRing}\left(R\right)] \forall (n: \mathbb{N}), \forall (k: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), R\right)), \operatorname{traceExt}\left(k, A\right) = (\operatorname{if} k \le n \operatorname{then} (-1)^{k} \cdot \operatorname{Polynomial.coeff}\left(\operatorname{Matrix.charpoly}\left(A\right), n - k\right) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.traceExt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

The exterior trace is the signed characteristic coefficient when k ≤ n and zero when k > n. Natural subtraction in the coefficient index is truncated. R is any commutative ring.

**Definition 1.2 (The integer serpentine matrix).**

$$\forall (n: \mathbb{N}), \operatorname{M}\left(n\right) = (fun (i: \operatorname{Fin}\left(n\right)) \mapsto (fun (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{if} \operatorname{Odd}\left(\operatorname{val}\left(i\right) + 1\right) \operatorname{then} (\operatorname{Nat.cast}\left(\operatorname{val}\left(j\right)\right): \mathbb{Z}) + 1 + (\operatorname{Nat.cast}\left(n\right): \mathbb{Z}) \cdot ((\operatorname{Nat.cast}\left(\operatorname{val}\left(i\right)\right): \mathbb{Z}) + 1 - 1) \operatorname{else} (\operatorname{Nat.cast}\left(n\right): \mathbb{Z}) \cdot ((\operatorname{Nat.cast}\left(\operatorname{val}\left(i\right)\right): \mathbb{Z}) + 1) - ((\operatorname{Nat.cast}\left(\operatorname{val}\left(j\right)\right): \mathbb{Z}) + 1) + 1)))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.M` (`✓ std3`).

*Citation.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

A322844 COMMENTS, revision 68, unpaginated: “For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n square matrix M(n) defined as M[i,j,n] = j + n*(i-1) if i is odd and M[i,j,n] = n*i - j + 1 if i is even (see A317614). Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-2)] in the characteristic polynomial of the matrix M(n), or the absolute value of the sum of all principal minors of M(n) of size 2.” The source indices are val(i)+1 and val(j)+1; all entries are integers.

**Definition 1.3 (The sequence value).**

$$\forall (n: \mathbb{N}), \operatorname{a}\left(n\right) = \frac{1}{12} \cdot (\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2} \cdot (3 \cdot (1 + (\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2}) - 2 \cdot (2 + (\operatorname{Nat.cast}\left(n\right): \mathbb{Q})^{2}) \cdot (\operatorname{Nat.cast}\left(\operatorname{Nat.mod}\left(n, 2\right)\right): \mathbb{Q}))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.a` (`✓ std3`).

*Citation.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

A322844 FORMULA, revision 68, unpaginated: “a(n) = (1/12)*n^2*(3*(1 + n^2) - 2*(2 + n^2)*(n mod 2)).” The expression is evaluated in the rationals, and Nat.mod is natural remainder.

**Definition 1.4 (Spezia’s first conjecture).**

$$claim \Leftrightarrow (\forall (n: \mathbb{N}), (1 < n) \Rightarrow ((\operatorname{Int.cast}\left(\operatorname{abs}\left(\operatorname{traceExt}\left(2, \operatorname{M}\left(n\right)\right)\right)\right): \mathbb{Q}) = \operatorname{a}\left(n\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.claim` (`✓ std3`).

*Citation.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

A322844 COMMENTS, revision 68, unpaginated: “For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n square matrix M(n) defined as M[i,j,n] = j + n*(i-1) if i is odd and M[i,j,n] = n*i - j + 1 if i is even (see A317614). Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-2)] in the characteristic polynomial of the matrix M(n), or the absolute value of the sum of all principal minors of M(n) of size 2.” Here n ranges over natural orders, 1 < n is the only guard, and the integer absolute trace is cast to the rationals.

**Definition 1.5 (Centered column coordinate).**

$$\forall (n: \mathbb{N}), \forall (i: \mathbb{N}), \operatorname{w}\left(n, i\right) = (\operatorname{Nat.cast}\left(i\right): \mathbb{Q}) + 1 - \frac{(\operatorname{Nat.cast}\left(n\right): \mathbb{Q}) + 1}{2}$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.w` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the midpoint centers the one-based column coordinate.

**Definition 1.6 (Affine row coordinate).**

$$\forall (n: \mathbb{N}), \forall (i: \mathbb{N}), \operatorname{u}\left(n, i\right) = (\operatorname{Nat.cast}\left(n\right): \mathbb{Q}) \cdot ((\operatorname{Nat.cast}\left(i\right): \mathbb{Q}) + 1) - \frac{(\operatorname{Nat.cast}\left(n\right): \mathbb{Q}) - 1}{2}$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row coordinate has slope n and midpoint correction (n−1)/2.

**Definition 1.7 (The n by two factor).**

$$\forall (n: \mathbb{N}), \operatorname{U}\left(n\right) = (fun (i: \operatorname{Fin}\left(n\right)) \mapsto (fun (j: \operatorname{Fin}\left(2\right)) \mapsto (\operatorname{if} j = 0 \operatorname{then} \operatorname{u}\left(n, \operatorname{val}\left(i\right)\right) \operatorname{else} (-1)^{\operatorname{val}\left(i\right)})))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two entries in each row are the affine coordinate and the alternating sign, over the rationals.

**Definition 1.8 (The two by n factor).**

$$\forall (n: \mathbb{N}), \operatorname{V}\left(n\right) = (fun (i: \operatorname{Fin}\left(2\right)) \mapsto (fun (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{if} i = 0 \operatorname{then} 1 \operatorname{else} \operatorname{w}\left(n, \operatorname{val}\left(j\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two entries in each column are one and the centered coordinate, over the rationals.

**Theorem 1.9 (Reduction to two dimensions).**

$$\forall (n: \mathbb{N}), (2 \le n) \Rightarrow (\operatorname{Matrix.charpoly}\left(\operatorname{Matrix.map}\left(\operatorname{M}\left(n\right), \operatorname{Int.castRingHom}\left(\mathbb{Q}\right)\right)\right) = \operatorname{Polynomial.X}^{(n - 2)} \cdot \operatorname{Matrix.charpoly}\left((\operatorname{V}\left(n\right) \cdot \operatorname{U}\left(n\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.charpoly_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n ≥ 2 the rectangular product identity factors the characteristic polynomial into X^(n−2) and the characteristic polynomial of V(n)U(n). It also gives all higher exterior traces.

**Theorem 1.10 (The second trace has the stated magnitude).**

$$\forall (n: \mathbb{N}), (1 < n) \Rightarrow ((\operatorname{Int.cast}\left(\operatorname{abs}\left(\operatorname{traceExt}\left(2, \operatorname{M}\left(n\right)\right)\right)\right): \mathbb{Q}) = \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.result` (`✓ std3`). ∎

*Resolves.* `Problems/sp322844-serpentine` (proved) by `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sp322844-serpentine","declaration_gid":"D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stefano Spezia (2018). *OEIS A322844 and the serpentine matrix A317614*. URL: <https://oeis.org/A322844>.

*Commentary.*

The second characteristic coefficient is −a(n). The four centered moments evaluate its two by two determinant, and parity gives a(n) ≥ 0. Taking the absolute value proves the formula for every n > 1.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.M`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.U`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.V`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.a`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.charpoly_factor`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.result`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.traceExt`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.u`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.w`
- Dependency: [D5/S3/Combinatorics/Permanental/SunAbsoluteDifferenceCongruences](../../Combinatorics/Permanental/SunAbsoluteDifferenceCongruences.md)
