# A396808: exact support modulo three

## Abstract

The two modulo-three support conjectures for OEIS A396808 hold at every index greater than one.

**Theorem 1.1 (Complete coefficient classification).**

$$\forall n: \mathbb{N}, 1 < n \Rightarrow \operatorname{cast}\left(\operatorname{ZMod}\left(3\right), \operatorname{a}\left(n\right)\right) = \operatorname{ite}\left(\exists r: \mathbb{N}, n = 3^{r}, 2, \operatorname{ite}\left(\exists i, j: \mathbb{N}, i < j \land 2 n = 3(3^{i} + 3^{j}), 1, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/TernaryTraceSupport.a396808_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396808, an implicit power-series coefficient equation*. URL: <https://oeis.org/A396808>.

*Commentary.*

The integer sequence a is the existing normalized solution of (n+1)[x^n]A^(n+1)=n[x^n]A^(n+2), with a(0)=a(1)=1. All quantified indices and exponents below are natural numbers. The cast is into ZMod(3), and ite denotes a conditional expression.

Set t(y)=sum over r of y^(3^r). Frobenius gives t^3=t-y. The series U=1+y^2-t^6 equals 1+t^2+t^4 and has only even exponents, so U=R(y^2). Its companion roots are (t^2+t)^2 and (t^2-t)^2. All three satisfy z^3=z^2+y^2*z+y^4.

Their mth-power sum is a polynomial in y^2 of degree at most floor(2m/3). The companion roots have order at least two. It follows that coefficient n of R^m vanishes when floor(2m/3)<n<m. This proves the reduced source equation, with explicit checks of its three initial indices. Strict-prefix coefficient induction then identifies R with a modulo three.

A sum of two powers of three determines its sorted exponent pair uniquely. In the square of t, equal exponents contribute once and distinct exponents twice. The minus sign in U gives residues two and one, respectively. The two supports are disjoint: after cancelling a factor of three, an intersection would identify a diagonal exponent pair with a strictly increasing pair.

## References

- Truth anchor: `D5/S3/Arith/TernaryTraceSupport.a396808_mod_three`
- Dependency: [D5/S3/Arith/ArtinSchreierTracePowersOfTwo](ArtinSchreierTracePowersOfTwo.md)
