# The Sixth-Iterate Exponential Congruence Modulo Six

## Abstract

The positive-index coefficients of OEIS A396806 agree with their indices modulo six.

Let A be the unique rational formal power series with zero constant coefficient satisfying A=X*exp(A^{[6]}), where A^{[6]} denotes the sixth compositional iterate. Write a(n)=n![X^n]A. The existing A_equation and fixed_unique in IterateExponentialParity identify A with AK(6) and a(n) with its natural sequence aK(6,n).

**Theorem 1.1 (Hanna's congruence for every positive index).**

$$\forall n:\mathbb{N}, 1\leq n\implies \operatorname{aK}\left(6, n\right) \bmod 6=n \bmod 6$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialModSix.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396806-iterate-exponential-mod-six` (proved) by `D5/S1/Recurrence/Residue/IterateExponentialModSix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396806-iterate-exponential-mod-six","declaration_gid":"D5/S1/Recurrence/Residue/IterateExponentialModSix.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396806: iterated-exponential congruences*. URL: <https://oeis.org/A396806>.

*Commentary.*

The conclusion is the pattern 1, 2, 3, 4, 5, 0 repeating modulo six from index one. Since three divides six, it also gives the entry's modulo-three pattern 1, 2, 0.

Work with integral exponential coefficients modulo three and put l(n)=n. Composition on the right by l acts as the binomial transform T(f)(n)=sum_j binomial(n,j)f(j)j^(n-j). After j transforms, the coefficient at 3q is zero and that at 3q+1 is (j+1)^q. Hence the sixth compositional iterate has zero coefficients at 3q, and at 3q+1 has value one when q=0 and zero otherwise. Its coefficients at 3q+2 need not vanish.

For any inner sequence with these support properties, the outer exponential has coefficient one at both 3q and 3q+1. Its recurrence over three consecutive indices cancels the unrestricted residue-two terms in characteristic three. The leading index factor therefore makes the defining operator preserve l modulo three. Induction through the stabilizing approximations gives the congruence for aK(6,n). The existing modulo-two congruence and coprimality of two and three then give the stated modulo-six conclusion.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialModSix.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateExponentialParity](IterateExponentialParity.md)
