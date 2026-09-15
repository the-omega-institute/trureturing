# The Third-Iterate Exponential Congruence Modulo Three

## Abstract

The positive-index coefficients of OEIS A396803 agree with their indices modulo three.

Let A be the unique rational formal power series with zero constant coefficient satisfying A=X*exp(A composed with A composed with A). The exponent contains the third compositional iterate. Write a(n)=n![X^n]A. The existing sequence aK(3,n) and series AK(3) in IterateExponentialParity satisfy this equation by A_equation, and fixed_unique identifies every zero-constant solution with AK(3). Thus a(n)=aK(3,n).

Work with integral exponential-generating coefficients modulo three, with composition defined by the integral chain-rule recurrence. Put l(n)=n and g=l composed with l composed with l. Substitution by X*exp(X) sends f(n) to the sum over j from zero to n of binomial(n,j)*f(j)*j^(n-j). Lucas decomposition preserves the subsequence at indices 3q and makes the subsequence at indices 3q+1 a binomial transform. Two transforms of the constant-one subsequence give 3^q. Consequently g(3q)=0 and g(3q+1) is one for q=0 and zero otherwise; no condition on g(3q+2) is needed.

**Theorem 1.1 (Hanna's congruence for every positive index).**

$$\forall n:\mathbb{N}, 1\leq n\implies \operatorname{aK}\left(3, n\right) \bmod 3=n \bmod 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialModThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396803-iterate-exponential-mod-three` (proved) by `D5/S1/Recurrence/Residue/IterateExponentialModThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396803-iterate-exponential-mod-three","declaration_gid":"D5/S1/Recurrence/Residue/IterateExponentialModThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2026). *OEIS A396803, A396805 and A396806: iterated-exponential congruences*. URL: <https://oeis.org/A396803>.

*Commentary.*

For any g with the two support properties above, let E be the integral composition of the constant-one sequence with g. This is the exponential coefficient transformation. The composition recurrence gives E(3q+1)=E(3q), E(3q+2)=E(3q)+S and E(3q+3)=E(3q+2)+2S, with the same auxiliary sum S. Since 3S=0, induction gives E(3q)=E(3q+1)=1. The coefficient transformation for X*exp(A composed with A composed with A) therefore fixes l: at the remaining indices its leading factor is zero modulo three. Induction through every approximation stage, followed by coefficient stabilization, proves the displayed congruence for all n at least one.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialModThree.result`
- Dependency: [D5/S1/Recurrence/Residue/IterateExponentialParity](IterateExponentialParity.md)
