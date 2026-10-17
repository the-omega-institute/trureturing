# Hanna's Arithmetic-Subsequence Closure

## Abstract

Integral logarithmic series remain integral under every positive affine extraction.

Let K be any characteristic-zero field and L any sequence from the natural numbers to K. All indices and ordinary degrees start at zero. Write egf(L)=sum_n L(n)X^n/n! and logarithmicTransform(L)=egf(L).subst(log(K)), where log(K) is the formal log(1+X). IntegralSeries means that every ordinary coefficient belongs to the canonical image of Z in K. No convergence, sign, support, degree bound or normalization of L(0) is imposed.

**Theorem 1.1 (The full A167540 implication).**

$$\forall K: Type, [\operatorname{Field}\left(K\right)] [\operatorname{CharZero}\left(K\right)] \forall L: \mathbb{N} \to K, \forall m: \mathbb{N}, \forall b: \mathbb{N}, (\operatorname{IntegralSeries}\left(\operatorname{logarithmicTransform}\left(L\right)\right)) \implies ((0 < m) \implies (\operatorname{IntegralSeries}\left(\operatorname{logarithmicTransform}\left((n: \mathbb{N} \mapsto \operatorname{L}\left(m \cdot n + b\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a167540-logarithmic-affine-closure` (proved) by `D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a167540-logarithmic-affine-closure","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure.result","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2009). *Hanna's logarithmic integer-series arithmetic-subsequence conjecture*. URL: <https://oeis.org/A167540>.

*Commentary.*

If the whole input transform is integral, the whole transform of n -> L(m*n+b) is integral for every positive m and every nonnegative b. Positive naturals represent exactly the source's positive integers, and b ranges over all naturals.

Put q_k(N)=k!S(N,k). Original exp/log inversion and reconstruction supply an integer sequence a with L(N)=sum_(k<=N) a(k)q_k(N); integral values of L are derived from the premise. Factorial-weighted inclusion-exclusion and exp(Q)^t=rescale(t,exp(Q)) identify the affine column's rational EGF as sum_(j<=k) (-1)^(k-j) binomial(k,j) j^b exp(Q)^(j^m). The original subst_exp_log identity then turns its logarithmic transform into the integer polynomial P_(k,m,b)=sum_(j<=k) (-1)^(k-j) binomial(k,j) j^b (1+X)^(j^m). All zero bases and exponents retain 0^0=1.

At an arbitrary degree r, log(K)^n contributes only for n<=r. The original finite-window identity expands T(a,m*n+b) using k<=m*r+b, since m*n+b<=m*r+b. Both sums are therefore finite, and the coefficient equals the integer sum sum_(k<=m*r+b) a(k) coeff(r,P_(k,m,b)). This is a bound for each arbitrary degree, with no bound on the whole series. The canonical rational-map compatibility transports this identity into K. At degree zero the output constant is L(b); when b=0 it retains arbitrary L(0). Signed and infinitely supported coordinates a are included.

The original finite-sum suppliers coeff_transform and T_window are applied directly.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure.result`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](HannaLogarithmicPowerClosure.md)
