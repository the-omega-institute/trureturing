# Kurkov's all-divisor conjecture for A386381

## Abstract

Every positive divisor of a term of the modified Entringer diagonal divides all terms at the corresponding arithmetic progression of indices.

**Definition 1.1 (The literal A386363 triangle).**

$$(\operatorname{triangle}\left(0, 0\right) = 1 \land \forall n: \mathbb{N}, (0 < n \Rightarrow (\operatorname{triangle}\left(n, 0\right) = 0 \land (\operatorname{triangle}\left(n, 1\right) = \operatorname{triangle}\left(n - 1, n - 1\right) \land \forall k: \mathbb{N}, (2 \le k \le n \Rightarrow \operatorname{triangle}\left(n, k\right) = \operatorname{triangle}\left(n, k - 1\right) + \left(n - 2\right) \cdot \operatorname{triangle}\left(n - 1, n - k\right))))))$$

*Formalization.* `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.triangle` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A386381 Conjecture 1: divisors of the modified Entringer diagonal*. URL: <https://oeis.org/A386381/internal>.

*Commentary.*

The natural array has T(0,0)=1 and T(n,0)=0 for positive n. For positive n its first value is T(n,1)=T(n-1,n-1). For 2<=k<=n its update is T(n,k)=T(n,k-1)+(n-2)*T(n-1,n-k). Natural subtraction in the coefficient agrees with integer subtraction in this range. The total Lean definition also assigns auxiliary values outside the row; the theorem uses the published triangular region. The n=0 clause has priority.

**Definition 1.2 (The diagonal sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{triangle}\left(n, n\right)$$

*Formalization.* `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.a` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A386381 Conjecture 1: divisors of the modified Entringer diagonal*. URL: <https://oeis.org/A386381/internal>.

*Commentary.*

The sequence is exactly a(n)=T(n,n), indexed from zero. In particular a(0)=a(1)=a(2)=1. The last update for n>=2 adds a multiple of T(n-1,0)=0, so a(n)=T(n,n-1). Every a(n) is positive.

**Theorem 1.3 (The complete first source conjecture).**

$$(\forall k: \mathbb{N}, \forall m: \mathbb{N}, \forall d: \mathbb{Z}, (0 < d \Rightarrow (d \mid \operatorname{a}\left(k\right) \Rightarrow d \mid \operatorname{a}\left(k + m \cdot \operatorname{toNat}\left(d\right)\right))) \land \forall k: \mathbb{N}, \forall m: \mathbb{N}, \operatorname{a}\left(k\right) \mid \operatorname{a}\left(k + m \cdot \operatorname{a}\left(k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a386381-divisor-propagation` (proved) by `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a386381-divisor-propagation","declaration_gid":"D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mikhail Kurkov (2025). *OEIS A386381 Conjecture 1: divisors of the modified Entringer diagonal*. URL: <https://oeis.org/A386381/internal>.

*Commentary.*

The first conjunct quantifies over k,m in N and positive d in Z, and uses integer divisibility. Int.toNat occurs only in the index k+m*d.toNat; positivity gives (d.toNat:Z)=d. The second conjunct is the source's a(k)-divisibility consequence over N, consumed directly in this conjunction using positivity of a(k). There is no finite cutoff or primality restriction. k=0, m=0 and d=1 are included. Conjecture 2 and A060818 are separate and are not asserted here.

For a rational polynomial f, S_N(f) is anchored at 1 with value zero and has backward difference f(N-X). It is constructed by applying the earlier frozen IntegerNewton.int_newton_of_fwdDiff_iter_eq_zero to the integer restriction of f(N-X), then replacing each binomial term by its backward antiderivative binom(X+1,j+1)-binom(2,j+1). Mathlib supplies the difference-vanishing bound, Pascal identity and Pochhammer polynomials.

Write Q(N,0)=1 and Q(N,j+1)=S_N(Q(N-1,j)). These polynomials have degree at most j and take integer values at every integer. Applying the same Newton reconstruction at order j+1 gives an integral polynomial for j!*Q(N,j), since i! divides j! for every i<=j. The implemented P(r), corresponding to source row n=r+2, is the sum over 0<=j<=r of r falling j times a(r+1-j) times Q(r+2,j). The identity r falling j=j!*choose(r,j) proves that P(r) has integer coefficients. This cancellation takes place over Q before reducing modulo d. Integer-valuedness by itself is never used as a period-d claim.

The row polynomial has value a(r+1) at 1 and backward difference r*P(r-1)(r+2-X) when r is positive. Induction identifies its evaluation with T(r+2,k) only for 1<=k<=r+1. Its evaluation at r+1 is a(r+2). No polynomial equality with the whole source row outside this interval is assumed.

For a positive modulus d, evaluate these integral polynomials in ZMod d. Their integer argument has period d. Induction on r proves P(r+d)(x)=a(d+1)*P(r)(x) pointwise at every integer x. At r=0 the backward differences vanish modulo d; the anchor is a(d+1). At the inductive step, the previous row relation and argument periodicity give both the anchor and the backward differences. Two-sided integer induction propagates equality to all arguments. The diagonal gives a(n+d)=a(d+1)*a(n) in ZMod d for positive n,d, and induction on m gives divisor propagation. If k=0, the hypothesis d|a(0)=1 forces d=1.

The Newton ingredient is classical and reused from the repository and pinned Mathlib. The reflected row construction and full source deduction are repository derived. No external Lean code is transplanted. Bounded literature searches are described in the Library note; global novelty and priority remain ASSUMED-UNVERIFIED.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.a`
- Truth anchor: `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.result`
- Truth anchor: `D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.triangle`
- Dependency: [D5/S3/VertexAlgebra/Analysis/IntegerNewton](../../../VertexAlgebra/Analysis/IntegerNewton.md)
