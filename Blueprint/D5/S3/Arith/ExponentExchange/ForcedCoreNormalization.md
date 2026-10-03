# Mandatory-Core Prime Prefix Normalization

## Abstract

A constrained divisor-sum maximum has an exact ordered prime-prefix representative.

Let q(i) be the i-th prime strictly above one, so q(0)=2. S(i,t) is RoughPrimeSuffixBellman.suffixNumber 1 i t, and W(i,t) is RoughPrimeSuffixBellman.suffixWeight 1 i t. Ordered(h,t) is the supplier's positive, nonincreasing list predicate with first exponent at most h. The empty list is ordered and S(i,[]) = W(i,[]) = 1. The symbol v(n,p) means Nat.factorization n at p; Z(n) means the real ratio ArithmeticFunction.sigma 1 n divided by n. c(B) means rootCap 1 B. The input ell is any finite list of natural exponents satisfying Ordered(headD(ell,0),ell); this is exactly a positive nonincreasing mandatory profile, including the empty profile.

**Theorem 1.1 (Attainment in the mandatory-divisor fiber).**

$$\begin{aligned}\forall ell:List\left(\mathbb{N}\right), Ordered\left(headD\left(ell, 0\right), ell\right)\Rightarrow \forall B:\mathbb{N},\\\operatorname{let} M:\mathbb{N} := S\left(0, ell\right); [\\(B<M\Leftrightarrow\neg(\exists n:\mathbb{N}, 1\le n\land n\le B\land dvd\left(M, n\right)))\\\land (M\le B\Rightarrow \exists n:\mathbb{N},\exists t:List\left(\mathbb{N}\right),\\1\le n\land n\le B\land dvd\left(M, n\right)\\\land (\forall p,q:\mathbb{N},Prime\left(p\right)\land Prime\left(q\right)\land p<q\Rightarrow v\left(n, q\right)\le v\left(n, p\right))\\\land Ordered\left(c\left(B\right), t\right)\land S\left(0, t\right)=n\land Z\left(n\right)=W\left(0, t\right)\\\land (\forall m:\mathbb{N},1\le m\land m\le B\land dvd\left(M, m\right)\Rightarrow Z\left(m\right)\le Z\left(n\right)))]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ExponentExchange/ForcedCoreNormalization.forced_core_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such ell and every natural budget B, M is the exact consecutive-prime core S(0,ell). The first equivalence states that B<M exactly when there is no positive multiple of M in [1,B]. If M<=B, the existential witness n is an actual constrained maximizer. Its total valuations are antitone across every pair of distinct primes p<q. The list t represents that same integer, has positive nonincreasing entries, and is bounded at the head by c(B). Its suffix weight equals the actual sigma ratio. The last universal clause compares n with every positive multiple of M within the budget.

The proof selects a maximum from the finite constrained fiber. A strict valuation inversion would admit IntegerSwap's smaller integer with a larger normalized divisor sum. Factorization of the mandatory list and its antitone profile show that this swap preserves divisibility by the whole M, including when the smaller valuation is zero. This contradicts maximality. The supplier's prime enumeration and factorization product then reconstruct the same n from its positive valuation prefix; its sigma identity gives the exact W value. No coprimality or multiplicative identity between M and a quotient of n is assumed.

This theorem covers B=0, B=M, M=1, and the empty exponent list. It proves the normalization assertion of source theorem 91.1. It supplies no forced-suffix Bellman recurrence or 91.2 pruning claim.

## References

- Truth anchor: `D5/S3/Arith/ExponentExchange/ForcedCoreNormalization.forced_core_normalization`
- Dependency: [D5/S3/Arith/ExponentExchange/RoughPrimeSuffixBellman](RoughPrimeSuffixBellman.md)
