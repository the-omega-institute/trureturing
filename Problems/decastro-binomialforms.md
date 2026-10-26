---
slug: decastro-binomialforms
bibkey: decastro2022binomialorders
doi: null
url: https://math.colgate.edu/~integers/w61/w61.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/DeCastroIntegersConjecture1
---

# de Castro's admissible binomial fractions

## Problem

D. T. de Castro, *p-Adic order of positive integers via binomial coefficients*, INTEGERS 22, #A61, Section 3, Conjecture 1:

> Given any admissible set S_{p,n}, the p-adic order of a positive integer n can be expressed as v_p(n) = log_p(n / L_{p,n}), where L_{p,n} represents the least common denominator of the elements of S_{p,n}.

The source's Definition 2 puts $\binom{n}{k}/n$ in $S^{\max}_{p,n}$ when $0<k\le n$ and $\gcd(k,p)=1$. Its lower set $S^{\min}_{p,n}$ uses $k=p_i^j\le n$, with $i\ge1$, $j\ge0$ and $\gcd(p_i^j,p)=1$. Definition 3 requires $S^{\min}_{p,n}\subseteq S\subseteq S^{\max}_{p,n}$. Here $p$ is prime and $n\ge1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The fraction $\binom{n}{k}/n$ | `frac` | The literal rational expression $(1/n)\binom{n}{k}$; rationals are reduced. |
| Positive prime index and nonnegative exponent | `Smin` | `Nat.nth Nat.Prime (i - 1)`, $i\ge1$, $j\in\mathbb N$; natural subtraction. |
| Upper index range and coprimality | `Smax` | $0<k\le n$ and $\gcd(k,p)=1$. |
| Both inclusions | Literal conjunction in `claim` | Finset-to-Set coercion preserves both inclusions; the private lcm proof uses the identical defining condition of `Set.Icc` membership. |
| Prime $p$, positive $n$, every admissible $S$ | `claim`, `result` | All quantifiers and hypotheses remain; $S$ is finite because the upper set is finite. |
| $v_p(n)=\log_p(n/L_{p,n})$ | `claim`, `result` | `padicValNat`, `Real.logb`, and `Finset.lcm Rat.den`, with natural-to-real casts. |

There are no additional mathematical hypotheses. `frac` is a total rational expression, including at $n=0$; the settlement restricts to $n\ge1$.

## Motivation

The conjecture identifies the same denominator lcm for every intermediate admissible set. The formal motivation is `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.result`; preregistration is issue #18681. The source note is `Library/Factorization/decastro2022binomialorders.md`.

## Gap

The source states Conjecture 1 without a proof. The preregistration's literature screen covers the source paper, OEIS A343249–A343253 and A345531, and arXiv:2209.14236v11. No settlement was found in that searched scope. Literature completeness and publication priority are `ASSUMED-UNVERIFIED`.

## Route

Write $d(n,k)$ for the reduced denominator of $\binom{n}{k}/n$. The identity $\binom{n}{k}/n=\binom{n-1}{k-1}/k$ gives $d(n,k)\mid\gcd(n,k)$. Iterated Lucas congruences show $\binom{r^jm-1}{r^j-1}\equiv1\pmod r$ for a prime $r$ and positive $m$. Thus $d(n,r^j)=r^j$ whenever $r^j\mid n$, including $j=0$.

For prime $p$, every denominator in the upper set divides the $p$-free part $T=n/ p^{v_p(n)}$. Every prime power dividing $T$ occurs as a denominator in the lower set. Therefore the lcm of every intermediate set is $T$. The identity $p^{v_p(n)}T=n$ gives the logarithmic equation. The elaborated proof uses `Rat.den_dvd`, `Nat.add_one_mul_choose_eq`, Lucas congruence, prime-power divisibility and `Real.logb_eq_iff_rpow_eq` through the module's helpers.

## Falsifier

A prime $p$, positive $n$, and admissible finite $S$ whose denominator lcm differs from `n.divMaxPow p` would contradict the proved statement. Replacing coprimality with exclusion of multiples at a composite base changes the question.

## Evidence

The Lean module is `D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.lean`, with settling theorem `result : claim`. Its denominator saturation theorem is `den_prime_pow`; its internal `admissible_lcm` establishes the lcm identity. The public declaration axiom closures are restricted to `propext`, `Classical.choice` and `Quot.sound`.

Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21956. The targets are `den_dvd_k`, `den_dvd_gcd`, `den_prime_pow`, `logarithm_iff` and `result` in this module. No validated four-slot registration is asserted.

### Exact computation

Experiment: [de Castro binomial orders](https://github.com/the-omega-institute/trureturing-experiments/tree/868cd5a4bfc892973540526d582483fba6d039c1/docs/reports/oeis-a343249-a343253-a345531-de-castro-p-adic-order).

The script is `check.py` at commit `868cd5a4bfc892973540526d582483fba6d039c1`, SHA-256 `edd3b71e1df8d451fd19a771e0d82b399c4f32d27370de96a9c69a0082007706`. The command `python3 /Users/auric/.sshx/e4c876a8ab450c29c9d841cb/attempt-1/check.py 400 200` exits 0 with `RESULT PASS`; this file is the exact script extracted from that commit.

The readings check A343249–A343253 and denominator identities through $n\le400$; C1 for primes $p\le13$, $n\le400$; C2 in 99 cases with composite $q\le30$, $c\le2$; and the A345531 first failure for every composite $q\le200$. No unbounded conclusion follows from these computations.

## Triage

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| C1 and its lcm identity | Proved; kernel-checked `result` and internal `admissible_lcm` | For prime $p$, positive $n$ and every admissible $S$, the lcm is `n.divMaxPow p`; hence C1. |
| C2 at $n=q^cp_j$ | Proved in prose below | For composite $q>1$, prime $p_j\mid q$ and $c\ge0$, every admissible set has lcm 1 and the logarithmic formula fails. This is not a Lean settlement in this module. |
| A345531 first failure with $q\nmid k$ | Proved in prose below | For every composite $q$, first failure is $qP$, where $P$ is the first prime power above $\minFac(q)$; every smaller positive input admits a successful cutoff. This is not a Lean settlement in this module. |
| Prime-power denominator saturation | Proved; kernel-checked `den_prime_pow` | Every prime $r$, positive $n$ and $r^j\mid n$, including $j=0$. |
| Supplied checker | Computed; exact computation above | Precisely the four bounded ranges recorded above; command exit 0 and immutable script SHA-256 given above. |
| DC-3, full composite feasibility, neighbouring sequence identifications | Open | No formal settlement here for the complete prime-by-prime cutoff-lcm formula, the full composite-$q$ feasibility criterion or unbounded A343249–A343253 identifications. |

### Composite-base C2: proof in prose

Let $n=q^cp_j$ with prime $p_j\mid q$ and composite $q>1$. If $\gcd(k,q)=1$, then $\gcd(k,n)=1$. The denominator divisor bound gives $d(n,k)=1$, so every admissible set has lcm 1. Since $q\nmid p_j$, the largest exponent for which $q^e\mid n$ is $c$. However $\log_q n=c+\log_q p_j>c$, proving the failure asserted by C2. The argument also covers $c=0$. It depends on the gcd-based admissibility of the paper, not the OEIS exclusion $q\nmid k$.

### A345531 first failure: proof in prose

Put $p=\minFac(q)$ and let $P$ be the least prime power greater than $p$. There is a prime strictly between $p$ and $p^2$ (for $p=2$, use 3; for $p\ge3$, Bertrand's bound suffices). Thus $p<P<p^2$, and $P=r^a$ for some prime $r\ne p$. In particular, $q\nmid P$.

For the OEIS convention let $L(q,K,n)$ be the lcm over $1\le k\le K$ with $q\nmid k$. At $n=qP$, the $q$-adic order is 1, so a successful cutoff would require $L(q,K,qP)=P$. If $K\ge p$, the permitted index $p$ has denominator $p$, contradicting $p\nmid P$. If $K<p$, the prime power $P$ cannot divide that lcm: whenever a positive power $r^a$ divides a finite denominator lcm, it divides one denominator, hence divides its index $k$ by the denominator bound, and therefore $P\le K$. Both cases are impossible.

Now let $1\le n<qP$. If $q\nmid n$, choose $K=n$. Every prime power dividing $n$ is a permitted index, and saturation gives $L=n$; the $q$-adic order is 0. Otherwise write $n=q^cT$ with $c\ge1$ and $q\nmid T$. Then $T<P$. Let $M$ be the largest prime-power divisor of $T$, with $M=1$ if $T=1$. Minimality of $P$ implies $M\le p$. Choose $K=M$. For $k<p$, $\gcd(k,q)=1$, so $d(n,k)\mid T$. If $k=p\le M$, then $M=p$ divides $T$, and $d(n,p)\mid p\mid T$. Conversely every prime power dividing $T$ is at most $M$, is not divisible by $q$, and is saturated as a denominator; therefore $T\mid L$. Hence $L=T$ and the logarithmic formula holds. This proves both the first failure and the success of every smaller positive input, without asserting the unresolved general feasibility classification.

### What the settlement shows

The decisive mechanism is saturation at prime-power indices together with the gcd denominator bound. The lcm identity is uniform over all intermediate admissible sets; no optimization over such sets is needed. This proves the interpretation of Conjecture 1 in Remark 5. Remark 4's denominator redundancy also follows in prose: the $r$-part $r^j$ of any permitted denominator divides $n$, is prime to $p$ and is at most its index $k\le n$; the lower set already contains the saturated denominator $r^j$. Additional upper-set elements cannot enlarge the lcm. This conclusion concerns denominator contributions, not equality of the rational values.

The prime-power saturation theorem extends to every positive $n$ and every divisor $r^j$, with no admissibility hypothesis. Composite bases obey different coprimality and exclusion rules, as distinguished above. The source paper's independently proved results retain their statements; Conjecture 1 and its lcm reformulation can now be used under exactly the displayed hypotheses. No additional formal theorem about the source's other results or the neighbouring sequences is asserted.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`. The bounded experiment does not settle the uniform DC-3 formula, full composite feasibility criterion or sequence identifications. C2 and A345531 have prose arguments here; this delivery's only formal settlement claim is Conjecture 1. Four-slot escape registration remains unfinished under issue #21956.
