---
bibkey: banks2007nicolasrobin
authors: William D. Banks; Derrick N. Hart; Pieter Moree; C. Wesley Nevans
year: 2007
title: The Nicolas and Robin inequalities with sums of two squares
doi: null
url: https://arxiv.org/abs/0710.2424v1
claim: A fixed positive-density restriction excluding exponent-one primes yields eventual Nicolas and Robin inequalities; the sum-of-two-squares Robin exceptions are bounded by 720.
strata_touched: []
license: citation-only
triage: anchor
---

# The Nicolas and Robin inequalities with sums of two squares

The [versioned author text](https://arxiv.org/html/0710.2424v1),
§1, equations (4)–(6) and Theorem 1, fixes a prime set
$\mathcal P$ satisfying

$$
0<\liminf_{x\to\infty}\frac{\pi_{\mathcal P}(x)}{\pi(x)}
\le\limsup_{x\to\infty}\frac{\pi_{\mathcal P}(x)}{\pi(x)}<1.
$$

Write $\mathcal Q$ for its complement and set

$$
\mathcal S(\mathcal P)=
\{n\ge1:\ p\in\mathcal Q, p\mid n\Longrightarrow p^2\mid n\}.
$$

Theorem 1 states that all but finitely many members satisfy

$$
\frac n{\varphi(n)}<e^\gamma\log\log n.
$$

Here $\varphi(n)$ is Euler's totient. The authors call this upper
inequality the Nicolas inequality; its direction differs from the
primorial Nicolas criterion recalled earlier in their introduction.
Their §1 also records $\sigma(n)/n<n/\varphi(n)$ for $n>1$, so these
same members satisfy Robin. This consumes the published theorem,
without reconstructing its density or minimization proof.

Corollary 2 gives a useful necessary profile: for every fixed reduced
residue class $a\pmod m$, all sufficiently large failures of their
Nicolas upper inequality have a prime $p\equiv a\pmod m$ with
$p\mid n$ and $p^2\nmid n$. The same implication applies to Robin
failures, by the preceding strict comparison. The exceptional threshold
depends on the fixed class; the corollary supplies no uniform threshold
when $m$ or the class varies with $n$.

## The four-phase norm is an already solved scalar class

The Robin application immediately following Theorem 2 in §1 gives

$$
n=a^2+b^2>720\Longrightarrow
\frac{\sigma(n)}n<e^\gamma\log\log n.
$$

The article determines the complete exceptional values in this class.
The [classical two-squares characterization](../Arith/grosswald1985representations.md)
explains its prime-exponent restriction. Thus the four-phase invariant
$E(a,b)=a^2+b^2$ of $C(a,b)=(-b,a)$ can use this bound directly;
neither exception enumeration nor a new proof of that bound is needed.

## The same theorem applies to golden norm magnitudes

For the golden integer $x=a+b\theta$, where $\theta^2=\theta+1$, write

$$
Q(a,b)=a^2+ab-b^2,\qquad n=|Q(a,b)|>0.
$$

Use the fixed set

$$
\mathcal P_5=\{5\}\cup\{p\text{ prime}:p\equiv1,4\pmod5\}.
$$

The prime number theorem in these fixed progressions gives density
$1/2$. Every complementary prime $p\equiv2,3\pmod5$ is inert in
$\mathbb Z[\theta]$. The classical inert-prime norm law gives
$p\mid n\Longrightarrow p^2\mid n$; this includes $p=2$.
The repository's golden carrier, conjugation, multiplicative norm and
`GoldenPrimeSplitting.golden_prime_of_mod_five_eq_two_or_three`
locate the algebraic inputs. Theorem 1 therefore applies to the same
actual norm magnitude $n$ with $\mathcal P=\mathcal P_5$.

Consequently all sufficiently large nonzero golden norm magnitudes
satisfy the strict Nicolas upper inequality and Robin. The threshold
is uniform over their representations because $\mathcal P_5$ is fixed;
no numerical threshold or full golden-norm exception list is supplied
here. This is a classical-source application, without a new Lean
declaration, Lean verification or originality claim.

## The norm readout does not replace the actual Robin integer

The FIB quantity is $q(a,b)=2a+3b$, with a separately retained unit bit
when required. It is different from both $E(a,b)$ and $|Q(a,b)|$.
To apply either norm-class bound to an actual Robin integer $N$, one
must certify that **$N$ itself** belongs to that class; the norm of its
FIB composition alone does not supply such a certificate.

The [already covered FIB norm branches](fibcomplement2026weightedresidues.md#support-conditioned-discriminants-and-already-covered-norm-branches)
bound quantities $gq(a,b)$ under their stated source conditions.
They are distinct from this bound on $|Q(a,b)|$, and this note does
not extend those quantity families. Basic Fib recursion preserves
$|Q|$, so increasing the recursion depth need not increase the norm
magnitude or cross its threshold. Finitely many exceptional norm
values can correspond to infinitely many compositions.

The [actual CA right-tail source obligation](../Arith/caveney2012sacaga.md#inherited-oscillation-relaxes-the-eventual-signed-target)
still needs its directed signed estimate at the original source clock.
No such estimate, covering certificate for that source family, or
proof of RH follows from these norm-class bounds.
