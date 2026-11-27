---
slug: a369255-dirichlet
bibkey: karttunen2024a369255
doi: null
url: https://oeis.org/A369255/internal
triage: theorem
motivation_gids:
  - D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.result
---

# The two A369255 Dirichlet convolutions

## Problem

The unnumbered OEIS A369255 formulas attributed to Sequence Machine assert
that, for every positive integer $n$,
$$
H(n)\bmod 2
=\sum_{d\mid n}A(d)B(n/d)
=\sum_{d\mid n}H(d)C(n/d).
$$

### Statement echo

| Source | Lean |
| --- | --- |
| A369255 offset 1 | Natural index $n$ with $1\le n$, including $1$ |
| A000035 applied to A140773 | The natural remainder of $H(n)$ modulo two, cast to the integers |
| A038548 and its inverse Möbius transform A140773 | $g(n)$ counts positive divisors $d$ satisfying $d^2\le n$, and $H(n)=\sum_{d\mid n}g(d)$ |
| A007875 | $A(n)$ counts positive factor pairs $rs=n$ with $r\le s$ and $\gcd(r,s)=1$ |
| A219009 | $B(n)$ sums $\mu(n/d^4)$ over positive $d$ with $d^4\mid n$ |
| A355837 | $C$ multiplies the coefficients $2(e\bmod2)(-1)^{\lfloor(e+1)/2\rfloor}$ over the prime powers of $n$. The empty product gives $C(1)=1$ |
| Both FORMULA equalities | Two integer divisor sums, conjoined in the proposition proved by the settling declaration |

## Motivation

The two formulas give exact integer values for the same parity sequence by
different convolutions. The preregistered question and source wording are
recorded in [#21450](https://github.com/the-omega-institute/trureturing/issues/21450).

## Gap

The OEIS formula block records finite agreement for the first $2^{20}$
indices. Its assertion quantifies over all positive indices.

## Route

The module works with Dirichlet convolution on integer-valued arithmetic
functions. Counting coprime factors by assignments of prime-power blocks
gives the first doubled convolution. Counting divisor pairs, including the
square diagonal, and using the prime-power coefficients of $C$ gives the
second. Both reduce to the convolution of the fourth-power indicator with
the sum of the squarefree indicator and the Möbius function. The unsigned
and signed residue products bound the resulting values to zero and two.
The proof identifies the source divisor sum for $H$ with the existing
ceiling expression in the A252505 module.

## Falsifier

A positive index where either integer sum differs from $H(n)\bmod2$ would
refute the conjunction. The source domain includes $n=1$ and permits every
prime support and exponent pattern.

## Evidence

The single settling declaration is
D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.result.
The module has generality I and no computational utility designation.
The four-slot escape audit is unfinished. [#21636](https://github.com/the-omega-institute/trureturing/issues/21636)

The exact-arithmetic script at
[experiments revision 2f7b7b577008f2134fe09c09a58e3c77c0e239ff](https://github.com/the-omega-institute/trureturing-experiments/tree/2f7b7b577008f2134fe09c09a58e3c77c0e239ff/docs/reports/a369255-dirichlet)
is run with `python3 docs/reports/a369255-dirichlet/check.py` from that revision.
Exit 0. Script SHA-256
`35c17794e7ec2cfa059af615fcf2d549777ea469352a113a4a0c6426195da831`.

## Triage

### What the settlement shows

- **Proved, kernel-checked by `result`**. Both original identities hold for all positive $n$. Their common integer value is zero or one, as is the parity remainder on their left-hand side.
- **Proved, kernel-checked by the private `convolution_C_mod_two`**. For any integer-valued $f$ and $n>0$, convolution by the literal $C$ preserves $f(n)$ modulo two. In the divisor sum, the term for $d=n$ has coefficient $C(1)=1$, and every remaining coefficient is even.
- **Computed, pinned experiment**. The support criterion is that every prime exponent is $0$ or $1$ modulo $4$ and the number congruent to $1$ is even. It agrees with the checker for $1\le n\le1{,}048{,}576$ and for all 74,613 exponent multisets with zero to six positive exponents, each at most 16. The uniform criterion has no separate Lean declaration in this module.
- **Computed, pinned experiment**. $a(2)=a(3)=0$ and $a(6)=1$, giving a failure of multiplicativity at the coprime indices $2$ and $3$.
- **Open in this settlement**. The nearby inverse-sequence questions for A378214 and A378215 have no settlement here. The two new universal equalities establish the finite agreement quoted by A369255 as a special case.

## ASSUMED-UNVERIFIED

The literature screen in the preregistration found classical convolution
ingredients and source divisor-count formulas, with no complete settlement
in the searched material. Citing-work completeness is ASSUMED-UNVERIFIED.
OpenAlex and Semantic Scholar returned HTTP 429, and the Sequence Machine
page provided no readable formula text to the preregistration screen.
