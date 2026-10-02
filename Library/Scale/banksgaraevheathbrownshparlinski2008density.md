---
bibkey: banksgaraevheathbrownshparlinski2008density
authors: W. D. Banks, M. Z. Garaev, D. R. Heath-Brown, and I. E. Shparlinski
year: 2008
title: Density of non-residues in Burgess-type intervals and applications
doi: 10.1112/blms/bdm111
url: https://arxiv.org/pdf/math/0607692v3
claim: The proof of Theorem 2.1 gives fixed reciprocal-prime weight at a Burgess-type cutoff for prime moduli; odd affine offsets retain the prime-two contribution, while actual square-part and multiplier exceptions still require their own budget.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime-conductor weights with the low-end exceptions retained

The article appeared in *Bulletin of the London Mathematical Society*
40 (2008), 88–96, [DOI:10.1112/blms/bdm111](https://doi.org/10.1112/blms/bdm111).
The inspected source is [arXiv:math/0607692v3](https://arxiv.org/abs/math/0607692v3),
dated 25 September 2007. The following bound is an explicit intermediate
conclusion in §3.1, printed pp.4–5, in the proof of Theorem 2.1; the main
theorem concerns the density of integer nonresidues. No independent full
proof audit or numerical threshold is claimed here. The local mod-eight
implication below was checked by a transient Lean application of existing
integer facts; the analytic estimate and Robin application were not
compiled. No new Lean declaration is delivered.

## The weighted statement actually available

For every fixed $0<\varepsilon\le0.01$ and every sufficiently large
**prime** $P$, the proof states

$$
\sum_{\substack{\ell\le R(P)\\(\ell/P)=-1}}\frac1\ell\ge\varepsilon,
\qquad R(P)=P^{1/(4\sqrt e)+\varepsilon/2},
$$

where $\ell$ ranges over primes, including two. The threshold depends
only on $\varepsilon$, not a chosen subsequence of $P$. There is no
growing lower cutoff in this statement. It applies to the Legendre
character of prime modulus; inducing that character to a composite modulus
does not make this a theorem for all composite quadratic characters.

## Actual-source application and its limits

Use the [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§§181,202 and the [same-integer Euler budget](bourgainlindenstrauss2003entropy.md).
Let the primitive quadratic character associated with the actual nonsquare
$D$ have **odd prime conductor $P$**. It is then the Legendre character
$\chi_P(\ell)=(\ell/P)$. On odd primes not dividing $D$, this agrees with
the actual symbol $(D/\ell)$. A positive example is $D=Pt^2$ with
$P\equiv1\pmod4$. Positive $D=P\equiv3\pmod4$ instead has conductor
$4P$ and does not meet this prime-conductor hypothesis.

For §202's actual affine $n=h+gU$ and $Y=\log n$, require $R(P)\le Y$.
Every odd supplied prime not dividing $D$ is excluded from $n$. Set

$$
E_D(P)=\sum_{\substack{\ell\le R(P)\\\chi_P(\ell)=-1\\\ell\mid2D}}\frac1\ell.
$$

Then the conservative paper-level interface is
$J_{\rm miss}(n;Y)\ge\varepsilon-E_D(P)$.
Square-part primes absent from the primitive conductor remain in this
cost. For §181's primitive multiplicative source $n=Cu$, every odd
negative-character prime is excluded from $u$, including primes in the
square part: an odd prime dividing $D$ cannot divide the primitive $u$.
Its corresponding cost is the same sum with $\ell\mid2C$, rather than
an independently charged ramification factor.

The upper cutoff can meet $Y$ when
$P\le(\log n)^{4\sqrt e-\delta}$ for fixed $0<\delta<4\sqrt e$, after
choosing fixed $\varepsilon>0$ small enough that
$(4\sqrt e-\delta)(1/(4\sqrt e)+\varepsilon/2)<1$.
This is a **cutoff range**, not an automatic Robin-safe family: the
exception-adjusted weight must still pay
$M(Y)+T(Y)-D_{\rm pow}(n)$ for that same $n$.

In particular, if $\chi_P(2)=-1$, deleting two already costs $1/2$, larger
than the guaranteed $\varepsilon$. A fixed exceptional set does not lose
its reciprocal weight merely because $P\to\infty$. Proving that an
exceptional prime actually misses $n$ can restore its contribution, but
that is an additional arithmetic certificate.

## Odd affine offsets certify the prime-two contribution

For the same actual affine source, assume additionally that $h$ is odd.
Then $D$ is odd and $D\equiv1\pmod4$. If $n$ is even,
$8\mid n(n-2h)$: writing $n=2k$, the product is $4k(k-h)$, and one of
$k,k-h$ is even. The existing identity gives $(gc)^2\equiv D\pmod8$.
Since $D$ is odd, $gc$ is odd, so its square is one modulo eight. Hence

$$
2\mid n\quad\Longrightarrow\quad D\equiv1\pmod8.
$$

This is a local application of the existing identity and ordinary parity
and odd-square facts, not a new character estimate. The standard
supplementary law at two implies that a negative quadratic character value
at two forces $2\nmid n$ here. This concerns the **primitive** character;
the character induced to $4|D|$ in §202 still has value zero at two.

With odd prime conductor $P$, write $D=dt^2$ with $t\ge1$ odd and

$$
d=\begin{cases}P,&P\equiv1\pmod4,\\-P,&P\equiv3\pmod4.\end{cases}
$$

The odd square $t^2$ preserves the mod-eight class. Thus
$\chi_P(2)=(D/2)$, and a supplied negative prime two is actually missing
from $n$. Every odd supplied prime not dividing $t$ is also missing by
§202. The only possible absorbed negative primes belong to the same
integer's square-part intersection. Define

$$
E_{\rm sq}(P;n,t)=
\sum_{\substack{\ell\le R(P)\\\chi_P(\ell)=-1\\
\ell\mid\gcd(t,n)}}\frac1\ell.
$$

Under the original Banks threshold and $R(P)\le Y=\log n$, the refined
paper-level interface is

$$
J_{\rm miss}(n;Y)\ge\varepsilon-E_{\rm sq}(P;n,t).
$$

In particular $\gcd(t,n)=1$ retains the entire guaranteed weight, without
requiring $t=1$. When the **actual signed $D=\pm P$**, the square part is
one and the cost vanishes. Along such actual sources with odd $h$,
$n\to\infty$, $P\to\infty$ and
$P\le(\log n)^{4\sqrt e-\delta}$ for a fixed
$0<\delta<4\sqrt e$, choose fixed $0<\varepsilon\le0.01$ satisfying
the cutoff condition above. The existing Euler budget then gives the
paper-level consequence

$$
\limsup\frac{Z(n)}{e^\gamma\log\log n}\le e^{-\varepsilon}<1.
$$

This is a conditional source-family application, including negative signed
$D=-P$ with $P\equiv3\pmod4$. It neither proves that all candidates meet
the hypotheses nor proves that such growing-prime canonical families
exist. Banks supplies no numerical onset threshold here.

The square-part condition has a real canonical obstruction. The legal
unit-bit-one representation

$$
n=6921=6765+144+8+3+1
$$

has composition $(a,b)=(1009,1634)$, $g=h=1$, and
$Q=-3169$, $D=12681=1409\cdot3^2$. The prime conductor is $1409$,
$\chi_{1409}(3)=-1$, and $3\mid n$. Thus negative primitive-character
primes in the original square part cannot all be declared missing, even
on this canonical slice. Removing oddness of $h$ also fails in the general
affine model: $h=0$, $g=1$, $(a,b)=(3,2)$ give $n=12$ and
$D=-44=-11\cdot2^2$, but $\chi_{11}(2)=-1$ and $2\mid n$.

The [Bourgain–Lindenstrauss window](bourgainlindenstrauss2003entropy.md)
has a different advantage: its lower cutoff eventually exceeds two and
its original $D$ retains square-part zeros. The
[Pollack input](pollack2017nonresidues.md) covers arbitrary nonprincipal
characters. Its Theorem 1.1 states a prime count; the linked note also
records a weighted induced-character consequence of its published inputs,
with the enlarged modulus and its zeros retained. Reuse these distinct existing statements according to their actual
hypotheses; none of these interfaces settles all Robin candidates or RH.
