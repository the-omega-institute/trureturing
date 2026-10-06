---
bibkey: alladi1982roughmobius
authors: Krishnaswami Alladi
year: 1982
title: Asymptotic estimates of sums involving the Moebius function
doi: 10.1016/0022-314X(82)90060-9
url: https://doi.org/10.1016/0022-314X(82)90060-9
claim: The fixed-u asymptotic for the signed Möbius sum over rough integers is recorded in Alladi–Goswami 2412.03088v1 §1.1; the original compact-u uniform range and the growing-prime-filter kernel estimates are not verified here.
strata_touched: []
license: citation-only
triage: anchor
---

# Signed Möbius sums over rough integers

Alladi's paper appeared in *Journal of Number Theory* **14** (1982),
86–98, DOI [10.1016/0022-314X(82)90060-9](https://doi.org/10.1016/0022-314X(82)90060-9).
The checked statement is its explicit account in Krishnaswami Alladi and
Ankush Goswami, *Parity results concerning the generalized divisor function
involving small prime factors of integers*,
[arXiv:2412.03088v1, §1.1](https://arxiv.org/html/2412.03088v1#S1.SS1).
The original 1982 theorem and proof have not been directly inspected.
No source text is vendored and no Lean verification is supplied.

Write $P^-(n)$ for the least prime factor and set $P^-(1)=\infty$.
The source defines

$$
M_{\mathrm{rough}}(z,y)
=\sum_{\substack{1\le n\le z\\P^-(n)>y}}\mu(n).
$$

For each fixed $u=\log z/\log y>1$, §1.1 records, as $y\to\infty$,

$$
M_{\mathrm{rough}}(z,y)
=\frac{z\rho'(u)}{\log y}
+O_u\!\left(\frac{z}{(\log y)^2}\right),
$$

where $\rho$ is the Dickman function. This is a literature-attested input,
not a new asymptotic estimate. It uses the actual Möbius weight, includes
the unit, and uses a strict least-prime-factor cutoff. The unweighted
Buchstab count and Liouville weights are different objects.

The same subsection reports that Alladi established uniform estimates
over longer ranges, but does not give their precise hypotheses and errors.
This note therefore does not certify a bound uniform on
$u\in[1+\delta,U]$, for fixed $\delta>0,U>1+\delta$, or on a growing range.
Pointwise fixed-$u$ asymptotics do not supply those assertions.

## Correspondence with a growing FIB prime section

For $Q(y)=\prod_{p\le y}p$, the coprime prefix of
[the FIB volume, §426](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
is exactly $M_{Q(y)}(z)=M_{\mathrm{rough}}(z,y)$.
Its fixed filter $P=210$ and the growing filter $Q(y)$ have different
uniformity obligations. The constants in §426.7 and §426.15 have not been
bounded uniformly for growing $Q(y)$.

At a source clock $A$, choosing $y=A^{1/u_0}$ with fixed $u_0>1$ and
$n\sim cA$ with fixed $c>0$ gives $\log n/\log y\to u_0$. This moving-$u$ sequence is not
certified by the fixed-$u$ statement alone. Moreover, one filter must be
shared by all rows of the complete pairing: choosing $y=n^{1/u_0}$
separately for each row does not invoke §426's same-filter identity.

A usable signed estimate still needs simultaneous control of the actual
rough prefix and its paired kernel at the same growing filter, the complete
original head compensation, the complementary range, and the selected
critical sources. The classical prefix formula alone does not give a sign
for the full Robin integral or prove RH. The distinct subpower range in the
[Alamoudi source](alamoudi2026subradicallysifted.md) is not substituted for
the fixed positive power cutoff here.

## The source-scale boundary $u\to1^+$

The fixed-$u$ estimate above cannot retain an
$O(z/\log^2 y)$ error with one bounded constant when $z/y\to c>1$.
For all real $y\ge2$ and $y\le z\le y^2$, exact prime counting gives

$$
M_{\mathrm{rough}}(z,y)=1-\pi(z)+\pi(y).
$$

Indeed, a composite integer whose prime factors are all strictly greater
than $y$ exceeds $y^2$. The allowed integers in this range are therefore
the unit and the primes in $(y,z]$; their Möbius weights are $1$ and $-1$.
For $z/y\to c>1$, the classical prime number theorem yields

$$
M_{\mathrm{rough}}(z,y)
=-(c-1)\frac y{\log y}+o\!\left(\frac y{\log y}\right).
$$

Here $u=\log z/\log y\to1^+$ and eventually $1<u<2$. In that interval
$\rho'(u)=-1/u$, so

$$
\frac{\log y}{y}
\left[M_{\mathrm{rough}}(z,y)-\frac{z\rho'(u)}{\log y}\right]
\longrightarrow1.
$$

Thus this moving-boundary error is of order $y/\log y$, rather than
$z/\log^2 y$. This does not contradict the fixed-$u$ statement or settle
uniformity on any interval bounded away from $u=1$. It is an elementary
scope check using exact prime counting and the classical PNT, not a new
rough-sum theorem or a claim about Alladi's uninspected uniform estimates.

For an actual proper GA1 CA source, retain $A=\log N$ and
$y=P(N)$ as distinct quantities. The [published GA1 envelope](../Arith/caveney2012sacaga.md),
Theorem 13, gives $y\sim A$ as such sources tend to infinity. Initial CA
prime support gives $\operatorname{rad}(N)=Q(y)$. Hence source-scale rows
$z=cA$, for fixed $c>1$, have exactly this moving-boundary behavior with
the same filter $Q(y)$, including the unit. This source class contains the
conditional critical maximizer selected by the extraordinary-number
reduction; no unbounded critical sequence is assumed. The asymptotic
statement supplies no effective cutoff, growing-filter kernel estimate,
complete compensated remainder bound, or Robin/RH conclusion.
