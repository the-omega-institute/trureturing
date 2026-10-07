---
bibkey: fordmaynardtao2015primechains
authors: Kevin Ford, James Maynard, Terence Tao
year: 2015
title: Chains of large gaps between primes
doi: null
url: https://arxiv.org/abs/1511.04468v1
claim: The primary proof supplies a positive proportion of widely spaced prime rows; its quantitative abundance supports deletion of sparse higher-layer CA events, but supplies no root-conditioned prefix balance.
strata_touched: []
license: citation-only
triage: anchor
---

# Many prime rows and the actual CA isolation interface

The inspected primary is [arXiv:1511.04468v1](https://arxiv.org/abs/1511.04468v1),
13 November 2015, by Ford, Maynard and Tao. Its
[16-page PDF](https://arxiv.org/pdf/1511.04468v1) has 200,200 bytes and SHA-256
`4c5709180f4b427eac3525411618534a6d5ab03c1a79d3faeee3318d2ad7ecce`.
Locators refer to this version and its printed pages. This note cites the
primary rather than redistributing it; it does not assert that this version
is the latest literature on prime gaps.

## Reuse the abundance retained in the proof

Theorem 1, p. 2, gives chains of any fixed number of consecutive large prime
gaps. For removing a second sparse family, the relevant input is stronger
than the existence of one such chain: use Theorem 2, pp. 5–6, Lemma 3.1,
pp. 6–7, and the proof of Theorem 1 on p. 7, equation (3.10) and its
following close-pair estimate.

Fix the source's sieve parameter sufficiently large that its good rows
contain at least three primes. Its equation (3.10) has probability bounded
below by a positive constant independent of the small separation parameter.
The subsequent probability of a close pair is $O(A^2\varepsilon)$; choose
$\varepsilon$ so this error is smaller than that lower bound. Thus the
source proof directly supplies fixed $c_0,\varepsilon,c>0$ and arbitrarily
large $x$ with at least $c_0Z$ good rows

$$
I_z=zP+m+(x,y],\qquad 1\le z\le Z,
\qquad
y=c\frac{x\log x\log_3x}{\log_2x},
$$

each containing at least three primes whose pairwise distances exceed
$\varepsilon y$. Here $P$ is the product of primes up to $x$ after removal
of the source's possible exceptional prime, and $m\in[1,P]$ is its CRT
shift. Choose a fixed integer $D>1$ at least as large as the constant in
Lemma 3.1 and put $Z=P^D$; that lemma holds for every $Z$ beyond its lower
threshold. Constants may depend on this fixed $D$.

Keeping the positive proportion is an application of the published proof,
not a new large-gap or sieve theorem. The source also gives
$\log P\asymp x$, $y=o(P)$, and $y/x\to\infty$.

## The additional project correspondence

Use the actual unrestricted CA price $g(t)=1/(t\log t)$ and events
$g(\eta_{p,j})=F(p,j)$, with

$$
F(p,j)=\frac{\log(1+1/(p+\cdots+p^j))}{\log p}.
$$

The [project's §420](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
combines the supplied many-row result with two elementary consequences
of this exact activation equation:

$$
p<\eta_{p,1}<p+1,
\qquad
\#\{(q,j):j\ge2,\ \eta_{q,j}\le T\}
=O\!\left(T^{1/2}(\log T)^{3/2}\right).
$$

The enlarged rows $J_z=[zP+m+x-1,zP+m+y+2]$ are disjoint and lie below
$T\asymp P^{D+1}$. Deleting every row containing a higher-layer event
costs $o(Z)$ rows because $D>1$. An interior prime in any remaining good
row then supplies an actual untied first-layer event with no other layer
within $K\log p$, for any prescribed fixed $K>0$, once $x$ is sufficiently
large. All layer counts retain multiplicities, including ties.

This CA correspondence is a source-derived paper application. The source
does not discuss CA activations, regular returns, their signed moments or
Robin's inequality; no Lean verification or literature novelty claim is
made for this additional interface.

## What isolation leaves unpaid

Isolation does not locate a self-matching return. For the same untied event,
write $\eta_p=p+\delta_p$ and retain the exact earlier higher-layer prefix

$$
B_{\ge2}(p)=\sum_{\substack{q\ \text{prime},\ j\ge2\\F(q,j)>F(p,1)}}\log q.
$$

Its post-event surplus is
$s_p=\vartheta(p)-p+B_{\ge2}(p)-\delta_p$.
The sufficient singleton family in §420 additionally requires, at the
same isolated primes,

$$
\frac34\log p\le s_p\le\frac78\log p.
$$

The many-row estimate supplies no such logarithmic-width prefix-placement
count. Even a positive and then negative surplus in one clean row can skip
this entire strip: between consecutive row primes $p<q$,
$s_q-s_p=\log q-(\eta_q-\eta_p)$, with the second term much larger than
$\log q$. Separate oscillation and large-gap results therefore do not
establish this joint assertion.

The [existing packet source](mantovanelli2026primeworkload.md) remains the
authority for the singleton criterion and packet-margin direction. Even
an unbounded winning singleton family would leave the selection obligation
at potentially nonpositive minima and the full Robin/RH sign unresolved.
