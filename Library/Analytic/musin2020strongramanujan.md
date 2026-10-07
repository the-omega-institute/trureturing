---
bibkey: musin2020strongramanujan
authors: Oleg R. Musin
year: 2020
title: Ramanujan's theorem and highest abundant numbers
doi: null
url: https://arxiv.org/abs/1905.09327v4
claim: The preprint extends the RH-conditional Ramanujan lower margin to all integers and shows that global highest-abundant contacts at the square-root logarithmic weight cannot exist if RH is false; finite hull contacts do not supply an unconditional Robin anchor.
strata_touched: []
license: citation-only
triage: anchor
---

# Ramanujan margins and attained highest-abundant contacts

The inspected primary is [arXiv:1905.09327v4](https://arxiv.org/pdf/1905.09327v4),
dated 10 February 2020, 12 pages. Theorem 1 and its proof on pp.3–5,
Corollary 1 on p.6, the contact definition on pp.3–4, and Theorems 2–4
with their supporting arguments on pp.9–11 were read. The PDF SHA-256 is
`eb858cbc77661c93203463fda00faae6ff30c70974e29a6fde0741587c6f42dd`.
This is a
primary-source applicability check, without a whole-paper proof audit,
publisher-version certification, numerical rerun, or Lean verification.
The source's results are reused, not claimed as new FIB mathematics.

## The positive margin already assumes RH

Write $E=e^\gamma$, $G(n)=\sigma(n)/(n\log\log n)$ and

$$
T(n)=\left(E\log\log n-\frac{\sigma(n)}n\right)\sqrt{\log n}.
$$

Theorem 1 gives, **assuming RH**,

$$
\liminf_{n\to\infty}T(n)\ge c_1,
\qquad c_1=E(2\sqrt2-4-\gamma+\log(4\pi))>1.393.
$$

This is an all-integer statement. Its proof uses Robin's comparison
between consecutive CA endpoints to extend the cited Ramanujan
CA margin, and pays the endpoint ratio tending to one. Corollary 1
retains an existential starting threshold for each $\varepsilon>0$:
$T(n)>c_1-\varepsilon$ eventually. These are conditional suppliers;
neither that extension nor its constant is an unconditional lower bound
for the selected Robin-critical source.

## The domain and attained support are part of the definition

For $D=\{n\in\mathbb N:n\ge5040\}$ and real $s$, set

$$
R_s(n)=(En\log\log n-\sigma(n))(\log n)^s.
$$

An integer $m$ belongs to $\mathrm{HA}_s(D)$ exactly when some real slope
$a$ makes $R_s(m)-am$ an **attained global minimum over all of $D$**.
The abscissa here is $n$, not $\log n$, and 5040 remains in the domain.
These are not the CA supporting objectives, nor the normalized global
maximizers of $G$ used in the
[Caveney–Nicolas–Sondow reduction](../Arith/caveney2012sacaga.md).

Theorem 2 states that for $s>1/2$ the set is infinite if RH is true and
empty if RH is false. For $s\le0$ it is $\{5040\}$ if RH is true and
infinite with negative slopes tending to zero if RH is false.
Changing the weight therefore changes which existence statement can be
used; the phrase "highest abundant" alone does not specify a source.

Theorem 3(b), p.10, covers the borderline needed here. For positive
$\tau(n)$ with

$$
\Phi_\tau=\lim_{n\to\infty}\frac{\tau(n)}{\sqrt{\log n}}>0,
$$

RH false implies that the contacts for
$R_\tau(n)=(En\log\log n-\sigma(n))\tau(n)$ are empty. Substituting
$\tau(n)=\sqrt{\log n}$ gives $\Phi_\tau=1$ and
$\mathrm{HA}_{1/2}(D)=\varnothing$ under that hypothesis.
The proof consumes Robin's infinitely many negative excursions; it is
not a theorem excluding those excursions unconditionally.

## Application at the retained Robin source

At the [selected critical integer](polak2026finiterobinca.md), retain
$A=\log N$ and $\Delta(N)=\gamma+\log\log A-\log(\sigma(N)/N)$.
Direct substitution gives the paper-level readout

$$
\frac{R_{1/2}(N)}N=T(N)
=E\sqrt A\log A\,[1-e^{-\Delta(N)}],
\qquad \Delta(N)=I_\psi(A)+D^*(A).
$$

The second identity has the same cited critical-source premises as its
existing supplier. No approximation to $1-e^{-\Delta}$ is used. This
readout retains the sign of the actual margin but supplies no bound for
it. In particular, under the counterexample hypothesis the selected
global maximizer exists, whereas Theorem 3(b) makes the entire
$\mathrm{HA}_{1/2}(D)$ empty. It cannot be identified with an attained
contact of that new objective.

A finite hull always has supported minima; this does not certify a
global contact after the omitted tail is restored. Establishing even
one genuine contact at this weight would, by the cited theorem, exclude
RH false. It cannot be assumed as a preliminary compactness or geometric
step in an RH proof. The
[higher-order CA construction](musin2026higherorder.md) uses different
coordinates and a different common domain; its separate attainment and
criterion-preservation hypotheses remain necessary.

An exact FIB address can preserve the integer $N$ when its original
quantity observer is retained. It does not prove attainment of this
all-integer minimum or bound its tail. This source rules out the proposed
unconditional contact-selection shortcut, not additional arithmetic
estimates at the original critical source. The signed condition
$\sqrt A\log A\,I_\psi(A)\ge-D_{\rm lb}(A)$ remains unproved.
