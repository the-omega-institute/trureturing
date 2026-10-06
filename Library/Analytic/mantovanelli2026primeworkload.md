---
bibkey: mantovanelli2026primeworkload
authors: Marco Mantovanelli
year: 2026
title: Colossally Abundant Numbers, Robin's Inequality, and an Exact Prime-Layer Workload
doi: null
url: https://zenodo.org/records/22014299
claim: The archived manuscript supplies the exact regular-return packet identity, a sharp two-moment lower bound, and a cone-envelope reduction for the actual unrestricted CA pressure; none decides the unresolved Robin sign.
strata_touched: []
license: citation-only
triage: anchor
---

# Actual CA packets and their existing moment bound

The primary used here is `paper/colossally_abundant_prime_layer_workload.tex`
in the author's [Zenodo record 22014299](https://zenodo.org/records/22014299),
version 1.0.0, published 19 August 2026. The
[88,822-byte archive](https://zenodo.org/records/22014299/files/colossally_abundant_prime_layer_workload_zenodo_22014299.zip?download=1)
has MD5 `b89a5bb3bf71aec8c4cd5b807aa0097f`, matching the record metadata.
The manuscript SHA-256 is
`8208445c84c6cafc971a6f2a0637b06715a783f680de80d2ed3bb4a3be503d65`,
matching its archive manifest. These identify the inspected source; the
archive's computational certificates are not premises here and were not rerun.

The record DOI, [10.5281/zenodo.22014299](https://doi.org/10.5281/zenodo.22014299),
identifies the computational companion, not a journal publication of the paper.
The manuscript is separately licensed CC BY 4.0; this note cites it rather
than redistributing the manuscript or code. The ResearchGate page reports
an “Improved Version 2” with preprint DOI 10.13140/RG.2.2.24429.76002;
correspondence of that version with this archived manuscript is not established.
All locators below refer to the inspected LaTeX source, not to assumed PDF
pagination, peer review, or Lean verification.

## Parameters and the actual packet

Source §2.1 defines $G(n)=[\sigma(n)/n]/\log\log n$ for $n>e$. Definition 3.3 and Appendix A
require regular returns to be event-free and to satisfy
$\Phi_{\rm CA}(a)=a$. The global prefix includes every tied layer.
For the [project's existing pressure](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
§§98 and 111, the exact parameter map is

$$
\eta_{p,j}=\tau_{p,j},\qquad
\Phi_{\rm CA}=A^+,\qquad
D_{\rm CA}(x)=x-A^+(x),\qquad
\widehat{\mathcal F}(x)=-\mathfrak D(x).
$$

Here $g(x)=1/(x\log x)$ is the same unrestricted price. On event-free
regular endpoints $a<b$, both endpoint conventions agree, the open packet
has total mass $L=b-a$, and every simultaneous layer keeps weight $\log p$.
Theorem 5.2 (`thm:packet-identity`) and §7 give the finite probability law

$$
\mu_{a,b}=\frac1L\sum_{a<\eta_{p,j}<b}(\log p)\delta_{\eta_{p,j}},
\qquad
\log\frac{G(C_b)}{G(C_a)}
=L\left(\int g\,d\mu_{a,b}-\overline g(a,b)\right),
$$

where $\overline g(a,b)=(\log\log b-\log\log a)/L$.
Proposition 7.6 (`prop:moment-workload`) already supplies the complete
moment–workload duality. These identities and their endpoint bookkeeping
are reused, not delivered as new project mathematics.

## The sharp two-moment statement is directly reusable

Theorem 7.7 (`thm:sharp-two-moment`), §7.4, applies to any probability
measure on $[a,b]\subset(1,\infty)$ with mean $m<b$ and variance $V$.
With $r=m-V/(b-m)$ and $\alpha=(b-m)/(b-r)$ it gives

$$
\int g\,d\mu\ge H_g:=\alpha g(r)+(1-\alpha)g(b).
$$

The source proves $a\le r\le m$ using the bounded-support variance
inequality and identifies the extremizer
$\alpha\delta_r+(1-\alpha)\delta_b$ by quadratic Hermite interpolation.
Its Remark 7.8 states that support, mean and variance alone cannot improve
this lower bound. No new generic moment or quadrature theorem is asserted.

On the same actual packet this means

$$
\mathfrak D(b)-\mathfrak D(a)
\le L\bigl(\overline g(a,b)-H_g\bigr).
$$

Thus $H_g>\overline g$ certifies a decrease of the full pressure margin;
it does not certify positivity of either endpoint. The relaxed extremizer
may have an atom at $b$, while an actual regular packet has none. Validity
as a lower bound does not make that measure an arithmetic realization.

## Existing completeness and cone reduction

Theorem 7.2 (`thm:moment-expansion`) already gives a complete positive
moment hierarchy: every genuine ascent has a finite-order certificate.
Corollary 9.3 (`cor:infinite-packet-class`) supplies infinitely many such
later packets only from a source with $G(C_a)<e^\gamma$. It therefore
does not address a potentially nonpositive Robin margin. Remark 9.4
explicitly leaves uniform low-moment control on an unbounded family of
short packets as the arithmetic problem.

Theorem 10.4 (`thm:cone-envelope`) identifies, for each regular source,
the supremum over all multiples of $C_a$ with the tail supremum of
$\widehat{\mathcal F}$ and then with later regular returns, including the
source. This is a same-source extremal reduction, not a sign theorem.

## Scope of the project's additional packet analysis

The [project's §417](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
uses the already established $A(t)=t+o(t)$ on the actual event packets.
It evaluates the existing two-moment expression on fixed and unbounded
endpoint ratios and excludes its sufficient certificate uniformly when
$b/a\ge1+d$, for each fixed $d>0$ at sufficiently large $a$.
Consequently successful asymptotic certificates require $b/a\to1$.

That is a repository-derived scale limitation of this particular certificate,
not a new general inequality or a certified originality claim. The inspected
§§7.4 and 9 state sharpness and the short-packet arithmetic difficulty;
they do not supply this fixed-ratio constant comparison or its unbounded-ratio
uniform conclusion. This bounded source comparison does not certify an
exhaustive literature search. Shrinking width alone still does not force
successful actual moments, the full Robin sign, or RH.

The [project's §418](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
adds a quantitative condition on the same actual packet. For $a\ge e$ and
$L=b-a\le a$, let $M=\sup_{[a,b]}|A^+(t)-t|$. A successful two-moment
certificate requires $L^3\le6400a^2M$. The uniform-reference Hermite loss
and the moment formula are reused from Theorem 7.7 and Proposition 7.6;
the additional application controls the change in that expression by the
same packet's workload error. Theorem 8.5 (`thm:psi-normal-form`), combined
with an existing unconditional PNT error supplier, then yields a shrinking
necessary relative-width rate. These are restrictions on this sufficient
certificate, not a successful actual packet, an endpoint sign theorem,
an effective starting threshold, or a solution of §12's `prob:low-moment`.

## The remaining signed supplier and its sampling conditions

The [existing Guth–Maynard note](guthmaynard2024largevalues.md) already
supplies the uniform short-interval input and its project applications.
Within its stated range it applies to actual starting points without an
exceptional-center selection step. It still gives an absolute increment
allowance, not the signed workload surplus required by the packet
certificate. An almost-all estimate has an additional sampling obligation:
regular roots are locally finite, so an exceptional set of real measure
zero can contain all of them. Their use as noninteger endogenous endpoints
also requires the same estimate up to the chosen return, with the actual
layer correction retained.

The [Caveney–Nicolas–Sondow primary](../Arith/caveney2012sacaga.md),
Theorems 6–7, already gives infinite CA subclasses with and without GA1.
Its CA parameters and prime-deletion conclusions do not supply actual
regular tangent endpoints or forward signed moments. In particular,
Lemma 7's sufficient price inequality cannot be satisfied by directly
substituting the tangent price; another admissible price of the same
integer must be checked. The known $720720$ example is already covered
by that primary and the project's §98.5, so it is not a new counterexample.

For a precise arithmetic supplier target, keep the same actual packet and
put $E(t)=A^+(t)-t$, $L=b-a$, $K=-g'$, and $B=g''$. Set

$$
Q_0=\int_a^bE(t)dt,\qquad
Q_1=\int_a^b(t-a)E(t)dt,\qquad
W=Q_0-\frac{B(a)}{K(a)}Q_1.
$$

In the near-uniform regime $a\to\infty$, $L=o(a)$, $Q_0=o(L^2)$ and
$Q_1=o(L^3)$, the existing moment identities and two-node expression,
expanded by ordinary Taylor calculus, give

$$
H_g-\overline g
=\frac{K(a)}{L}
\left[W-\left(\frac1{36}+o(1)\right)\frac{L^4}{a^2}\right].
$$

The first two Taylor terms are exactly $K(a)Q_0/L-B(a)Q_1/L$.
The limiting two-node law has weights $3/4,1/4$ at normalized locations
$1/3,1$, so its third moment is $5/18$, whereas the uniform third moment
is $1/4$. Their difference is $1/36$; using
$g'''(a)/K(a)=-(6+o(1))/a^2$ and the Taylor factor $1/6$ gives the term
displayed. The fourth-order remainder is smaller by $O(L/a)$.
This is an application of existing moment and calculus interfaces, not
a new general moment theorem or an assertion made by the archived paper.

Consequently a fixed positive surplus
$W\ge(1/36+\epsilon_0)L^4/a^2$ on an unbounded actual family satisfying
those regime conditions would pay this intermediate two-moment target.
It is not established by the cited sources. Even a transferred absolute
bound $\sup|E|\le\epsilon(a)L$ only gives
$|W|\le\epsilon(a)L^2(1+O(L/a))$. For $L=a^\beta$, $\beta<1$, the
short-PNT-type allowance $\epsilon(a)L^2$, with
$\epsilon(a)=\exp[-(\log a)^{1/4}]$, remains asymptotically larger than
$L^4/a^2$. This compares guaranteed allowances;
it neither supplies the actual sign nor proves the packet fails.

An arbitrary unbounded winning family would address the archived
intermediate problem. Applying that family to full Robin still requires
a selection theorem covering the relevant potentially nonpositive
self-matching minima, without assuming those sources are safe.
