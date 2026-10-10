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

## The existing prime-local bridge

Theorem `thm:direct-bridge`, §4 of the same archived manuscript,
starts with an actual integer $N>e$ satisfying

$$
N/p>e,\qquad G(N)\ge G(N/p)\quad(p\mid N),
\qquad G(N)\ge G(Np)\quad(p\text{ prime}).
$$

It directly gives $N=C_A$, $\Phi_{\rm CA}(A)=A$ and an event-free
scale $A=\log N$, with price $1/(A\log A)$. The statement is about
every proper prime-local Robin well; neither GA1 alone nor an arbitrary
self-tangent return supplies its insertion hypothesis. This bridge is
reused without reconstructing its neutral-layer proof.

Lemma `lem:external-extremal-input` and Theorem
`thm:persistent-obstruction`, §11, select the least global maximizer
of $G(n)$ on $n>5040$ under RH failure and place this single proper
GA1–GA2 source at a regular return. They state no unbounded regular
family with a fixed power-sized excess. The
[same-source quantified selection](../Arith/caveney2012sacaga.md#the-same-power-excess-family-also-supplies-proper-ga1-sources)
uses the prime-local bridge on its selected family; its family and excess
quantifiers are separate from that fixed-maximizer reduction. These
source statements and their hypothesis correspondence were inspected;
no independent full proof audit or Lean certification is claimed.

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

## Source-local multipliers use the existing finite-size and cone results

Section 4's `lem:neutral-point` and `thm:neutral-mean` already give the
finite layer's insertion/deletion thresholds. A successful untied singleton
packet has $C_b=pC_a$, so its source is improved by one prime insertion.
It therefore cannot start at a proper prime-local well, where every such
insertion is non-improving. This is a direct application of the cited source,
not a new obstruction theorem. Arbitrary winning singleton families do
not pay the source-selection obligation at these wells.

The existing `thm:cone-envelope` gives a less restrictive constructive
target: any actual multiple $m$ with $G(m)>G(C_a)$ guarantees an improving
later regular return. A joint multiplier need not itself be a CA prefix or
end at a prescribed return. Endpoint isolation and a fixed packet length
are optional stronger conditions for a particular construction.

The [source-local multiplier experiment](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/fib-source-local-multipliers/README.md)
reuses catalog factorizations and the author's original rational log
enclosure implementation for 109 additional comparisons. At
$N=2021649740510400$, all single-prime insertions and deletions decrease
$G$. The archive's existing `verification/packet_identity_checks.json`
already verifies the ascent to return 7, precisely the joint insertion
$3\cdot37$; that positive comparison is directly reused, not recomputed
as a new result. At
$N=160626866400$, all one- and two-prime insertions decrease it, including
repeated primes. Its $2\cdot29$ descent is also directly reused from the
archive's existing return 4-to-5 check, leaving 65 additional pair
comparisons at that source. Universal prime coverage here uses the elementary
absent-prime replacement argument stated in the report; the computed
intervals themselves cover its finite pool. Neither the integers nor
the log-enclosure method are claimed as new discoveries.

These finite applications distinguish actual joint improvement from
single-layer improvement, and disallow a universal two-prime shortcut at
all proper local wells. They give neither an unbounded family nor a
result restricted to potentially persistent Robin-level sources. The
full signed source-coverage obligation remains open; these additions have
no Lean verification or literature originality certification.

### Repetitions can be removed within a bounded multiplier search

The existing layer formula in §2, `eq:layer-data`, and the finite-size
comparison in §4 give a useful paper-level pruning interface. Keep the
same integer $N$, put $A=\log N>27/8$, and assume
$G(Np)\le G(N)$ for every prime $p$. For every positive integer multiplier
$u$ with $W=\log u\le A/2$, let $\operatorname{rad}(u)$ be the product of
its distinct prime factors, with $\operatorname{rad}(1)=1$. Then

$$
G(N\operatorname{rad}(u))\ge G(Nu),
$$

with strict inequality when $u$ has a repeated prime factor. This uses
neither a CA hypothesis nor a prior positive Robin margin.

For the calculation, write

$$
c_A(w)=\log\log(A+w)-\log\log A=\int_A^{A+w}g(t)\,dt,
\qquad
h_{p,j}=\log r_{p,j}.
$$

If $S_{p,j}=p+\cdots+p^j$, the classical formula gives
$S_{p,j+1}=p(S_{p,j}+1)$. The elementary bounds
$\log(1+t)<t$ and $\log(1+t)\ge t/(1+t)$, for $t>0$, hence give

$$
h_{p,j+1}<\frac1{p(S_{p,j}+1)}\le\frac{h_{p,j}}p.
$$

Source insertion stability says
$h_{p,v_p(N)+1}\le c_A(\log p)$. If a current multiplier still contains
at least two copies of $p$, its top inserted layer therefore has reward
less than $\tfrac12(\log p)g(A)$. The current integer $m$ has
$A\le\log m\le A+W$, and removing that copy saves the denominator cost

$$
\int_{\log m-\log p}^{\log m}g(t)\,dt
\ge(\log p)g(A+W)>\tfrac12(\log p)g(A).
$$

The last inequality follows from $W\le A/2$ and
$(3A/2)\log(3A/2)<2A\log A$, which is equivalent to $A>27/8$.
Thus each such deletion strictly increases $G$. Iterating removes only
the repeated copies in $u$, retains $N$ and all required stack prefixes,
and reduces the multiplier budget. Intermediate states need not be
insertion-stable: the comparison continues to use the original source's
next-layer bound. When $u$ is squarefree the two integers coincide.

Consequently, within this budget, an improving multiplier with at most
$k$ inserted layers exists exactly when an improving subset of at most
$k$ distinct primes exists. A construction with the explicit bound
$W=O(\log A)$ eventually lies in this budget. A fixed layer count alone
does not imply that bound. The reduction need not preserve exactly $k$
layers, a prescribed endpoint, or the structure of an actual return packet;
it is suitable for the unrestricted-multiple target of `thm:cone-envelope`.
It supplies no improving subset or critical-source coverage.

This is a derived application of the cited layer and finite-size data,
not a statement attributed verbatim to the manuscript, a new generic
inequality, or a Lean result. No originality certification or full
Robin/RH conclusion is supplied.

## The complete Euler transform of actual GA2 subset losses

This is a scope check using classical Bernstein complete alternation and
finite Euler expansion, not an additional theorem attributed to the
archived manuscript or a new Robin estimate. Use the
[Caveney–Nicolas–Sondow GA2 condition](../Arith/caveney2012sacaga.md)
at one actual integer $N>5040$, put $A=\log N$, and assume
$P^+(N)\le A$. For a finite prime set $\mathcal B\subset\{p:p>A\}$,
define, for every $\mathcal S\subseteq\mathcal B$,

$$
\begin{aligned}
q_{\mathcal S}&=\prod_{p\in\mathcal S}p,&
w_{\mathcal S}&=\log q_{\mathcal S},&
b_{\mathcal S}&=\sum_{p\in\mathcal S}\log(1+1/p),\\
C_A(w)&=\log\log(A+w)-\log\log A,&
L_A(\mathcal S)&=C_A(w_{\mathcal S})-b_{\mathcal S}.
\end{aligned}
$$

Multiplicativity and GA2 directly give
$L_A(\mathcal S)=\log[G(N)/G(Nq_{\mathcal S})]\ge0$.
All comparisons retain the same $N$. The empty block is included with
$q_\varnothing=1$ and $L_A(\varnothing)=0$.

The denominator cost has the classical positive representation

$$
C_A(w)=\int_{(0,\infty)}(1-e^{-wt})\,\nu_A(dt),\qquad w\ge0,
$$

with a nonzero positive measure. It can be checked without a general
Bernstein theorem: the classical log integral and the Gamma Laplace
integral, with $r=s/\log A>0$, give

$$
\begin{aligned}
C_A(w)
&=\int_0^\infty\frac{e^{-s}}s
\left[1-(1+w/A)^{-s/\log A}\right]ds\\
&=\int_0^\infty\int_0^\infty
(1-e^{-wt})\frac{e^{-s}A^r t^{r-1}e^{-At}}{s\Gamma(r)}\,dt\,ds.
\end{aligned}
$$

Tonelli applies to this positive integrand. The density on $s,t>0$ is
strictly positive. For every nonempty $\mathcal U\subseteq\mathcal B$,
the interaction integral

$$
I_A(\mathcal U)=\int_{(0,\infty)}
\prod_{p\in\mathcal U}(1-p^{-t})\,\nu_A(dt)
$$

is finite and strictly positive: selecting $p_0\in\mathcal U$, its
integrand lies between zero and $1-p_0^{-t}$, whose integral is
$C_A(\log p_0)<\infty$.

Set $E_0=\prod_{p\in\mathcal B}(1-1/p)>0$. The actual complete
Euler-weighted loss transform satisfies

$$
\begin{aligned}
\mathsf T_A(\mathcal B)
&:=\sum_{\mathcal S\subseteq\mathcal B}
\frac{\mu(q_{\mathcal S})}{q_{\mathcal S}}L_A(\mathcal S)\\
&=-E_0\left[
\sum_{p\in\mathcal B}\frac{L_A(\{p\})}{p-1}
+\sum_{\substack{\mathcal U\subseteq\mathcal B\\|\mathcal U|\ge2}}
\frac{I_A(\mathcal U)}{\prod_{p\in\mathcal U}(p-1)}\right].
\end{aligned}
$$

For the finite calculation, keep
$E_{\mathcal B}(t)=\prod_{p\in\mathcal B}(1-p^{-1-t})$ and use

$$
\sum_{\mathcal S\subseteq\mathcal B}
\frac{\mu(q_{\mathcal S})}{q_{\mathcal S}}C_A(w_{\mathcal S})
=\int_{(0,\infty)}[E_0-E_{\mathcal B}(t)]\,\nu_A(dt),
$$

$$
\sum_{\mathcal S\subseteq\mathcal B}
\frac{\mu(q_{\mathcal S})}{q_{\mathcal S}}b_{\mathcal S}
=-E_0\sum_{p\in\mathcal B}\frac{\log(1+1/p)}{p-1},\qquad
\frac{E_{\mathcal B}(t)}{E_0}
=\prod_{p\in\mathcal B}\left(1+\frac{1-p^{-t}}{p-1}\right).
$$

Expand the last finite product completely. Its singleton terms integrate
to $C_A(\log p)$ and combine with the additive benefits to yield the
displayed loss transform. Keep $E_0-E_{\mathcal B}(t)$ together inside
the integral; the individual constant integrals need not converge.

Thus $\mathsf T_A(\mathcal B)\le0$, and it is strictly negative if
$|\mathcal B|\ge2$. This conclusion needs only the actual singleton
losses to be nonnegative; strict singleton losses are unnecessary.
For $\mathcal B=\varnothing$ the transform is zero, and for
$\mathcal B=\{p\}$ it is $-L_A(\{p\})/p$. No subset order is discarded.
The particular choice $\mathcal B=\{p:A<p\le2A\}$ is allowed; no limit
over an infinite prime tail is asserted.

Consequently neither pointwise GA2 loss positivity nor the additional
Bernstein structure makes this particular complete transform nonnegative.
Its negative has the displayed positive decomposition, but no
sign-preserving comparison with the already recombined actual
$I_\psi(A)+R(A)$ has been supplied. The
[FIB volume's §§434–435](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
pair the native same-filter kernel window with its complete complement;
those are different quantities and are reused directly. This scope check
excludes the proposed unflipped loss transform as a positive supplier,
not other Abel or cumulative transforms, and gives no Robin-critical
margin, source coverage, new Bernstein theorem, or Lean verification.

## Divisor-record box geometry does not transfer to Robin records

The inspected primary is Marco Mantovanelli, *Prime-Exponent Transition
Geometry and Divisor Barriers Between Consecutive Highly Composite Numbers*,
[arXiv:2608.17045v1](https://arxiv.org/html/2608.17045v1),
17 August 2026. Its definitions in §2, Proposition 4.1, Theorem 4.2,
Corollary 4.3 and layer spectrum in §7.1 were read. This identifies the
inspected version; a latest-version comparison and whole-paper proof audit
are not supplied. No computation from its companion archive is a premise.

The source uses the closed prime-exponent box

$$
\mathcal B(m,n)=\left\{\prod_p p^{e_p}:
\min(v_p(m),v_p(n))\le e_p\le\max(v_p(m),v_p(n))\right\}.
$$

Proposition 4.1 supplies the complementary state $z^\sharp=mn/z$ in
the same box, with $zz^\sharp=mn$ and
$d(z)d(z^\sharp)\ge d(m)d(n)$. Theorem 4.2 gives
$\mathcal B(H,H')\cap(H,H')=\varnothing$ for consecutive strict
**divisor-count** records. Corollary 4.3 consequently puts every interior
state of a ceiling-admissible mixed geodesic below $H$. These published
results are reused, not reproved. The layer reward in §7.1 is
$\log((j+1)/j)$ for $d(n)$; it is not a layer reward for
$Z(n)=\sigma(n)/n$ or $G(n)=Z(n)/\log\log n$.

There is already a published actual pair that prevents transferring
the box-gap conclusion to consecutive XA records. Use $H=n_1$ and
$H'=n_3$ from Nazardonyavi–Yakubovich, Remark 5.5, printed p.26,
[arXiv:1211.2147v3](https://arxiv.org/pdf/1211.2147v3), as cited in the
[existing XA source note](../Arith/caveney2012sacaga.md).
Their consecutive XA status is the primary's reported numerical result,
not independently reproduced here. Their published factorizations give

$$
H'=H\,\frac{149\cdot151}{2},\qquad
v_2(H)=9,\quad v_2(H')=8.
$$

The other changed coordinates are $v_{149},v_{151}:0\to1$; all remaining
coordinates agree. Thus the actual integers

$$
z=149H,\qquad z^\sharp=\frac{151H}{2}
$$

both belong to $\mathcal B(H,H')\cap(H,H')$, and satisfy
$zz^\sharp=HH'$. Membership and the strict size inequalities follow
directly from those factorizations; no new enumeration is required.
Conditional on the cited record classification, this is a counterexample
to the XA version of the proposed box-gap transfer, not to the source's
HCN theorem or to Robin's inequality.

The normalization explains why the reflected-product argument does not
force a contradiction here. Each changed exponent has only its two
endpoint choices, so multiplicativity gives
$Z(z)Z(z^\sharp)=Z(H)Z(H')$. Set $t=\log n$ and
$b(t)=\log\log t$ for $t>1$. Ordinary calculus gives

$$
b''(t)=-\frac{1+\log t}{t^2(\log t)^2}<0.
$$

The two interior logarithms have the same sum as the endpoint logarithms.
Strict concavity therefore yields
$b(\log z)+b(\log z^\sharp)>b(\log H)+b(\log H')$, and consequently

$$
G(z)G(z^\sharp)<G(H)G(H').
$$

Thus the size denominator changes the product comparison needed by the
HCN proof. This is a direct scope application of the published example
and elementary multiplicativity and calculus, not a new general
reflection theorem, a signed prime-error estimate, or a Lean result.

There is a separate source-selection obstruction: under a Robin
counterexample hypothesis, the project's selected least global maximizer
is the last XA, by the existing source note. It has no later strict
$G$-record with which to form the required consecutive pair. Neither
replacing it by a divisor-count record nor assuming a later XA retains
that source. A usable joint-prime supplier must apply at the same actual
selected integer and control the full Robin-normalized comparison;
the cited box geometry does not supply it.

## Local root spacing controls the sign-exact first-layer sampling error

Use the existing full largest optimizer $C_b$ and let
$R(n)=\log G(n)-\gamma$. For $X\ge4$ and
$X\le u<v\le3X$, put $I=[u,v]$ and $h=v-u$.
For any real threshold $t$, let $K_I(t)$ count the complete
positive-length plateaus intersecting $I$ in positive length and
satisfying $R(C_b)>t$. Define the actual post-event sample count

$$
P_I(t)=\sum_{\substack{p\text{ prime}\\u\le\tau_{p,1}<v}}
\mathbf1_{\{R(C_{\tau_{p,1}})>t\}}.
$$

Every simultaneous layer is included in $C_{\tau_{p,1}}$.
The [existing actual-event charging](stadlmann2022meansquaregaps.md)
applies with this exact full-state sign, before its prime-prefix
upper relaxation. Distinct first-prime samples give distinct
plateaus, and only an initial boundary plateau or higher-only
event can create an extra counted state. Consequently

$$
0\le K_I(t)-P_I(t)\le1+H_I,\qquad
H_I=\#\{(p,j):j\ge2,\ u\le\tau_{p,j}<v\}.
\tag{LS1}
$$

This reuses the existing bookkeeping rather than giving a second
proof of it. The local bound below adds a dependence on the actual
interval length; it does not estimate either sample's Robin sign.

For the usual real layer root $x_j(b)>1$, use

$$
F_j(x)=\frac{\log(1+1/S_j(x))}{\log x},\qquad
S_j(x)=\sum_{k=1}^j x^k,\qquad F_j(x_j(b))=g(b).
$$

The classical decreasing threshold has limits $\infty$ and $0$
at the two ends of $(1,\infty)$, so its inverse root is well
defined. For $x\ge2$ and $j\ge2$, logarithmic differentiation gives

$$
-\frac{F_j'(x)}{F_j(x)}
=\frac{S_j'(x)}{S_j(x)(S_j(x)+1)\log(1+1/S_j(x))}
+\frac1{x\log x}\ge\frac j{4x}.
\tag{LS2}
$$

Indeed, $\log(1+1/S_j)\le1/S_j$, $S_j+1\le2S_j$,
$S_j\le2x^j$ and $S_j'\ge jx^{j-1}$ give the displayed
lower bound. With $-g'(b)/g(b)\le2/b$ for $b\ge e$,
implicit differentiation yields
$0<x_j'(b)\le8x_j(b)/(jb)$ wherever $x_j(b)\ge2$.

Put $Q_X=3X\log(3X)/\log2$ and
$d_X=\lfloor\log Q_X/\log2\rfloor$.
The [existing activation cutoff](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
§420.2, proof preceding (420.5), gives $p^j<Q_X$ for every layer active
by $3X$, hence only $j\le d_X$ can contribute. On the effective
part $x_j\ge2$ it also gives $x_j<Q_X^{1/j}$. For $j=2$,
comparison at $x=\sqrt{2b}$ gives $x_2(b)<\sqrt{2b}$:
$x^2\log x=b\log(2b)>b\log b$ and
$F_2(x)<1/(x^2\log x)<g(b)$.

Set $r_j(b)=\max(2,x_j(b))$. This increasing root has at most
one clipping corner; its derivative bound can be integrated on
either side. Integer counting in its image, followed by the
derivative estimate, therefore gives the finite bound

$$
\begin{aligned}
H_I&\le d_X+\sum_{j=2}^{d_X}[r_j(v)-r_j(u)]\\
&\le d_X+\frac{8h}{X}
\left[\frac{\sqrt{6X}}2+Q_X^{1/3}\log d_X\right].
\end{aligned}
\tag{LS3}
$$

The harmonic sum for $j\ge3$ is at most $\log d_X$.
Root endpoints with $u=\tau_{p,j}$ or $v=\tau_{p,j}$ are
covered by the one-integer allowance per layer; the right price
endpoint remains excluded in $H_I$. Together with (LS1), this gives
uniformly over these intervals and all real $t$,

$$
\boxed{0\le K_I(t)-P_I(t)
\ll h/\sqrt X+\log X.}
\tag{LS4}
$$

For the particular fixed exponent of the existing selected-source
interval, $h=\lambda A^{1-\eta/2}e^{(\log A)^{1/4}/2}$,
take $X=A$. Its sampling error relative to $h/\log A$ is
$O(\log A/\sqrt A+(\log A)^2/h)=o(1)$.
The interval and threshold may depend on actual arithmetic data;
the bound is pointwise and assumes no independence.

Unlike a separate prime-product upper envelope, $P_I$ keeps the
complete exponent tail and actual size in every sign test. No
upper estimate on $P_I(t)$ or its positive-part moments is supplied.
This is a paper-level application of the layer geometry and existing
charging, not a new prime theorem, originality claim, Lean
certification, complete signed Robin estimate or RH proof.
