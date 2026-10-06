---
bibkey: kalyabin2026maximalgronwall
authors: Gennadiy A. Kalyabin
year: 2026
title: On Maximal Values of Gronwall Numbers for Integers with Given Greatest Prime Factor and Remainder in Modified Mertens Formula
doi: null
url: https://arxiv.org/abs/2603.24548v1
claim: The preprint states a sharp support-conditioned modified-Mertens calibration, with a lower construction on all sufficiently large supports and a matching upper bound only on its locally unimprovable support set E; it supplies no strict Robin sign or effective finite-source cutoff.
strata_touched: []
license: citation-only
triage: anchor
---

# Support-conditioned maximal Gronwall numbers

The primary is [arXiv:2603.24548v1](https://arxiv.org/pdf/2603.24548v1),
submitted 25 March 2026. The retrieved PDF has 16 pages and SHA-256
`faead89924bd201d95a6ac827a9cc3e5784929d8b8800a13bd6797059ecabed9`.
The locators below use its printed pages. Theorem 1, Definitions 2–4,
Theorem 2(I)(iv), and their arguments in §§2–4 were inspected against
the versioned PDF and [HTML](https://arxiv.org/html/2603.24548v1).
These are statements of a public preprint, not a journal-publication,
complete proof-audit, or Lean-verification claim. No source text is vendored.

## Exact support and quantifier scope

Put $P=p_k$, $T(P)=\prod_{p\le P}p$, and

$$
\begin{aligned}
G(N)&=\frac{\sigma(N)}{N\log\log N},\\
\widetilde W_k&=\{N>1:P^+(N)=p_k,\ T(p_k)\mid N\},\\
\widetilde g_k&=\log\max_{N\in\widetilde W_k}G(N),\\
S(P)&=\sum_{p\le P}\log\frac p{p-1},\\
Q(P)&=S(P)-\log\log\vartheta(P)-\gamma.
\end{aligned}
$$

The real logarithms in these comparisons are used on sufficiently large
supports. Theorem 1, printed pp.2–3, states

$$
\liminf_{k\to\infty}
\sqrt{p_k}\log p_k\,[\widetilde g_k-\gamma-Q(p_k)]
=-2\sqrt2.
$$

Its two parts have different domains. For each $\varepsilon>0$ there is
an existential cutoff $K_\varepsilon$ such that part (I) gives

$$
\widetilde g_k>
\gamma+Q(p_k)-\frac{2\sqrt2+\varepsilon}{\sqrt{p_k}\log p_k}
\qquad(k>K_\varepsilon).
$$

This is obtained from a constructed $M_k\in\widetilde W_k$; it is a
bound on the maximum, not on every member of that support class.
Part (II) gives

$$
\log G(N)\le\widetilde g_k<
\gamma+Q(p_k)-\frac{2\sqrt2-\varepsilon}{\sqrt{p_k}\log p_k}
\quad(k\in E,\ k>K_\varepsilon,\ N\in\widetilde W_k).
$$

Definitions 3–4, printed pp.5–6, specify

$$
\begin{aligned}
U_{1,k}
&=\{N:P^+(N)=p_k,\ N\in\mathrm{GA1},\
G(Np)\le G(N)\text{ for every prime }p\le p_k\},\\
E&=\{k:U_{1,k}\ne\varnothing\}.
\end{aligned}
$$

Definition 2's $U_1$ imposes the insertion comparison for **every** prime,
including primes beyond the support. The paper reports both $E$ and its
complement as infinite, referring to its earlier one-step-unimprovability
preprint [arXiv:1810.12585](https://arxiv.org/abs/1810.12585).
The upper estimate is not an eventual bound over all support indices.

## Directly reusable infinite one-step sources

The cited antecedent is Kalyabin, *One-Step G-Unimprovable Numbers*,
[arXiv:1810.12585v1](https://arxiv.org/pdf/1810.12585v1), submitted
30 October 2018. Its PDF has 11 pages and SHA-256
`6d45415c30ad326be291ccf4716d711975ea85bbabfbe822d119061d3898a72c`.
The definition on printed p.2, Theorem 1 on p.6, and Theorem 3 with its
argument on p.10 were inspected. This is primary-source scope checking,
not a complete proof audit or Lean verification.

Theorem 3 states that for every $M>0$ there is an actual integer $V_r$
with $P^+(V_r)>M$ and $V_r\in U_1$. Its one-step conditions retain the
same integer:

$$
G(V_r/p)\le G(V_r)\quad(p\mid V_r),\qquad
G(V_rp)\le G(V_r)\quad(p\text{ prime}).
$$

The 2026 paper's Proposition 5(IV), in §3, recalls an infinite subsequence
of these $V_k$ lying in $U_1$, hence with support indices in $E$.
The existence of an unbounded family with both single-prime comparisons
is therefore an existing supplier; neither its construction nor its
infinitude needs another proof here. It is stronger source information
than separately selecting a GA1 integer and an insertion-stable integer.

The multiplier comparison in $U_1$ still concerns one prime at a time.
GA2 requires every positive integer multiplier. The
[existing workload note](mantovanelli2026primeworkload.md) already records
an actual one-step source improved by the joint multiplier $3\cdot37$;
that comparison is reused rather than recomputed. Thus the cited
infinitude does not certify GA2 or establish an unbounded sequence of
selected Robin-critical global maximizers. It also provides no signed
modified-Mertens estimate or effective cutoff for one fixed source.

The antecedent's Proposition 1(i) prints the opposite comparison
$G(N)\le\min(G(N/p),G(Np))$. The conditions quoted above are those of
its definition and Theorem 1; the reversed line is not used as a
verified source condition.

## Uniform clock expansion on the eligible sources

Theorem 2(I)(iv), printed p.8, states the uniform clock expansion

$$
\sup_{N\in U_{1,k}}
\left|\frac{\log N-\vartheta(p_k)}{\sqrt{\vartheta(p_k)}}-\sqrt2\right|
\longrightarrow0
\qquad(k\to\infty,\ k\in E).
$$

Its uniformity is over actual $U_{1,k}$ members. It does not identify
$p_k$, $\vartheta(p_k)$, and $\log N$, or supply an effective cutoff for
an independently specified finite integer.

## Eligibility of the conditional critical source

Use the [Caveney–Nicolas–Sondow source reduction](../Arith/caveney2012sacaga.md)
directly. Under its counterexample hypothesis, let $N>5040$ be the least
integer attaining the global maximum of $G$ over that range. This is the
selected extraordinary, CA source, not the least Robin counterexample.
GA1 and GA2 imply $N\in U_1$ and $N\in U_{1,k}$ with $k$ its own support
index, so $k\in E$. Initial CA prime support gives $N\in\widetilde W_k$.

The small-support conditions can be discharged for this selected source
by reusing existing results. If $k\le4$, all prime factors of $N$ lie
in $\{2,3,5,7\}$. The repository's
[seven-smooth Robin theorem](../../Blueprint/D5/S3/Arith/Robin/SevenSmooth.md),
`robin_seven_smooth`, gives $G(N)<e^\gamma$, contradicting the selected
counterexample-level maximum. Its exponents are unrestricted, so this
exclusion has no finite enumeration cutoff. Hence $k>4$, and the
endpoint conditions below give $\log N<p_{k+1}$ at this same integer.

[Axler's existing valuation stop](../notes/axler2023robin.md), author
version [2110.13478v3](https://arxiv.org/pdf/2110.13478v3), Theorem 1.4
(published Theorem 3), gives strict Robin for $N>5040$ with
$v_2(N)\le20$. Thus $v_2(N)\ge21$ at the selected source. If $k=5$,
the endpoint would give $\log N<13$, whereas
$\log N\ge21\log2>13$. Therefore $k\ge6$, $P\ge13$, and

$$
T(P)\ge T(13)=30030>5040.
$$

Every member of $\widetilde W_k$ consequently belongs to the selected
global maximization domain, and $\log G(N)=\widetilde g_k$ without an
extra support-size hypothesis. This is a paper application of the cited
source conditions and existing seven-smooth theorem, not a new valuation
bound, enumeration, Lean declaration, or signed Robin estimate.
The source's asymptotic estimates still require their own
$k>K_\varepsilon$ cutoff; $k\ge6$ does not pay that requirement.

Consequently the asymptotic calibration along such sources with unbounded
support is

$$
\log G(N)=\gamma+Q(P)
-\frac{2\sqrt2+o(1)}{\sqrt P\log P},
\qquad P=P^+(N).
$$

This conditional asymptotic does not assert the existence of an unbounded
critical-source sequence. A single selected global maximizer has fixed
support; Theorem 1 gives no explicit $K_\varepsilon$ certifying that it lies
in the asymptotic range.

## Reusing the signed-tail clock comparison

For an actual $N\in U_1$ with $P=P^+(N)=p_k$ and $k>4$, set
$P^+$ equal to the next prime, and $A=\log N$. The 2026 Theorem
2(I)(ii)–(iii) and (III), together with the 2018 Lemma 3(i), already give

$$
P<\xi(P,0)+\log P\le A\le\xi(P^+,0)<P^+.
$$

Here the largest-prime exponent is one by Theorem 2(I)(ii).
Thus $\vartheta(A)=\vartheta(P)$; $(P,A]$ has no ordinary prime.
This is direct use of the published one-step conditions, with no new
source-selection theorem. The support restriction is material:
the 2026 footnote 4 records $14\in U_1$, whereas $\log14<7=P^+(14)$.

The signed-tail comparison in the
[Nicolas card](../ArithSums/nicolas2025comparison.md), under
“The endpoint condition at actual self-tangent sources”, can be reused
with the current endpoints $P,A$. The uniform clock expansion above
gives $A-\vartheta(P)=O(\sqrt P)$ along these $U_1$ sources with support
tending to infinity. The
[existing uniform short-interval input](guthmaynard2024largevalues.md)
gives $A-P\le P^+-P\le P^{2/3}$ eventually. The classical prime-power
decomposition and monotonicity therefore give the same interval budget
used in that comparison, $|\psi(u)-u|=O(P^{2/3})$ for $P\le u\le A$.
Direct integration against its existing kernel yields

$$
I_\psi(P)=I_\psi(A)+O\!\left(\frac{P^{-2/3}}{\log P}\right),
\qquad
Z_\psi(P)=c_NZ_\psi(A)+O(P^{-1/6}),
\quad
c_N=\frac{\sqrt P\log P}{\sqrt A\log A}
=1+O(P^{-1/3}),
$$

where $Z_\psi(t)=\sqrt t\log t\,I_\psi(t)$. The factor $c_N$ remains;
ratio convergence alone does not bound the normalized tail. This is an
application of the existing interval argument at the source's own
support, not the Nicolas card's primorial cutoff or a selected sieve
cutoff. It pays the eventual clock comparison on this source class,
without supplying a signed lower bound, an effective cutoff for a fixed
critical source, or an unbounded critical-source sequence. It introduces
no new generic interpolation theorem, prime-gap estimate, or Lean claim,
and does not extend the self-tangent pressure identity to arbitrary
$U_1$ hosts.

## What remains outside this supplier

The calibration leaves the needed one-sided comparison for $Q(P)$ open;
it does not imply $\log G(N)<\gamma$. The eventual source-clock comparison above
preserves its normalization factor and supplies neither that one-sided
bound nor a finite-source cutoff. The support calibration, the classical exponent
construction, and the existing pressure decomposition in
[the FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
are reused results, not new Robin estimates.

The paper identifies its lower construction as continuing
[arXiv:2201.02663](https://arxiv.org/abs/2201.02663), and its local source
classes as continuing arXiv:1810.12585. These antecedents are citation
links; their entire proofs are not independently certified here.
The inspected proof text contains notation slips: §4.1's verbal assignment
of the two exponent thresholds reverses the order required by its products,
and its claim that $\log\widetilde G(t)$ tends to zero at infinity differs
from the displayed formula. The formal theorem statements above are
recorded with their stated scope; these slips are not silently repaired or
used as verified intermediate lemmas.
