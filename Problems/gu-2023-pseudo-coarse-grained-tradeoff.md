---
slug: gu-2023-pseudo-coarse-grained-tradeoff
bibkey: gu2023dissipationtimetradeoff
doi: 10.1103/PhysRevE.108.L052103
url: https://arxiv.org/abs/2304.08752v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result
---

# Gu's pseudo-coarse-grained dissipation-time trade-off is false

## Problem

Jie Gu, *Speed limit, dissipation bound and dissipation-time trade-off in thermal relaxation processes*, Phys. Rev. E 108, L052103 (2023), DOI 10.1103/PhysRevE.108.L052103, arXiv:2304.08752v2, states the following conjecture in the section “Trade-off between dissipation and time,” Eq. (13). The verbatim sentence and equation are from `relaxation.tex`, lines 328 and 331 (the equation's mathematical content is rendered inline):

> Let us state  the third main result: for $N$-state dynamics evolving from $\boldsymbol{p}^\text{(i)}$ to $\boldsymbol{p}^\text{(f)}$ during $\tau$ with an total rate $\mathcal{W}$, the conjecture is that the entropy production $\Sigma$ is bounded from below by (referred to as trade-off bound)
>
> $\Sigma_\text{na} \ge \Sigma_{\Omega_i}(\mathcal W \tau) \quad i =1,2,\ldots,S_N^{(2)}.$

The displayed inequality concerns non-adiabatic entropy production, despite the sentence's use of $\Sigma$. Lines 333–337 define each binary comparison by a partition into two nonempty sets, the aggregate endpoints, and the original process's total rate and elapsed time. The source conventions and the two-state steady-state formula are also recorded in [the literature note](../Library/StatisticalMechanics/gu2023dissipationtimetradeoff.md).

Issue [#21842](https://github.com/the-omega-institute/trureturing/issues/21842) fixes the following restricted reading, encoded by `claim`. For every natural number $n$, rate array $a:\mathrm{Fin}\,n\to\mathrm{Fin}\,n\to\mathbb R$, vector $u$, real curve $P:\mathbb R\to\mathbb R^n$, real time $\tau$, and finite subset $\Omega$ of the states, put

$W_{ij}=a_{ij}$ for $i\ne j$, and $W_{jj}=-\sum_{i\ne j}a_{ij}$.

Assume all of the following:

- $a_{ij}>0$ whenever $i\ne j$;
- $u_i>0$ for every state, $\sum_i u_i=1$, and $Wu=0$;
- $P$ has derivative $WP(t)$ at every real $t$;
- $\tau>0$, every coordinate of $P(0)$ is positive, $\sum_iP_i(0)=1$, and every coordinate of $P(\tau)$ is positive;
- $\Omega$ and its complement are both nonempty.

Define $D(v\|w)=\sum_i v_i\log(v_i/w_i)$, $d(z\|b)=D((z,1-z)\|(b,1-b))$, and

$x=\sum_{i\in\Omega}P_i(0)$, $y=\sum_{i\in\Omega}P_i(\tau)$, $k=-\operatorname{Tr}W$, $s=x+(y-x)/(1-e^{-k\tau})$.

Whenever $0<s<1$, the proposed inequality is

$d(x\|s)-d(y\|s)\le D(P(0)\|u)-D(P(\tau)\|u)$.

The module proves `result : ¬ claim`. Thus even this restriction to positive off-diagonal rates, positive endpoints and an interior fitted binary steady state is false.

## Motivation

The proposed bound uses only two endpoints, an elapsed time and the total rate, while allowing dynamics without detailed balance. If valid for every partition, its maximum over partitions would give a general lower bound on non-adiabatic entropy production. The question is whether replacing the full process by an endpoint-matched binary relaxation preserves that inequality.

## Gap

Issue #21842 records the bounded literature check:

- Gu's v2 source retains the conjecture; the quoted source text was independently checked against the downloaded TeX.
- The preregistration's web search for the pseudo-coarse-graining trade-off with “conjecture” and “counterexample” returned Gu (2023; arXiv:2304.08752v2) and Bao–Hou (2023; arXiv:2303.06428), with no settlement found.
- The preregistration reports that Kolchinsky–Dechant–Yoshimura–Ito (2024 preprint; arXiv:2412.08432v2) addresses the distinct divergence conjecture, Gu's Eq. (11), rather than Eq. (13).
- The recorded Zenodo search and inspection of the three citations listed by OpenAlex found no settlement. The recorded repository search found no existing treatment.

`not-found-in-searched-scope`.

## Route

The helper names below refer to private lemmas of the canonical module. All vectors and constants in the construction are fixed, except where a lemma's real parameter and hypotheses are stated explicitly.

1. **Generator and modes.** Use $n=3$ and
   $W=\frac1{100}\begin{pmatrix}-101&1&100\\100&-101&1\\1&100&-101\end{pmatrix}$,
   $u=(1/3,1/3,1/3)$, $v=(2,-1,-1)$, $w=(0,\sqrt3,-\sqrt3)$, $\alpha=303/200$, and $\beta=99\sqrt3/200$.
   `rates_positive` proves positivity for every pair of distinct indices of this fixed rate array; `stationary` proves $Wu=0$; `mode_action` proves $Wv=-\alpha v+\beta w$ and $Ww=-\beta v-\alpha w$.
2. **Trajectory and endpoints.** Define
   $P(t)=u+e^{-\alpha t}(\cos(\beta t)v+\sin(\beta t)w)/12$,
   $\tau=\pi/\beta$, and $r=e^{-\alpha\tau}$.
   For every real $t$, `trajectory_deriv` proves that this fixed trajectory has derivative $WP(t)$. `endpoints` gives
   $p=P(0)=(1/2,1/4,1/4)$ and
   $q=P(\tau)=((2-r)/6,(4+r)/12,(4+r)/12)$.
3. **Admissibility of the binary fit.** `time_bounds` proves $\tau>0$ and $0<r<1/4$ for the fixed constants. `total_rate` gives $k=303/100$; `steady_formula` gives
   $s=(2-3r)/(6(1-r))$ for $x=1/2$ and $y=(2-r)/6$.
   For every real $r$ satisfying $0<r<1/4$, `steady_bounds` proves $0<(2-3r)/(6(1-r))<1/3$.
4. **Exact divergence comparison.** For every real $z$, `split_divergence` proves
   $D((z,(1-z)/2,(1-z)/2)\|u)=d(z\|1/3)$.
   For real $x,y,s$ with $0<x<1$, $0<y<1$, and $0<s<1$, `reference_change` proves
   $[d(x\|1/3)-d(y\|1/3)]-[d(x\|s)-d(y\|s)]=(x-y)\log(2s/(1-s))$.
   For every real $r$ with $0<r<1/4$, `strict_violation` applies these identities to the displayed $p,q,s$ and proves the strict reverse of the proposed inequality. The difference simplifies to
   $\frac{1+r}{6}\log\frac{4-6r}{4-3r}<0$;
   the logarithm's argument lies strictly between zero and one under exactly these hypotheses.
5. **Refutation.** `result` instantiates `claim` with this rate array, $u,P,\tau$ and $\Omega=\{0\}$ in $\mathrm{Fin}\,3$. Its proof checks positive normalized $u$ and $P(0)$, positive $P(\tau)$, both nonempty partition blocks, stationarity, the derivative hypothesis at every real time, positive elapsed time, and $0<s<1$. The claimed inequality contradicts `strict_violation` with the fixed residual and the hypotheses supplied by `time_bounds`.

## Falsifier

The comparison must use the source's column-generator convention, total rate and fitted binary reference distribution. Here `generator` has column sums zero, $k=-\operatorname{Tr}W$ is the sum of all off-diagonal rates, and `binarySteadyState` is exactly the endpoint formula of TeX lines 191–196. `klDivergence` is the source's finite sum with natural logarithms. Lean index $0$ corresponds to the source's state $1$.

The claim requires the differential equation at every real time, but positivity only at the two endpoints; it assumes normalization only at the initial endpoint. The calculation in Triage additionally verifies that this particular trajectory is a positive normalized probability vector for every nonnegative time. That calculation is not an extra Lean conclusion. All divisions and logarithms used in the witness have nonzero denominators and positive logarithm arguments. The refutation concerns $\Sigma_{\rm na}$, as displayed in Eq. (13); it does not assert a violation of a bound on total entropy production $\Sigma$.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.lean` (257 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It uses `generator` from `MarkovMpembaTripletRefutation`, `klDivergence` from `ClassicalDPI`, and Mathlib's derivative, exponential, trigonometric and logarithm lemmas.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.lean.json`, statement `sha256:0754631c2303feec6a6a18d4aca735cb84ccf285183bef46d3ce192f90aafa56`.

Declaration statements:

- `result`: `sha256:ea53b46a622585e8dd9b44b836c54c50616c53174551716dea3229bcf3839cee`;
- `claim`: `sha256:df119dfd5671b769e113107628c1c09bf180d6d978f1a6f344e3785588532f50`.

## Triage

Tier 1 explicitly stated conjecture of a 2023 journal letter, preregistered in issue #21842 before any Lean.
`theorem`; resolution `refuted`.

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** `claim` is false: the inequality in Problem is not valid for every choice of its quantified data satisfying all the listed hypotheses.

**Computed, not formalized**. An independent 80-digit mpmath matrix-exponential evaluation of the single displayed witness gives $\tau\approx3.66424113986711$, $r\approx0.00388230850445873$,
$q\approx(0.332686281915924,0.333656859042038,0.333656859042038)$, and $s\approx0.332683760072127$.
The full divergence drop is approximately $0.0588905755030222$, the fitted binary drop is approximately $0.0593798855623970$, and their difference is approximately $-0.000489310059374850$. The maximum absolute difference between the matrix-exponential endpoint and its closed form is below $1.6\cdot10^{-81}$; the absolute discrepancy in the logarithmic difference formula is below $3\cdot10^{-81}$. These are numerical readings for this witness, not evidence for other inputs.

**Argued, not formalized**.

- *Physical trajectory.* Both mode vectors have coordinate sum zero, so $\sum_iP_i(t)=1$. For every coordinate, the pair of cosine and sine coefficients has Euclidean length $2$: the pairs are $(2,0)$, $(-1,\sqrt3)$ and $(-1,-\sqrt3)$. Thus, for every $t\ge0$, $P_i(t)\ge1/3-e^{-\alpha t}/6\ge1/6$. This supplies the probability-path bridge to the source's setting beyond the endpoint requirements of `claim`.
- *Mechanism.* The damped rotating mode takes the selected population below its true stationary value $1/3$. A binary relaxation matched to these endpoints with total rate $k$ has the fitted stationary value $s$, which is different from the aggregate of $u$. Endpoint matching does not preserve the reference distribution in the entropy-production formula. The source itself warns, at TeX line 346, that “the population ${P}_\Omega(t)$ is in general not equal to $\sum_{n \in \Omega} p_n(t)$ except at the two endpoints”. Data processing applied separately to the initial and final divergences supplies no general inequality between their differences, and does not justify changing their stationary reference.
- *A surviving exact case.* For a genuine two-state generator $\begin{pmatrix}-a&b\\a&-b\end{pmatrix}$ with $a,b>0$, a positive normalized initial vector and $\tau>0$, write $k=a+b$ and $s_0=b/k$. Column sums zero preserve the initial normalization. Its first coordinate solves $z'(t)=-k(z(t)-s_0)$, hence $z(t)=s_0+(z(0)-s_0)e^{-kt}$. Substitution in the fitted formula gives $s=s_0$, since $1-e^{-k\tau}>0$. The full and binary divergences are then identical, so the conjectured comparison is equality. This elementary two-state argument is not a theorem of the settlement module.
- *A surviving limit under explicit convergence.* Fix positive normalized $p,u$ and a nonempty proper $\Omega$. If $P(\tau)\to u$ and $k>0$ is fixed as $\tau\to\infty$, then $s\to u_\Omega=\sum_{i\in\Omega}u_i$. The full and binary drops tend respectively to $D(p\|u)$ and $d(p_\Omega\|u_\Omega)$. Applying the log-sum inequality separately to the two blocks gives $D(p\|u)\ge d(p_\Omega\|u_\Omega)$. Thus this conditional limiting comparison survives; it gives no finite-time inequality.
- *Open repairs.* This generator does not satisfy detailed balance with $u$: opposite off-diagonal rates are $1$ and $1/100$, while $u$ is uniform. Whether detailed balance suffices for Eq. (13), or which additional compatibility condition on the binary dynamics suffices for general multistate processes, remains open here. Neither a replacement universal trade-off nor a statement about total entropy production is supplied.
- *Effect on the paper.* Eq. (13) cannot provide a universal exclusion region for the dissipation-time plot in Fig. 1(c), or a universal lower bound whose superiority to other bounds is inferred from comparing its numerical value. The examples in Fig. 1(c) and Fig. 2 are not individually refuted by this witness. The source's separate speed-limit argument in TeX lines 460–505 does not use Eq. (13), so this refutation does not invalidate that argument. Gu's Eq. (11) is a distinct conjecture, not the statement encoded by `claim`. A proposed quantum generalization of the unrestricted Eq. (13) would already have to address this classical counterexample.

## ASSUMED-UNVERIFIED

The bounded literature check establishes neither exhaustive worldwide novelty nor priority. The web, Zenodo, OpenAlex, citing-work and Kolchinsky–Dechant–Yoshimura–Ito source readings reported in issue #21842 were not reproduced for this dossier; the OpenAlex count and negative literature findings remain attributed reports.

Gu's conjecture, generator convention, divergence definition, binary fit, numerical-evidence discussion and downstream uses were checked in the downloaded arXiv:2304.08752v2 TeX, member `relaxation.tex` (MD5 `73c406829510539d2db7d2bb969829fb`). The source's random-sampling runs, optimization plots and supplemental numerical verification were not reproduced. No assertion is made that those particular sampled data contain a violation.

Everything labelled “Computed, not formalized” or “Argued, not formalized” is outside the formal conclusion of `result`, including positivity and normalization along the nonnegative-time trajectory, the two-state equality argument, the conditional limiting comparison and the dependency analysis of the source. The detailed-balance restriction, other repaired bounds and a total-entropy-production version remain unsettled here.
