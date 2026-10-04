---
slug: yurischev-2017-xstate-unimodality
bibkey: yurischev2017extremal
doi: 10.1007/s11128-017-1701-0
url: https://arxiv.org/abs/1702.03728v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result
---

# Unimodality of the X-state conditional entropy

## Problem

M. A. Yurischev, *Extremal properties of conditional entropy and quantum
discord for XXZ, symmetric quantum states*, Quantum Inf. Process. 16, 249
(2017), arXiv:1702.03728v3.

Introduction:

> we suppose the unimodal property for the function $S_{cond}(\theta)$ (see
> Appendix). So, if the unimodality hypothesis is valid the only possibility
> (except the trivial case $S_{cond}(\theta)=const$) for a single local
> extremum (minimum or maximum) to appear or disappear inside the open
> interval by continuous varying the parameters defining the X state is the
> doubling the extremun at the ends of interval $[0,\pi/2]$.

The Appendix writes the conditional entropy of an X state as
$f_1(x)=-h_2\bigl(\frac{1+p_2x}2,\frac{1-p_2x}2\bigr)+h_4\bigl(\frac{1+p_2x\pm\sqrt{r_1}}4,\frac{1-p_2x\pm\sqrt{r_2}}4\bigr)$
on $x\in[0,1]$ (Eq. (A1)). Here
$r_{1,2}=(p_1\pm p_5x)^2+4w^2(1-x^2)$, $w=(|p_3+p_4|+|p_3-p_4|)/4$, and
$h_2,h_4$ are Shannon entropies in bits. The Appendix defines weak
unimodality as follows:

> A function $f(x)$ is a weakly unimodal function in the interval $[a,b]$ if
> there exists a value $x_m\in[a,b]$ for which it is weakly monotonically
> increasing for $x\le x_m$ and weakly monotonically decreasing for
> $x\ge x_m$. […] Analogous definitions are given for the minimum.

It then states the conjecture:

> The functions $f_1(x)$ and $f_2(x)$ for every choice of parameters
> $p_1,\ldots,p_5$ for which all arguments of Shannon functions are
> non-negative can have at most only one local extremum (minimum or maximum)
> in the open interval $x\in(0,1)$. […] It is required to prove or refute
> this proposition.

## Motivation

The hypothesis underlies the paper's bifurcation picture: interior extrema
of the conditional entropy appear and disappear only at the end points, so
the boundaries of the regions with an interior extremum are given by
end-point conditions. The frozen declaration
`D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result` shows
that the hypothesis fails for $f_1$.

## Gap

Issue #12783 classifies the hypothesis as Tier 1. Before any Lean it recorded
the following checks:

- The $f_2$ clause was answered by the same author, arXiv:1706.02852:
  bimodal entropy after measurement.
- That paper still describes the conditional entropy as "restricted by
  monotonic and unimodal types", "confirmed for … subclasses of X states"
  (source l. 677–682).
- arXiv:1903.08342 (l. 177) still bases its equations "on the unimodality
  hypothesis for the function $Q(\theta)$".
- Semantic Scholar lists 13 forward citations of arXiv:1702.03728 and 10 of
  arXiv:1804.03755. The arXiv-available ones were read in source: 2201.07005,
  2003.04542, 1911.04724, 1903.08342, 1706.02852, 1804.03755, 1908.02410.
  None states a counterexample for $f_1$.

These are orchestrator-checked readings, `not-found-in-searched-scope`. They
do not establish exhaustive worldwide novelty.

## Route

1. Take $p=(-2466,-1107,187,-163,1138)/2500$, so $w=187/5000$.
2. On $[0,1]$, $(1+p_2x)^2-r_1$ and $(1-p_2x)^2-r_2$ are nonnegative
   combinations of $(1-x)^2$, $x^2$ and $x(1-x)$, so every Shannon argument
   is nonnegative.
3. At $x=0,\tfrac{27}{50},\tfrac{177}{200},1$:
   - bracket the square roots by rationals;
   - bracket each Shannon argument $t$ by rationals $0<l\le t\le u\le1$;
   - use $l(-\log u)\le-t\log t\le u(-\log l)$;
   - bound $\log l$ and $\log u$ by the alternating-free series for
     $\log(1-y)$ after scaling by a power of $2$, together with
     $|\log2-287209/414355|\le10^{-10}$.
4. The resulting intervals for $f_1\log2$ give
   $f_1(0)>f_1(\tfrac{27}{50})<f_1(\tfrac{177}{200})>f_1(1)$, which no weakly
   unimodal function admits in either form.

## Falsifier

The kernel-checked `result` is the negation of the following statement. For
all real $p_1,\ldots,p_5$ such that the six arguments
$\frac{1\pm p_2x}2$, $\frac{1+p_2x\pm\sqrt{r_1}}4$ and
$\frac{1-p_2x\pm\sqrt{r_2}}4$ are nonnegative for every $x\in[0,1]$, the
function $x\mapsto f_1(x)$ is weakly unimodal on $[0,1]$. Weak unimodality
means that some $x_m\in[0,1]$ makes $f_1$ either weakly increasing on
$[0,x_m]$ and weakly decreasing on $[x_m,1]$, or weakly decreasing on
$[0,x_m]$ and weakly increasing on $[x_m,1]$.

This statement is the paper's own definition of weak unimodality applied to
$f_1$. The Appendix also defines strong unimodality, with strict
monotonicity. Every strongly unimodal function is weakly unimodal, so the
result also refutes the strong form.

The conjecture's wording counts local extrema. Read with non-strict local
extrema, it is false already for constant $f_1$: take $p_2=p_3=p_4=p_5=0$,
$|p_1|\le1$. The Introduction excludes that trivial case. A weakly unimodal function
has no strict local extremum in $(0,1)$ other than $x_m$. The Lean result
does not by itself produce two strict local extrema (see Triage).

## Evidence

- The four values (mpmath, 50 digits, bits):
  - $f_1(0)=0.0483262050$;
  - $f_1(27/50)=0.0483145773$;
  - $f_1(177/200)=0.0483282133$;
  - $f_1(1)=0.0483099449$.
- The certified intervals for $f_1\log2$ have widths at most $4.002\cdot10^{-8}$. The
  three separations used by the contradiction, for $f_1(0)>f_1(27/50)$,
  $f_1(177/200)>f_1(27/50)$ and $f_1(177/200)>f_1(1)$, are at least
  $8.0\cdot10^{-6}$.

The canonical source is
`D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.lean`.
- Public declarations: `h2`, `h4`, `wParam`, `r1`, `r2`, `f1`, `ArgsNonneg`,
  `WeaklyUnimodal`, `claim` and `result`.
- Reuse: `h2` and `h4` are the frozen `shannonEntropy` of
  `D5/S3/Entropy/MaxEntropy`, divided by `log 2`.
- Freeze identities:
  - module statement `sha256:cf25406f7afc7905d874ae45a0a4a947f2268004635fdb3f00f8354ce23fead6`;
  - `result` statement `sha256:97c57bb87c02426bbb21f1c24030917248ee275602295296c0e326aa5383471e`;
  - Freeze event `sha256:5ff336716a0de0e9df6e7731e14dfef554ec43b32510e2ce8ed981680d619d8c`.
    Its project-level frozen prerequisite is the Freeze event of
    `D5/S3/Entropy/MaxEntropy`.
- Axioms: the proof uses only `propext`, `Classical.choice` and
  `Quot.sound`. It contains no `sorry`, no `native_decide` and no new axiom.

## Triage

Tier 1 hypothesis of a 2017 journal article. Resolution: `Refuted`, by
`D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.result`.

- `proof_shape: bind-only`. The settlement of the named hypothesis is the new
  content; there is no escape witness.
- `admission_basis: open-problem-resolution` (issue #12783).
- Utility kind `certified-instance`, basis `refutes` the module's `claim`.

### What the settlement shows

- **Proved by `result`:**
  - the parameters $p$ above have nonnegative Shannon arguments on $[0,1]$;
  - $f_1(\cdot\,;p)$ is not weakly unimodal on $[0,1]$, in either the
    maximum or the minimum form.
- **Consequence for extrema (orchestrator argument, not stated in Lean):**
  - $f_1$ is continuous on $[0,1]$. Its minimum on $[0,177/200]$ is
    attained in the open interval, at a local minimum $m$. Its maximum on
    $[27/50,1]$ is attained in the open interval, at a local maximum $M$.
    Since $f_1(m)\le f_1(27/50)<f_1(177/200)\le f_1(M)$, the points $m$ and
    $M$ are distinct.
  - On $(0,1)$ all six Shannon arguments of this $p$ are positive, so $f_1$
    is real-analytic there. It is not constant, so $m$ and $M$ are strict
    local extrema.
  - The conjecture therefore also fails in its extremum-counting wording.
- **Where the example lives (orchestrator readings, not stated in Lean):**
  - $|p_1|=0.9864$ is close to $1$.
  - At the four points, the arguments $\frac{1+p_2x-\sqrt{r_1}}4$ and
    $\frac{1-p_2x-\sqrt{r_2}}4$ lie between $3\cdot10^{-4}$ and
    $6.5\cdot10^{-3}$, and the four values of $f_1$ differ by about
    $10^{-5}$ bits.
  - $h_2$ and $h_4$ are concave on their probability simplices (the paper
    calls them convex, l. 1395). Their curvature does not decide the shape,
    because $f_1$ is a difference of entropies.
- **Effect on the paper's other conclusions (checked by reading the v3
  source):**
  - Two statements do not hold for general X states:
    - the abstract's statement (l. 42–45) that $S_{cond}(\theta)$ "for X
      states can have at most one local extremum in the open interval";
    - the bifurcation argument of the Introduction (l. 169–175), by which interior
      extrema appear only by doubling at the end points.
  - The hypothesis is a statement about general X states (Appendix,
    l. 1300–1306). The witness's density matrix has unequal middle diagonal
    entries. It is therefore not symmetric, and lies outside the XXZ
    symmetric subclass studied in the body of the paper (orchestrator
    computation through the parametrization of [Y15]).
  - The numerical phase diagrams and the region boundaries found for that
    subclass are not contradicted by this example.
  - The boundary equations (SII1) of the Introduction (l. 151) capture regime changes that
    pass through the end points. For general X states they need not
    capture all of them.
  - arXiv:1903.08342 bases its equations on the same hypothesis for
    $Q(\theta)$. Outside the subclasses where unimodality is proved or
    checked, its conclusions are conditional.
- **Open here:**
  - whether $f_1$ is weakly unimodal on the XXZ symmetric subclass;
  - the largest number of local extrema of $f_1$ in $(0,1)$;
  - whether the counterexample region has positive measure in the
    seven-parameter X-state domain. The parameter walk that produced this
    witness passed through nearby rational $p$ with the same pattern; this
    is not proved.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained. The Lean kernel verifies the encoded
statement and its axiom closure. Its correspondence to the paper, including
the reading of "at most one local extremum" through the paper's definition of
weak unimodality, is checked by reading the source and the definitions.
