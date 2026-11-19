---
slug: yin-polygamma-majorization-refutation
bibkey: yin2022polygamma
doi: 10.7153/jmi-2022-16-62
url: https://files.ele-math.com/articles/jmi-16-62.pdf
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.result
---

# Yin's finite polygamma majorization conjecture

## Problem

Li Yin, *Monotonic properties for ratio of the generalized (p,k)-polygamma
functions*, Journal of Mathematical Inequalities 16(3) (2022), 915–921,
Conjecture 4.1, p. 920, DOI 10.7153/jmi-2022-16-62. The
[Library note](../Library/Asymptotics/yin2022polygamma.md) contains the source
quotation, definitions and verified locator. There is no arXiv identifier in
the located source metadata. Preregistration: [#24132](https://github.com/the-omega-institute/trureturing/issues/24132).

For a positive integer $p$, positive real $k$ and $x>0$, put

$$\psi_{p,k}(x)=k^{-1}\log(pk)-\sum_{j=0}^{p}(jk+x)^{-1},\qquad
\psi_{p,k}^{(r)}(x)=\frac{d^r}{dx^r}\psi_{p,k}(x).$$

For positive integer tuples $a,b$ of length $n\ge1$, $a\prec b$ means that
their descending rearrangements differ, every proper prefix sum for $a$ is
at most the corresponding prefix sum for $b$, and the total sums are equal.
The source asserts that

$$Q_{a;b,p,k}(x)=\frac{\prod_{i=1}^{n}\psi_{p,k}^{(a_i)}(x)}
{\prod_{i=1}^{n}\psi_{p,k}^{(b_i)}(x)}$$

is decreasing on $(0,\infty)$ and has image exactly

$$\left(\frac{\prod_i(a_i-1)!}{\prod_i(b_i-1)!},
\frac{\prod_i a_i!}{\prod_i b_i!}\right).$$

### Statement echo

| Source clause | Lean counterpart | Fidelity boundary |
| --- | --- | --- |
| Equation (1.5), finite sum | `psi` | Literal finite-sum right-hand side; total real function restricted by the claim to $x>0$. |
| The derivative definition before (1.5) | `polygamma` | `iteratedDeriv` of `psi`, retaining all orders. |
| Strict majorization on p. 916 | `StrictlyMajorized` | `moreMixed` and distinct `desc` rearrangements after natural-to-real casts; no additional hypothesis. |
| Positive $p,k,n$ and positive orders | Binders and positivity hypotheses of `claim` | Finite-product convention gives positive natural $p,n$ and orders; $k$ is real. |
| The product quotient | `Q` | All $n$ factors; `Fin n` replaces one-based indexing. |
| Decreasing on $(0,\infty)$ | `AntitoneOn` conjunct of `claim` | Weak decrease is refuted, hence strict decrease is refuted too. |
| Onto the factorial interval | Image equality conjunct of `claim` | Both endpoints and the complete image equality are retained. |
| Refutation of the whole assertion | `result` | Literal type $\neg\mathrm{claim}$, with no assumptions. |

The two signs printed in equation (1.6) disagree. The functions here follow
the derivative definition and (1.5), which give $(-1)^{r+1}r!$ times the
positive reciprocal sum. The inconsistent printed finite-sum sign is not a
premise. Changing all positive-order factors to the opposite printed sign
would cancel in the equal-length product quotient.

## Motivation

The settling node is
`D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.result`.
The module has `generality: G`, `utility: none` and
`admission_basis: open-problem-resolution (#24132; Refuted)`.
All proof declarations are classified bind-only compositions; the settlement
uses the named external-open-problem admission basis and claims no escape witness.

The symbolic result is an escape-audit target. Its four-slot registration is
unfinished, with the original theorem and missing evidence listed in
[issue #29215](https://github.com/the-omega-institute/trureturing/issues/29215).
There is no utility-refutation exemption and no delivered Reg mirror.

## Gap

The source's finite truncation has a zero-shift node and at least one distinct
positive-shift node. Its normalized neighboring-moment quotient has equal
endpoint limits but a strict interior deficit. A monotonicity assertion
cannot hold under these three facts simultaneously.

## Route

For $p\ge1$, $k>0$, $m\ge2$ and length $n=l+2\ge2$, take

$$a=(m,\ldots,m),\qquad b=(m-1,m+1,m,\ldots,m).$$

`family_majorization` proves $a\prec b$, and `orders_positive` proves the
positive-order hypotheses. Write $S_r(x)=\sum_{j=0}^{p}(jk+x)^{-r}$ and
$c=m/(m+1)$. The private derivative bridge `polygamma_eq` and nonvanishing
lemma `polygamma_ne_zero` justify cancellation in `Q_family`, yielding

$$Q_{a;b,p,k}(x)=R_{p,k,m}(x)
=c\frac{S_{m+1}(x)^2}{S_m(x)S_{m+2}(x)}.$$

`moment_gap_identity` applies the frozen
`D5.S3.QuantumBounds.LagrangeGramIdentity.lagrange_gram_identity` to square-root
weights. `strict_moment_gap` uses the distinct nodes $0,1$ to make the gap
strict. `ratio_bounds` gives $0<R(x)<c$. The normalized finite sums
$x^rS_r(x)$ tend to $1$ at $0^+$ and to $p+1$ at infinity;
`normalized_atZero`, `normalized_atTop` and `ratio_endpoints` establish
both limits of $R$ as $c$.

`ratio_neither_monotone` passes a proposed monotonicity inequality to the
appropriate endpoint and contradicts the strict interior deficit.
`family_failure` transfers both failures to $Q$. The public `result` uses
$p=k=1$, $m=2$, $l=1$ to contradict the monotonicity conjunct of `claim`.

## Falsifier

The refutation would fail if the tuples did not satisfy the source's strict
majorization, if cancellation used a zero derivative factor, or if an
endpoint limit or the strict moment gap failed in the positive source domain.
These are the obligations of `family_majorization`, `polygamma_ne_zero`,
`ratio_endpoints` and `strict_moment_gap`, respectively. The claim retains
the image assertion even though failure of its monotonicity conjunct suffices.

## Evidence

The Lean source and Scribe are
[the settling module](../D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.lean)
and [its Blueprint](../Blueprint/D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation.md).
The public mathematical theorem is `result`; all auxiliary proof lemmas are
private and used by the settlement. The frozen Gram owner supplies the
moment identity. The frozen
`D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing` owner supplies
`desc`, `moreMixed` and `prefixSum` for the tuple argument.

### Independent exact experiment

[Experiment directory at commit 940a20d75846863a2c001eaf34d76e26aa29d79e](https://github.com/the-omega-institute/trureturing-experiments/tree/940a20d75846863a2c001eaf34d76e26aa29d79e/docs/reports/yin-polygamma-majorization)
contains `check.py`. Its SHA-256 is
`44509fde783070626a9be66f9958e3cc4df4e79c45d12530c53a5c251b1e5be8`.
The immutable object was checked with `git cat-file -e` (exit 0).
Command: `git -C /Users/auric/trureturing-experiments show 940a20d75846863a2c001eaf34d76e26aa29d79e:docs/reports/yin-polygamma-majorization/check.py | python3`,
with pipeline failure checking enabled; exit 0, `ALL_CHECKS_OK`.
The experiment contains rational or symbolic checks, with no floating-point evidence.

The readings are $Q(1)=54/85$, $Q(2)=2450/3783$ and
$Q(2)-Q(1)=3968/321555>0$ for $p=k=1$, $a=(2,2,2)$, $b=(1,2,3)$;
24 derivative checks ($p=1,\ldots,4$, orders $1,\ldots,6$);
1,584 moment-gap checks ($p=1,\ldots,12$, $m=2,\ldots,12$,
$k\in\{1/3,1,3/2\}$, $x\in\{1/7,1,2,11\}$);
168 embeddings ($n=3,\ldots,8$, $m=2,\ldots,8$, $p=1,\ldots,4$, $k=1$, $x=2$);
and nine endpoint checks ($p=1,\ldots,3$, $k=1$, $m=2,\ldots,4$).
The experiment's $b=(1,2,3)$ permutes the family tuple $(1,3,2)$; products and descending rearrangements are unchanged.
Four symbolic truncation cases also check the logarithmic derivative of
source (1.4) against (1.5). The printed sign discrepancy is detected exactly
at $p=k=x=r=1$. This finite grid does not prove the general family.

## Triage

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Every $p\ge1,k>0,m\ge2$ and nominated length $n\ge3$: strict majorization does not imply either weak monotonicity; the family includes $n=2$. | Proved; kernel-checked. | `family_failure`, with $n=l+2$ for arbitrary natural $l$, and `orders_positive`. |
| The family quotient is positive, strictly below $m/(m+1)$, and has that limit at both $0^+$ and infinity. Finite-node dispersion causes the failure. | Proved; kernel-checked bounds and limits, with the stated substitution. | `ratio_bounds`, `strict_moment_gap`, `ratio_endpoints`; `Q_family` identifies $Q=R$ for $m\ge2$. |
| Positive derivative orders have no zero factors on $x>0$. | Proved; kernel-checked. | `polygamma_ne_zero` for every positive order, every natural truncation, $k>0$ and $x>0$; `Q_family` uses these denominators. |
| The exact witness, 24 derivative checks, 1,584 moment checks, 168 embeddings and nine endpoint checks. | Computed. | The independent exact experiment above, with its immutable program, command, exit code and SHA-256; only the specified finite scope. |
| Sharp interior minima, number/location of critical points and independent exact image classification. | Open. | No assertion in this delivery settles these questions. |
| Ordinary untruncated polygamma and the degenerate cases $p=0$ or $k=0$. | Open; outside this settlement. | The refuted source domain requires $p\ge1,k>0$ and finite truncation. |

### What the settlement shows

The decisive mechanism is a strict finite-moment gap together with equal
endpoint scaling, rather than a numerical anomaly. The surviving inequalities
$0<Q(x)<m/(m+1)$ and both endpoint limits hold for the entire embedded family.
The proof covers every length at least two, so it covers every nominated
length at least three. The exact interior minimum and image are open.

The argument is specific to finite truncation. The ordinary untruncated
polygamma series has different large-argument scaling; neither the ordinary
polygamma results of Qi nor those of Yang–Tian are refuted here. The same
neighboring-order family contradicts the finite-function monotonicity mechanism
used in the source's Theorem 1.1 and Section 4; those assertions are not premises
of this proof. Claims depending on that finite-function monotonicity require
independent justification. No classification of all other tuple pairs follows.

The literature screen recorded in #24132 found no inspected work settling
this exact finite-truncation conjecture. Qi–Agarwal's ordinary-polygamma survey,
Burić and Zhao–Wang's related work, and the Yang–Tian publisher abstract do not
supply a settlement in the inspected material. The full Yang–Tian body and
unretrieved citation and later-author records remain unverified.
Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature screen is not exhaustive; the unread Yang–Tian body and
unretrieved citation records remain outside the verified source set. No
worldwide novelty claim is made. The source's inconsistent signs are disclosed,
and the derivative convention is explicit. The escape audit of `result` remains
unfinished under issue #29215; the Lean proof does not supply a four-slot
registration or imply one is validated.
