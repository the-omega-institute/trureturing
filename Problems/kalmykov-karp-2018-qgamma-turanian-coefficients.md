---
slug: kalmykov-karp-2018-qgamma-turanian-coefficients
bibkey: kalmykovkarp2018qgamma
doi: 10.1016/j.jmaa.2017.11.041
triage: theorem
motivation_gids:
  - D5/S3/Analytic/QGammaTuran/Result.result
url: https://arxiv.org/abs/1702.03788
---

# Refutation of reciprocal q-gamma coefficient positivity

## Problem

S. I. Kalmykov and D. B. Karp, *Inequalities for series in q-shifted
factorials and q-gamma functions*, J. Math. Anal. Appl. 460 (2018),
332–351, DOI 10.1016/j.jmaa.2017.11.041, arXiv:1702.03788v1,
Conjecture 1, printed p. 12:

> All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.

Theorem 3, printed p. 11:

> For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define
>
> $g(\mu;x)=\displaystyle\sum_{n=0}^{\infty}\frac{g_nx^n}{\Gamma_q(\mu+n)}.$ (16)
>
> Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian
>
> $\Delta_g(\alpha,\beta;x)=g(\mu+\alpha;x)g(\mu+\beta;x)-g(\mu;x)g(\mu+\alpha+\beta;x)$
>
> is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then Δg(α, β; x) has positive power series coefficients at all powers of x.

The sequence is nontrivial, nonnegative, log-concave and has no
internal zeros, the definition of doubly positive on printed p. 3.
Equation (6), printed p. 4, defines

$$\Gamma_q(z)=(1-q)^{1-z}\frac{(q;q)_\infty}{(q^z;q)_\infty}.$$

Its reciprocal is extended by zero at the poles $z\in-\mathbb N_0$.
Only the coefficient-positivity conclusion is refuted here.

### Formal reading

The new Lean names have prefix `D5.S3.Analytic.QGammaTuran.Result`.

| Source object | Lean name | Correspondence |
| --- | --- | --- |
| Reciprocal of (6) | `rqgamma` | Real infinite-product quotient, extended by zero at nonpositive integers. |
| Doubly positive sequence | `D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq` | Existing nontriviality, nonnegativity, log-concavity and no-internal-zero hypotheses. |
| Degree $m$ coefficient | `qturanCoeff` | Exact finite Cauchy sum over $0\le k\le m$. |
| Coefficient clause of Conjecture 1 | `claim` | Every $0<q<1$, admissible sequence, permitted real shifts and natural degree. |
| Refutation | `result` | Exactly $\neg\,\texttt{claim}$. |

## Motivation

The settling declaration is `D5/S3/Analytic/QGammaTuran/Result.result`.
The source note is `D5/L/Asymptotics/kalmykovkarp2018qgamma`.
The unit sequence meets the sequence hypotheses. The boundary triple
$(-t,t,t)$ is permitted by the conjectured coefficient clause and
exposes the same cancellation pattern as in the classical reciprocal
Gamma problem.

## Gap

Status: **Refuted** for the coefficient clause. The witness is
$g_n=1$, $q=(99/100)^{10}$, $\mu=-7/10$,
$\alpha=\beta=7/10$, $m=2$. Its shifts satisfy
$\mu=\max(-\beta,-1)$ and $\alpha\le\beta+1$.
Theorem 3 itself concerns integral $\alpha$; the witness has
$\alpha=7/10$, so it does not contradict that theorem.
Function positivity and parameter log-concavity remain unaddressed.

## Route

Write $R_q(x)=1/\Gamma_q(x)$ and
$[x]_q=(1-q^x)/(1-q)$. The product definition yields
$R_q(x)=[x]_qR_q(x+1)$, $R_q(0)=0$ and $R_q(1)=1$.
At $t=7/10$, the degree-two Cauchy sum reduces to

$$\delta_2=1-PC,\qquad P=R_q(3/10)R_q(7/10),$$

$$C=\frac{[-7/10]_q}{[7/10]_q[17/10]_q}
+\frac1{[7/10]_q}+\frac1{[3/10]_q}.$$

For $r=99/100$ and $q=r^{10}$, every bracket appearing here is
rational because $q^{n/10}=r^n$. The complementary exponents in $P$
give

$$P=\frac{(r^3;q)_\infty(r^7;q)_\infty}
{(q;q)_\infty^2(1-q)}.$$

For $0\le a<1$, a partial product bounds $(a;q)_\infty$ from above.
Its lower bound is the partial product multiplied by
$1-aq^N/(1-q)$, using

$$\prod_{j\ge N}(1-aq^j)\ge1-\frac{aq^N}{1-q}.$$

These bounds convert $PC>1$ to a finite rational comparison and yield
$\delta_2<0$.

## Falsifier

One permitted sequence and parameter choice with a nonpositive
coefficient contradicts the universal strict-positivity clause.
The displayed unit-sequence witness has a negative second coefficient.
An error in the Cauchy reduction, the product-tail bound or its rational
comparison would invalidate this argument without establishing the
coefficient clause.

## Evidence

`D5/S3/Analytic/QGammaTuran/Result.result` has the type
`result : ¬ claim`, with no additional hypotheses.
The sequence hypothesis is supplied by the existing
`D5.S3.Analytic.ReciprocalGammaTuran.Defs.admissible_one`.

The experiments are available at the immutable
[q-gamma experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/16625fed7a778151de7c1bb6a86ecd47a7ada60c/experiments/kalmykov-karp-qgamma-turanian).
The following readings concern the scripts at that revision.

- **COMPUTED.** Command:
  `python3 /Users/macstudio/omega-op/s3688/kk-qgamma-cert.py`;
  exit code 0; script `kk-qgamma-cert.py`, SHA-256
  `a0b18ca90e4bfd31b2c5d3871f53212c3b53c9e66cbb3be2d04042ce85065f85`.
  The script uses 800 product factors with outward rounding to multiples
  of $2^{-200}$ and the geometric tail bound. Its exact rational checks
  are $C>0$ and $P_{\rm lower}C>1064/1000$, hence $PC>1064/1000$.
  Its printed value for $1-P_{\rm lower}C$,
  approximately $-0.06428299060000457$, is a floating approximation;
  the asserted rational inequalities are exact.
- **COMPUTED.** Command:
  `python3 /Users/macstudio/omega-op/s3688/kk-qgamma-scan.py`;
  exit code 0; script `kk-qgamma-scan.py`, SHA-256
  `e1dcb5bf944905427dbdf16ea8b07267d074c4628cd75cbe14f421619c3b15c0`.
  This finite scan uses 30 decimal digits and truncated products, with
  $q\in\{0.5,0.9,0.97\}$, $t=k/20$ for $1\le k\le19$,
  $\alpha=\beta=t$, $\mu\in\{-t,-t+0.05,0,0.5\}$,
  retaining $\mu\ge\max(-t,-1)$, and degrees zero through four.
  It finds negative coefficients for $q=0.9$ and $q=0.97$ and none
  for $q=0.5$. The respective minimum values are approximately
  $-0.0636984$, $-0.07192$ and $0.000120102$; the negative minima
  occur at $(t,\mu,m)=(0.7,-0.7,2)$ and the positive minimum at
  $(0.05,-0.05,4)$. These are finite numerical observations.

The supplied literature scope comprises the cited-by works recorded for
OpenAlex W2603745271: arXiv:1808.05105 cites the source but supplies no
settlement of Conjecture 1; the 2019 journal version adds no settlement
in that scope; DOI 10.1142/s1793042120400187 treats a different
q-binomial question. The classical reciprocal Gamma refutation,
arXiv:2607.02511 and the Zenodo preprint on failure of parameter
log-concavity concern $q=1$. No settlement was found in the supplied
Formal Conjectures and conjectures.io scope. This bounded search does
not establish exhaustive coverage or priority.

## Triage

### What the settlement shows

- **PROVED.** The universal coefficient clause is false:
  `D5.S3.Analytic.QGammaTuran.Result.result`.
  The witness uses the boundary cancellation at $(-t,t,t)$, $t=7/10$,
  and $q=(99/100)^{10}$. Thus the boundary failure seen in the
  classical $q=1$ problem persists at this $q$ close to one.
- **COMPUTED.** At this witness the exact rational certificate gives
  $PC>1064/1000$, as checked by `kk-qgamma-cert.py` with the command,
  exit code and SHA-256 in Evidence. The approximate printed bound is
  separate from the exact comparison.
- **COMPUTED.** The finite scan in Evidence finds no negative
  coefficient at $q=0.5$ through degree four on its stated grid.
- **OPEN.** The dependence of coefficient positivity on $q$, including
  any uniform interval near $q=1$ or a positive result at $q=0.5$,
  is not settled by this witness or finite scan.
- **OPEN.** The function-positivity and parameter log-concavity clauses
  of Conjecture 1 are not addressed. A negative coefficient alone
  does not establish failure of function positivity.
- **OPEN.** The remaining conjectural extensions, and any results
  requiring them, receive no conclusion from this coefficient
  counterexample. The integral-shift assertion of Theorem 3 is outside
  the witness's parameter choice.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, citation-index completeness and priority
are unverified. The bounded literature scope is supplied bibliographic
evidence; no current network search is asserted. The scan's truncated
product values are numerical observations, not rigorous signs on a
continuous parameter range. Its absence of negative values at
$q=0.5$ does not prove coefficient positivity there.
