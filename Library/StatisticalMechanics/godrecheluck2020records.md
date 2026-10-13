---
bibkey: godrecheluck2020records
authors: C. Godrèche and J.-M. Luck
year: 2020
title: "Records for the moving average of a time series"
doi: 10.1088/1742-5468/ab5d08
url: https://arxiv.org/abs/1907.07598
claim: "Finally, the data shown in figure 1 suggest that (6.33) provides an absolute upper bound for $Q_n$."
strata_touched:
  - D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1742-5468/ab5d08

Source: https://arxiv.org/abs/1907.07598

The source is arXiv:1907.07598v2, *Journal of Statistical Mechanics:
Theory and Experiment* (2020) 023201. Page numbers refer to the 39-page
arXiv v2 PDF, https://arxiv.org/pdf/1907.07598v2.

Section 1, p. 2:

> In the present work we investigate the statistics of records for sequences made of
> sums of p successive iid positive random variables, defined as follows. For p = 2,

Equation (1.4):

\[
Y_2=X_1+X_2,\quad Y_3=X_2+X_3,\dots,\quad Y_n=X_{n-1}+X_n,\ \dots.
\]

Equation (1.7), p. 2, is $Q_n=\mathrm{Prob}(Y_n>L_{n-1})$.
Equation (1.8), p. 3, defines $L_n=\max(Y_1,Y_2,\dots,Y_n)$.
The accompanying sentence on p. 3 is:

> where records are counted from the first complete sum Y₂ onwards.

Thus the record event used here is
$Q_n=\Pr(Y_n>\max(Y_2,\dots,Y_{n-1}))$.
The factor $1/2$ in the moving average does not change this strict comparison.

Section 6.6, equation (6.33), p. 30, gives $Q_n=3/(2n)$ for $n\ge3$
in the exponentially broad limit. Immediately afterward, on p. 31:

> Finally, the data shown in figure 1 suggest that (6.33) provides an absolute upper bound for $Q_n$.

The density statement uses independent real coordinates of common law
$\mu=\mathrm{volume}.\mathrm{withDensity}(x\mapsto\mathrm{ENNReal.ofReal}(f(x)))$,
where $f$ is continuous and nonnegative, $\mu$ is a probability measure, and
$\mu(({-\infty},0])=0$. Coordinate $x_i$ is the source's $X_{i+1}$:
indices $1\le i$ and $i+2\le n$ compare $Y_{i+1}$ with $Y_n$.
The repository-derived bound applies more generally to every atomless
probability measure on the real line, without positivity or continuity.

The arXiv v2 text and PDF agree on the quoted upper-bound sentence.
The corresponding typeset journal wording is ASSUMED-UNVERIFIED.
