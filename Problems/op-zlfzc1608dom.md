---
slug: op-zlfzc1608dom
bibkey: zoroa2017couponcollector
doi: 10.1098/rsif.2016.0643
url: https://arxiv.org/abs/1608.00155v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Probability/StrongDominanceRefutation.result
---

# Strong dominance in unequal-probability coupon collection

## Problem

Zoroa, Lesigne, Fernández-Sáez, Zoroa and Casas conjecture that if $p\prec q$, the number $Y_n$ of distinct labels seen in $n$ independent draws under $p$ strongly stochastically dominates $Y_n$ under $q$. The conjecture follows Definition 8.2 on p. 30 of [arXiv:1608.00155v1](https://arxiv.org/abs/1608.00155v1) and Definition 7.2 of the [published paper](https://doi.org/10.1098/rsif.2016.0643). Issue [#28951](https://github.com/the-omega-institute/trureturing/issues/28951) gives the verbatim source clauses and model conventions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $N$ labels and $n$ independent draws | Positive natural binders $N,n$ in `claim`, indexed by `Fin N` and `Fin n` | The explicit positivity guards record the source populations and draw counts. Zero-based labels only rename the source labels. |
| Fixed nonnegative coordinate probabilities of total one | $p,q$ range over `Convexity.StdSimplex` on real weights indexed by `Fin N` | Includes zero coordinates. |
| A cylinder has the product of its coordinate probabilities | The product within `distinctCountPMF` | Length-$n$ words partition the histories into cylinders. The finite marginal therefore gives their exact probability sum. |
| $Y_n=k$ means that exactly $k$ different labels occur | The image-cardinality filter within `distinctCountPMF` | The definition sums precisely the cylinders in this event and assigns zero to all other words. |
| $p\prec q$ in Definition 6.1 | `moreMixed` applied to the weight vectors | Decreasing rearrangement, inequalities for proper prefixes, and equal totals. The extra empty prefix contributes $0\leq 0$. |
| A real threshold with lower comparison at $k\leq c$ and reversed comparison at $k>c$ | `StronglyDominates` | The paper's countable value set is instantiated with natural counts embedded in the reals. Outside the support both probabilities are zero. The lower side includes equality with $c$. |
| Universal implication in the direction from $p$ majorized by $q$ to dominance under $p$ | `claim`, negated by `result` | The counterexample is an instance in the full source domain. |

## Motivation

Majorization gives an ordinary cumulative-distribution comparison in the paper. A single threshold for the mass functions would additionally constrain how mass changes at individual occupancy levels.

## Gap

The published article retains the conjecture and reports proofs for $n=2,3$ and for $n=4$ with $N\leq5$. The source and literature screen on [#28951](https://github.com/the-omega-institute/trureturing/issues/28951) identified no settlement in the material examined. The relevant comparisons found concern ordinary tail order or waiting-time laws.

## Route

Take $N=4$, $n=5$, $p=(48,48,2,2)/100$ and $q=(50,46,3,1)/100$. The decreasing prefix numerators are $(48,96,98,100)$ and $(50,96,99,100)$. The proof reduces the cylinder sums to integer word-weight sums over $4^5$ words and divides by $100^5$. At $k=2$ the mass under $p$ is strictly larger, forcing $c<2$. At $k=3$ the mass under $p$ is strictly smaller, requiring $3\leq c$. These inequalities exclude every real threshold.

## Falsifier

The witness would fail if its weights were invalid, if its ordered prefixes failed the majorization test, or if its strict comparisons at $2$ and $3$ had different signs. The settling proof checks the witness and derives the incompatible threshold conditions from Definition 8.2.

## Evidence

`D5.S3.Analytic.Probability.StrongDominanceRefutation.result` refutes the closed proposition `claim`. The module has generality `I` and admission basis `open-problem-resolution (#28951; Refuted)`. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact checker is available at [trureturing-experiments, pinned checker directory](https://github.com/the-omega-institute/trureturing-experiments/tree/0e0d1900830295271d2dfbf86b8e53f9c2c69cb0/docs/reports/1608.00155-strong-dominance/). After extracting `docs/reports/1608.00155-strong-dominance/check.py` from that revision, run `python3 check.py`. The command exited 0 with `ALL_CHECKS_OK`. Script SHA-256 is `f3f435168370f9ff71553778cf56a166d7852ec33bd352275391563e90ee0c53`.

The checker exhausts all 1,024 words for each concrete witness vector and compares exact polynomial coefficients and rational enclosures for the family at $N=4,n=5$. Its separate fidelity computations cover 600 cases with $1\leq N\leq4$, $1\leq n\leq5$ and weights with denominator $6$, and 12,012 majorized ordered pairs with $N=4$, $n=2,3,4$ and weights with denominator $6$.

## Triage

### What the settlement shows

1. **Proved.** The exact universal one-threshold conjecture is false at $N=4,n=5$. The kernel-checked declaration is `D5.S3.Analytic.Probability.StrongDominanceRefutation.result`.
2. **Computed.** Both four-coordinate witness vectors have strictly positive weights. This witness also refutes the conjecture on the positive-risk domain. Evidence is the exact check of the concrete vectors and the positive parameter family in the pinned checker.
3. **Computed.** Averaging the two common coordinates of $q$ gives numerators $(48,48)$, and averaging its rare coordinates gives $(2,2)$. The witness mass differences at $k=1,2,3,4$ have numerators $(-8855220,1524660,-6565440,13896000)$ over $100^5$. Evidence is exact arithmetic on the vectors and word enumeration in the pinned checker. The resulting signs $(-,+,-,+)$ show how mass shifts across occupancy levels under the two averages.
4. **Computed.** Proper cumulative-difference numerators are $(-8855220,-7330560,-13896000)$ with denominator $100^5$, and the full difference is zero. The pinned checker verifies that the concrete witness respects ordinary stochastic dominance. The paper's ordinary order follows from its independent majorization argument in §6 and remains applicable. The refutation removes the general one-threshold strengthening.
5. **Computed.** At $N=4,n=5$, the family $p_t=(1/2-2t,1/2-2t,2t,2t)$ and $q_t=(1/2,1/2-4t,3t,t)$ is positive, normalized and majorized and has PMF difference signs $(-,+,-,+)$ throughout the real interval $0<t\leq1/100$. Evidence is coefficient-by-coefficient polynomial equality and exact rational sign bounds in the pinned checker. Extensions to other dimensions, draw counts, or parameter intervals are open here.
6. **Open.** A classification of pairs, or additional hypotheses that guarantee a single crossing, remains open in this dossier. The paper's stated cases $n=2,3$ and $n=4,N\leq5$ lie outside the $n=5$ witness. Their status here is based on the paper's stated progress and the bounded fidelity computation in Evidence.

## ASSUMED-UNVERIFIED

Literature completeness and priority are unverified. The exact-target screen in #28951 records the checked material and the unavailable texts, including the full Wong–Yue 1973 result and several subscription articles.
