---
bibkey: bolducjennings2026coloring
authors: William Bolduc, Michael Jennings
year: 2026
title: "Quantum Coloring Games on Complete Graphs"
doi: 10.48550/arXiv.2611.19002
url: https://arxiv.org/html/2611.19002v1
claim: "Section 5.1 asks for a closed form for the classical optimum of the weighted complete-graph coloring game when p < 2/(m+2)."
strata_touched:
  - D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue
license: CC-BY-4.0
triage: anchor
---

# Bolduc and Jennings on the classical complete-graph coloring value

## Verified locator

- Versioned HTML and registered DOI. https://arxiv.org/html/2611.19002v1 · https://doi.org/10.48550/arXiv.2611.19002
- Versioned author source and scope: [arXiv:2611.19002v1 §§1–2](https://arxiv.org/html/2611.19002v1#S1).
- The classical clause is in the first sentence of [§5.1, Open Problems](https://arxiv.org/html/2611.19002v1#S5.SS1.p1.1), [PDF p. 28](https://arxiv.org/pdf/2611.19002v1#page=28).
- The deterministic reductions and synchronous formula are in [§§3.1–3.3](https://arxiv.org/html/2611.19002v1#S3). Lemma 3.4.1 and the finite search over nonsynchronous candidates are in [§3.4](https://arxiv.org/html/2611.19002v1#S3.SS4).

## Classical value

For $2\le m<n$ and $0<p<2/(m+2)$, each ordered diagonal input has weight $p/n$ and each ordered off-diagonal input has weight $(1-p)/(n(n-1))$. The players win exactly when their answers have the same equality relation as their inputs. The classical winning probability is a linear functional on the simplex of input-independent mixtures of ordered pairs of local response tables. Its attainable values form the convex hull of the deterministic probabilities, and a simplex vertex attains its maximum.

Let $t=p(n-1)/(1-p)$, $\lambda=1+t$, $d=m-2$, and $s_*=\min(n,d\lceil t/2\rceil)$. Put $B_k(u)=k(u\operatorname{div}k)^2+(2(u\operatorname{div}k)+1)(u\bmod k)$ for $k>0$, and $B_0(0)=0$.

$$
1-p+\frac{1-p}{n(n-1)}
\max\{\lambda n-B_m(n),\,\lambda s_*-B_d(s_*)\}.
$$

The two scores are attained by a balanced synchronous pair and by a balanced common block with two reserved distinct colors, respectively. The second pair uses an empty common block at $m=2$. The referee weights sum to one.

## Mathematical attribution and license

William Bolduc and Michael Jennings supply the question, game model, collision-count reduction, balanced synchronous value and residual-color method in §§1–3.

The Codex CLI mathematics search supplies the closed form and parity-sensitive endpoint argument. The source and proof qualification supplies the fixed-marginal, equal-marginal and tie analyses and the simplex formalization. The Lean proof contribution supplies the finite counting, explicit table constructions and full-interval proof. [Issue #33102](https://github.com/the-omega-institute/trureturing/issues/33102)

The Codex CLI Stage A integration supplies the canonical Lean placement, Blueprint, Library note, Reg registration and restoration materials. The focused prefreeze repair supplies the direct Mathlib counting and arithmetic applications, proof-shape accounting and source-provenance corrections.

Cui, Mančinska, Nezhadi and Roberson give the prior uniform-input two-color case in [Theorem 5.5 of arXiv:2502.05136v1](https://arxiv.org/html/2502.05136v1#S5). It is a related exact case. The Lean proof uses Mathlib for finite sums, counting, ordered arithmetic, ceilings and the standard simplex.

The versioned arXiv HTML labels the author preprint “License: CC BY 4.0”. The versioned abstract record and DataCite v1 metadata both link the article's rights to Creative Commons Attribution 4.0 International. The formula and exposition above express the repository result. [HTML](https://arxiv.org/html/2611.19002v1) · [Abstract metadata](https://arxiv.org/abs/2611.19002v1) · [DataCite](https://api.datacite.org/dois/10.48550/arXiv.2611.19002) · [License](https://creativecommons.org/licenses/by/4.0/)
