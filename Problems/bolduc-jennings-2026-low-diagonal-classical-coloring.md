---
slug: bolduc-jennings-2026-low-diagonal-classical-coloring
bibkey: bolducjennings2026coloring
doi: 10.48550/arXiv.2611.19002
url: https://arxiv.org/html/2611.19002v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.result
---

# The low-diagonal classical value of complete-graph coloring

## Problem

William Bolduc and Michael Jennings, *Quantum Coloring Games on Complete Graphs*, arXiv:2611.19002v1, §5.1, first sentence, write:

> We have not yet found which quantum strategies are optimal for $p<\frac{2n-m}{(m+2)n-2m}$, nor have we found a closed form for the classical optimum when $p<\frac{2}{m+2}$.

The quotation transcribes the versioned author preprint under CC BY 4.0. [Source paragraph](https://arxiv.org/html/2611.19002v1#S5.SS1.p1.1) · [PDF p. 28](https://arxiv.org/pdf/2611.19002v1#page=28) · [Article rights](https://arxiv.org/abs/2611.19002v1)

The classical clause asks for the sharp value for every $n,m\in\mathbb N$ with $2\le m<n$ and every real $0<p<2/(m+2)$. The weighted input space is the set of **ordered** pairs $(x,y)\in\mathrm{Fin}(n)^2$. Each diagonal pair has weight $p/n$ and each off-diagonal pair has weight $(1-p)/(n(n-1))$. The outputs $A(x)$ and $C(y)$ belong to $\mathrm{Fin}(m)$. The winning predicate is $(x=y)\iff(A(x)=C(y))$. Shared and private randomness is independent of the referee input. Each full random tape yields a pair $(A,C)$ of local response tables, and its pushforward is a distribution on table pairs. Every such distribution can be realized by shared sampling.

## Motivation

The synchronous balanced strategy and the sufficient regime for its classical optimality are given in §§3.2–3.3. The search in §3.4 reduces the classical low-diagonal problem to finitely many candidate strategies. A two-score formula replaces this search with arithmetic in $n,m,p$ and gives a sharp classical benchmark for comparisons with quantum strategies. [Source §§3–4](https://arxiv.org/html/2611.19002v1#S3)

## Gap

The scoped literature check in the preregistration found the source's deterministic count identity, synchronous optimum, maximal agreement at fixed color marginals, and residual-support candidate search. The two-color case $p=1/n$ is covered by Cui, Mančinska, Nezhadi and Roberson, Theorem 5.5. The cited scope also covers the synchronous complete-graph and edge-supported cut formulations in Helton et al. The arXiv title and citation searches, indexed citation records, repository registry, pinned D5 and Mathlib, and sampled external Lean sources listed in the preregistration found no matching low-diagonal formula or proof. The check is bounded by the searched versions and indexing coverage. [Issue #33102](https://github.com/the-omega-institute/trureturing/issues/33102) · [Two-color uniform-input result](https://arxiv.org/abs/2502.05136v1) · [Synchronous and edge-supported results](https://arxiv.org/abs/2109.14741v2)

## Route

1. For every pair of deterministic tables let $\xi$ be the number of diagonal agreements and let $a_i,b_i$ be Alice's and Bob's color counts. The ordered collision count is $\mu=\sum_i a_i b_i$. The off-diagonal winning count is $n(n-1)-(\mu-\xi)$. Writing $t=p(n-1)/(1-p)$, $\lambda=1+t$, the probability is $1-p+((1-p)/(n(n-1)))(\lambda\xi-\mu)$. This gives the same objective as the weighted winning-indicator sum and uses the ordered input normalization.

2. Set $c_i=\min(a_i,b_i)$ and $k=n-\sum_i c_i$. The residual vectors $a_i-c_i$ and $b_i-c_i$ each sum to $k$ and have disjoint supports. Also $\xi\le\sum_i c_i$, with no synchronization hypothesis. When $k=0$, the balanced-square minimum gives the synchronous bound for all pairs with equal marginals. If $k>0$, choose a color of smallest $c_i$ on each positive residual support. The choices are distinct. With respective common counts $a,b$, the collision count is at least $\sum_i c_i^2+k(a+b)$.

3. Hold the other $m-2$ common counts fixed, with total $S$ and square sum $E$. Put $C=a+b$ and $R=n-S=C+k$. The score is at most $\lambda S-E+(\lambda-R)C+2ab$. For $H=\lfloor R/2\rfloor\lceil R/2\rceil$, parity gives $4H=R^2-(R\bmod2)$. Since $C<R$, the square of $a-b$ and $C\le R-1$ give $4Rab\le RC^2\le4CH$. The last two terms are bounded by $(C/R)(\lambda R-B_2(R))$, hence by $\max(0,\lambda R-B_2(R))$. At the first endpoint the other $m-2$ counts remain, with score at most $\lambda S-B_{m-2}(S)$. At the second endpoint complete the $m$ counts with $\lfloor R/2\rfloor,\lceil R/2\rceil$ to obtain the upper bound $\lambda n-B_m(n)$. The integer inequality includes $R=1$ and the endpoint argument uses $R>0$.

4. For $d>0$ and $s\ge0$, the minimum sum of squares of $d$ nonnegative integer parts of $s$ is $B_d(s)=dq^2+(2q+1)r$, with $q=s\operatorname{div}d$, $r=s\bmod d$. For an integer part $v$, $(v-q)(v-q-1)\ge0$ bounds the square from below. Equality is realized by $r$ parts of size $q+1$ and $d-r$ parts of size $q$. The difference of the common-block score between $s+1$ and $s$ is $t-2(s\operatorname{div}d)$. It is positive before $d\lceil t/2\rceil$ and nonpositive thereafter. For $d=0$, the feasible block is empty and $B_0(0)=0$.

5. Take one identical balanced table on both sides to attain the synchronous score. For the second score take identical balanced tables with colors $2,\ldots,m-1$ on the first $s_*$ inputs. On every remaining input Alice uses $0$ and Bob uses $1$. Thus the two reserved colors add no collision, and only the common block contributes agreements and collisions. A singleton distribution on a pair attaining the larger score gives the maximizing classical mixture. Every mixture is bounded by averaging the deterministic upper bound with nonnegative weights totaling one.

## Falsifier

A permitted deterministic table pair beating the proposed maximum would falsify the formula. A failure to realize either score would falsify the attainment conjunct. Fidelity also requires the full simplex, both orders of off-diagonal pairs, two local functions with arbitrary synchronicity and marginals, the stated strict bounds on $p$, and normalization. Swapping a total diagonal weight with a per-pair weight or using an edge-only coloring game would change the objective. Substituting a ceiling for the quotient in $B_d$ or dropping the feasible empty block would change the formula.

## Evidence

The source is `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.lean`. The declaration is `D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.result`. The versioned Library locator is `D5/L/Convexity/bolducjennings2026coloring`.

William Bolduc and Michael Jennings supplied the model, question and preceding results in §§1–3. The Codex CLI mathematics search supplies the formula and endpoint argument. The source and proof qualification supplies the boundary analysis and simplex formalization. The Lean proof contribution supplies the finite counting, both deterministic constructions and the full-interval proof. [Issue #33102](https://github.com/the-omega-institute/trureturing/issues/33102)

The Codex CLI Stage A integration supplies the canonical Lean placement, Blueprint, Library note, Reg registration and restoration materials. The focused prefreeze repair supplies the direct Mathlib applications, proof-shape accounting and source-provenance corrections.

## Triage

The classical question in §5.1 asks for a theorem over the full low-diagonal interval. [Source §5.1](https://arxiv.org/html/2611.19002v1#S5.SS1.p1.1)

### What the settlement shows

**Proved by the classical result.** For all $n,m\in\mathbb N$ and $p\in\mathbb R$ with $2\le m<n$ and $0<p<2/(m+2)$, set
$$
t=\frac{p(n-1)}{1-p},\qquad
\lambda=1+t,\qquad
d=m-2,\qquad
s_*=\min\{n,d\lceil t/2\rceil\}.
$$
For $k>0$, put $q=u\operatorname{div}k$, $r=u\bmod k$, and $B_k(u)=kq^2+(2q+1)r$, with $B_0(0)=0$. Define
$$
w_p(x,y)=
\begin{cases}
p/n & x=y,\\
(1-p)/(n(n-1)) & x\ne y.
\end{cases}
$$
Let $\mathcal T=(\mathrm{Fin}(n)\to\mathrm{Fin}(m))^2$. For each real standard-simplex distribution $\rho$ on $\mathcal T$, put
$$
W_p(\rho)=\sum_{(A,C)\in\mathcal T}\rho(A,C)
\sum_{(x,y)\in\mathrm{Fin}(n)^2}
\mathbf 1_{(x=y)\iff(A(x)=C(y))}\,w_p(x,y).
$$
The greatest element of $\{W_p(\rho):\rho\in\Delta_{\mathbb R}(\mathcal T)\}$ is
$$
1-p+\frac{1-p}{n(n-1)}
\max\!\left\{\lambda n-B_m(n),\ \lambda s_*-B_d(s_*)\right\}.
$$
There exist two deterministic table pairs whose respective scores
$$
\lambda\#\{x\in\mathrm{Fin}(n):A(x)=C(x)\}
-\#\{(x,y)\in\mathrm{Fin}(n)^2:A(x)=C(y)\}
$$
equal $\lambda n-B_m(n)$ and $\lambda s_*-B_d(s_*)$. Independently, $\sum_{(x,y)\in\mathrm{Fin}(n)^2}w_p(x,y)=1$. The proof is sharp by the explicit constructions. The two-color case has $d=s_*=0$. A cap $s_*=n$ leaves no reserved block. Both witnesses survive ties in the maximum. At integral $t/2$ the forward differences can vanish and the stated ceiling still gives a maximizing integer. [Lean result](../D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue.lean)

**Proved within the same derivation.** The bound applies to arbitrary nonsynchronous table pairs, including equal marginals, and to all input-independent mixtures. The source's finite classical search on this interval is therefore replaced by two explicit scores. A synchronous strategy is optimal exactly when the synchronous score is at least the common-block score. Equality permits a synchronous optimum. This gives the classical benchmark for the source's comparisons with quantum strategies. The low-diagonal quantum question, the structure of all quantum optimizers and a classification of every deterministic maximizing table pair remain open here.

**Argued tie structure.** For $d>0$ and integral $t/2=j$, the zero increments run from $dj$ through $d(j+1)-1$. If $n\ge dj$, all common-block sizes from $dj$ through $\min(n,d(j+1))$ give the same second score. If $n<dj$, the maximum is at the cap $n$. This describes ties within the common-block optimization and is distinct from equality of the two displayed scores.

**Argued extension.** The endpoint and balance inequalities use $t\ge0$ and the affine comparison uses $p<1$ with $n>1$. The same argument extends on paper to real $0\le p<1$ with the same size restrictions. The public Lean theorem uses the original strict interval. The source's high-diagonal synchronous-optimality theorem gives the independent boundary comparison at $p=2/(m+2)$. At $p=1$ the rescaling divides by $1-p$ and a direct game argument is required. A separately formalized extension and complete classifications of ties remain open here. [Source §3.3](https://arxiv.org/html/2611.19002v1#S3.SS3)

## ASSUMED-UNVERIFIED

The literature audit is bounded by the sources and indexes listed above. The ordinary random-tape interpretation of the simplex is the finite-game correspondence used in the source reading.
