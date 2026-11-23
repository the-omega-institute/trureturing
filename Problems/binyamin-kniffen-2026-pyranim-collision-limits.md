---
slug: binyamin-kniffen-2026-pyranim-collision-limits
bibkey: binyaminkniffen2026pyranim
doi: null
url: https://arxiv.org/abs/2611.16153v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Games/PyranimCollisionLimits.result
---

# The Pyranim isomorphism probability decays subexponentially

## Problem

Binyamin and Kniffen ask whether the nth root of the probability of isomorphism tends to one and ask about subexponential decay. Section 5.3 item 4 states the root limit for two randomly selected elements of the stable-position set at width $n$. [Versioned source](https://arxiv.org/html/2611.16153v1#S5.Ex4) [Preregistration](https://github.com/the-omega-institute/trureturing/issues/33556)

Take $X$ and $Y$ to be independent uniform draws with replacement from the entire set $mathcal T_n$ of stable positions of width $n$. Write $p_n=\Pr(X\simeq Y)$, and write $p'_n$ for the same event under uniform sampling of distinct ordered pairs, equivalently conditioned on $X\ne Y$ for $n\ge1$. Then
\[
\lim_{n\to\infty} p_n^{1/n}=1,\quad
\lim_{n\to\infty} p_n=0,\quad
\lim_{n\to\infty} (p'_n)^{1/n}=1,\quad
\lim_{n\to\infty} p'_n=0 .
\]
All limits are over the natural widths, so the root and distinct-pair limits use every positive width in their tails.

## Motivation

The Catalan number $C_{n+1}$ counts literal stable positions. Their game isomorphism classes can have unequal sizes. Collision probability weights each class by the square of its size and tests how much of the population is concentrated in large classes. [Stable-position count](https://arxiv.org/html/2611.16153v1#S2.Thmthm2)

## Gap

The root limit requires enough collisions at all large widths. The zero limit requires control of the class sizes relative to the whole population. These are separate inequalities.

The precise model follows Definitions 1.1–1.3. A chip is a nonempty interval $[i,j]$ of $[n]$ and a stable position is a lower set for inclusion. A visible chip lies in the position with at most one of its two possible immediate upper chips present. The legal successor is the stable result of deleting that chip and its upward support cascade. Game isomorphism requires a bijection of actual legal successor positions that recursively matches game-isomorphic successors. The empty board and boards with missing bottom chips are part of the population. [Definitions 1.1–1.3](https://arxiv.org/html/2611.16153v1#S1) [Lemma 3.1](https://arxiv.org/html/2611.16153v1#S3.Thmthm1)

## Route

**Root limit.** Fix a block width $b+2$. Divide width $n$ into $q=\lfloor n/(b+2)\rfloor$ full blocks and the remaining columns. Leave the remainder empty and include all singleton and length-two intervals within each full block. Deleting two filled rows reduces the choice in each full block to an arbitrary stable position of width $b$. There are $T=C_{b+1}$ choices. No chip crosses between blocks. Equal multiplicity vectors are realized by permuting the full blocks, which gives an order isomorphism of the chip sets. The order isomorphism respects visibility and transports legal options at each descendant. There are at most $(q+1)^T$ multiplicity vectors and $T^q$ boards, so a class has at least $T^q/(q+1)^T$ members. With $N=C_{n+1}$, this gives $p_n\ge (T^q/((q+1)^TN))^2$. For fixed $b$ the lower bound using the Catalan exponential upper bound has root limit $(T^{1/(b+2)}/4)^2$. The latter tends to one as $b$ increases. The upper bound is one.

**Zero limit.** Game isomorphism preserves lengths of complete legal paths. The maximum such length is the chip count, attained by successively removing maximal chips one at a time. Encode a width-$n$ ideal by its column thresholds, then by the frozen inversion-sequence equivalence to Dyck words of semilength $n+1$. Fix $L\ge0$, put $M=2(L+1)$, and write $2(n+1)=Mq+r$ with $0\le r<M$. Mark slots containing one of the $L+1$ specified balanced Dyck blocks. Replacing the first marked block among those $L+1$ choices produces strictly ordered chip counts and preserves the first marked slot. From any fixed-rank marked fiber the resulting replacement map is injective. The unmarked words are bounded by $(2^M-1)^q2^r$. Hence for each position its class has size at most
\[
\frac{N}{L+1}+(2^M-1)^q2^r.
\]
Summing over first draws and dividing by $N^2$ bounds $p_n$ by $1/(L+1)$ plus the unmarked count divided by $N$. At fixed $L$ this ratio tends to zero by a central binomial lower bound for $N$ and a geometric loss per slot. Taking $L$ arbitrarily large proves the zero limit.

**Distinct pairs.** There are $N$ diagonal ordered pairs and every diagonal pair is a collision. For $N>1$ the probability for distinct ordered pairs is $(Np_n-1)/(N-1)$, at most $p_n$. The independent root limit and exponential growth of $N$ give $p_n\ge2/N$ eventually, so $p'_n\ge p_n/2$ eventually and the distinct-pair root tends to one.

## Falsifier

A failure of either limit means a fixed positive tolerance and arbitrarily large positive widths violating it. In particular, a positive lower bound for the probability along an unbounded subsequence would contradict decay, and a fixed root deficit along an unbounded subsequence would contradict the all-width lower bound.

## Evidence

`D5/S3/Combinatorics/Games/PyranimCollisionLimits.result` gives the four limits. The exact class estimate is `PyranimCollisionLimits.gameIso_class_card_upper`. `PyranimCollisionRoot.distinctCollisionProbability_eq` gives the diagonal correction. `PyranimPosition.stableCard` and `PyranimPosition.stableEquivDyck` identify the population, using `InversionSeq152Dyck.monoDyckEquiv` and the Mathlib Dyck-word count. The probability definitions are exact finite-cardinality ratios. At width zero their real division and power expressions are totalized, which is outside the positive-width sampling interpretation of the distinct-pair and root expressions.

The escape audit is unfinished under [issue #33619](https://github.com/the-omega-institute/trureturing/issues/33619).

## Triage

- **Proved in Lean.** The nth-root and zero limits hold for independent draws and also for uniformly sampled distinct pairs.
- **Proved in Lean.** A uniform class-size bound gives decay by chip-count invariance and the marked-block injection.
- **Open within this dossier’s formal scope.** The full reverse component classification, a sharp rate or asymptotic equivalent for the collision probability, and the random-start expectation in item 4.

## ASSUMED-UNVERIFIED

The probability uses the independent uniform interpretation fixed in the preregistration. The scoped literature search recorded there found no earlier settlement of these limits. Priority beyond that search is unverified.
