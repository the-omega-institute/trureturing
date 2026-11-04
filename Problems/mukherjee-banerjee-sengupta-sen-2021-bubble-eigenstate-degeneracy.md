---
slug: mukherjee-banerjee-sengupta-sen-2021-bubble-eigenstate-degeneracy
bibkey: mukherjeebanerjeesenguptasen2021fragmentation
doi: 10.1103/PhysRevB.104.155117
url: https://arxiv.org/abs/2106.14897v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.result
---

# A closed formula for the bubble-eigenstate configuration count

## Problem

B. Mukherjee, D. Banerjee, K. Sengupta and A. Sen, *Minimal model for Hilbert space fragmentation with local constraints* (Phys. Rev. B 104, 155117, 2021; arXiv:2106.14897v3), section “Construction of bubble eigenstates”, TeX `fragmentation_prb_v2.tex`, lines 729–731, immediately following Table I:

> While we have not been able to find a closed form expression for the degeneracy of the different bubble eigenstates for an arbitrary $L$, we can still place a lower bound on the degeneracy of such states when $L \gg 1$.

The counting prescription is explicit in the same source, lines 670–674:

> The number of bubble eigenstates at an integer energy $E=n_1-n_2$ can be calculated for a given system size from the number of configurations that satisfy the hard core constraint of at least two consecutive $\downarrow$ spins separating any of the $n_1$ $X$ and $n_2$ $Y$ units on the periodic one-dimensional lattice.

Here $X$ and $Y$ are three-site units with energies $+1$ and $-1$, respectively (the source's construction, lines 634–647). Issue [#26367](https://github.com/the-omega-institute/trureturing/issues/26367) fixes the combinatorial reading: sites are $\mathrm{Fin}\,L$, a centre set $B$ is admissible when every ordered pair of distinct centres has clockwise separation at least five, and a subset $x\subseteq B$ specifies the $X$ labels, with the other centres labelled $Y$. Its energy is $2|x|-|B|$. Translations are counted separately, and the empty placement contributes one configuration at energy zero. Let $D_B(L,E)$ denote this count, defined by `bubbleCount`.

For $1\le n\le\lfloor L/5\rfloor$, write

$$C(L,n)=\left(L\binom{L-4n-1}{n-1}\right)\mathbin{\mathrm{div}}n,$$

where $\mathrm{div}$ is natural-number division, and put

$$A(n,E)=\begin{cases}\displaystyle\binom{n}{(n+E)/2},&n+E\text{ is even and }|E|\le n,\\0,&\text{otherwise}.\end{cases}$$

The module proves `claim`: for every natural $L\ge5$ and every integer $E$,

$$D_B(L,E)=[E=0]+\sum_{n=1}^{\lfloor L/5\rfloor}C(L,n)A(n,E).$$

Here $[E=0]$ is one when $E=0$ and zero otherwise; the equality is evaluated in the integers by casting the natural count and placement coefficients. The guarded index $(n+E)/2$ is a nonnegative integer. This settles the stated closed-form gap for labelled configurations; identifying these configurations with eigenstates of $H_3$ uses the source's construction and is not part of the Lean theorem.

## Motivation

An energy-resolved count quantifies the explicitly constructed bubble sector and distinguishes its contribution from the full integer-energy spectrum. Table I provides finite-size counts, while the source uses a fully packed subfamily for a large-size lower bound. An exact expression for the whole configuration count gives finite-size values without enumerating centre sets or diagonalizing the Hamiltonian.

## Gap

Issue #26367 records the bounded literature check:

- The v3 source explicitly acknowledges the closed-form gap; the quoted passage and counting prescription are present in the TeX source.
- The search-seat report used INSPIRE record 1872920, listing 66 citing records, and screened the eleven arXiv works named in the issue; it reported no closed form in those screened works.
- The preregistration reports no existing repository dossier, Library note or issue naming this source in its recorded searches.

`not-found-in-searched-scope`.

The preregistration and [Library note](../Library/StatisticalMechanics/mukherjeebanerjeesenguptasen2021fragmentation.md) credit classical cyclic-placement counting as the ingredient; no novelty is claimed for that ingredient. The citing-work readings and repository-search results above are reports from #26367, not independently reproduced literature findings.

## Route

Write $c(L,n)$ for the number of admissible $n$-element centre sets, represented by the private `placements L n`.

1. **Packing.** For every natural $L\ge5$ and every admissible $B\subseteq\mathrm{Fin}\,L$, `packing_bound` proves $5|B|\le L$. The proof injects $B\times\mathrm{Fin}\,5$ into the cycle by adding the offset modulo $L$; both directed separation inequalities exclude collisions between different centres.
2. **Marked gaps.** For natural $L,n$ with $L\ge5$, $n\ge1$ and $5n\le L$, `marked_gap_equiv` gives a bijection between admissible $n$-centre sets with a marked centre and $\mathrm{Fin}\,L\times\mathrm{PositiveLengths}(L-4n,n)$. The latter consists of a site and an indexed vector of $n$ positive integers summing to $L-4n$. Clockwise gaps $g_i\ge5$ become positive parts $g_i-4$, and cumulative sums reconstruct the centres from the marked site. For $n=1$ the sole gap is $L$, so the hypothesis $L\ge5$ also covers that case. The reused `MiuraRunCompositions.positive_lengths_card` requires $n\ge1$ and $n\le L-4n$, both available here, and counts these vectors by $\binom{L-4n-1}{n-1}$.
3. **Exact division.** For natural $L,n$ with $L\ge5$, $n\ge1$ and $5n\le L$, `marked_count` proves $n\,c(L,n)=L\binom{L-4n-1}{n-1}$, and `placement_count` proves both $c(L,n)=C(L,n)$ and $n\mid L\binom{L-4n-1}{n-1}$. Thus the natural division in the formula is exact on its summation range.
4. **Labels and vacuum.** For every natural $L$, every $B\subseteq\mathrm{Fin}\,L$ and every integer $E$, without an admissibility hypothesis, `label_count` counts subsets $x\subseteq B$ of energy $2|x|-|B|=E$ by $A(|B|,E)$. For every natural $L$ and integer $E$, `vacuum_count` proves that the size-zero contribution is $[E=0]$.
5. **Sum.** For every natural $L\ge5$ and integer $E$, `sum_by_size` groups `bubbleCount` by $|B|$ and gives the vacuum term plus $\sum_{n=1}^{\lfloor L/5\rfloor}c(L,n)A(n,E)$. `result` casts that equality into the integers and substitutes `placement_count` for each $n\ge1$ with $5n\le L$.

## Falsifier

A count with a different exclusion distance, a quotient by translations, or a different energy assignment would not answer the registered question. `Admissible` imposes separation in both directions for every distinct pair, and `bubbleCount` counts subsets of the actual centre set by the integer energy $2|x|-|B|$. The parity and absolute-value conditions in `claim` exclude invalid binomial indices, including for negative energies.

The theorem assumes $L\ge5$. `Admissible` imposes no self-separation condition on a singleton, so extending this particular formula to smaller positive lengths would omit valid single-centre configurations. The theorem does not encode a Hilbert space, a Hamiltonian or the eigenstate correspondence, and it makes no statement about non-bubble eigenstates or open boundary conditions.

## Evidence

The canonical source is `D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.lean.json`.

Declaration statements:

- `result`: `sha256:d2bcfad81c77f1961d684a2700f45cee6cec77f91dac27c8b8e6a2ed545d46b1`;
- `claim`: `sha256:11c7cb479f23adb2e1794615a1deda2dc069fa7b2260c3e6946645b5b472985e`.

## Triage

Tier 1 explicitly acknowledged gap of a 2021 paper, preregistered in issue #26367 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $L\ge5$ and integer $E$, the integer cast of the number of admissible centre sets with an $X$-labelled subset of energy $E$ equals the vacuum term plus $\sum_{n=1}^{\lfloor L/5\rfloor}C(L,n)A(n,E)$, with natural-number division in $C$ and the parity and energy-range guards in $A$ as defined above.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism and extension.* Marking a centre removes the ambiguity of where to start reading cyclic gaps without assuming that translation orbits have full size; every $n$-element set has exactly $n$ marked versions. For an integer exclusion distance $d\ge1$, a cycle length $L\ge d$ and $1\le n\le\lfloor L/d\rfloor$, the same construction subtracts $d-1$ from each gap and identifies marked sets with a site and a positive composition of $L-(d-1)n$. Counting these pairs and dividing by $n$ gives $\frac Ln\binom{L-(d-1)n-1}{n-1}$ centre sets. This extension to variable $d$ is not a statement of the module's distance-five `marked_gap_equiv`.
- *Sharp packing.* For $L=5q$ with integer $q\ge1$, `packing_bound` applies to every admissible centre set since $L\ge5$, and gives $|B|\le q$. At energy $E=\pm q$, the identity $E=2|x|-|B|$ forces $|B|=q$ and all labels to have the same sign. All $q$ cyclic gaps must then be five, leaving exactly the five residue-class centre sets, so the configuration count at each of these two energies is five. These endpoint evaluations are consequences argued here, not additional compiled declarations.
- *Energy symmetry.* For any natural $L$ and integer $E$, replacing $x\subseteq B$ by $B\setminus x$ preserves the centre set, reverses $2|x|-|B|$, and is its own inverse; hence the configuration counts at $E$ and $-E$ agree without requiring a spectral argument.
- *Small-length boundary.* For $1\le L\le4$, any directed distance between distinct sites is at most $L-1<5$, so the only admissible sets are empty or singletons. Their labellings give one configuration at $E=0$ and $L$ configurations at each of $E=\pm1$, while the displayed sum is empty. Thus $L\ge5$ is necessary for the displayed formula with this pairwise definition and this summation range.
- *Effect on the source.* The formula supplies the full finite-size configuration count in place of the acknowledged missing expression. The source's Hamiltonian construction and entanglement claims remain separate inputs, and its asymptotic inequality following Table I is not verified by this settlement. The source also says, at TeX lines 680–683: “Comparing the degeneracy of the bubble eigenstates with the integer eigenstates, we see that for $L=16,18,20$, $E=\pm n_0$ eigenstates are solely the bubble eigenstates. We conjecture that this property is true for any $L$.” Here $n_0=\lfloor L/5\rfloor$; this distinct conjecture remains open in this settlement because counting the bubble configurations does not exclude non-bubble states at the same energies. The non-bubble scaling and entanglement questions at lines 751–758 likewise remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check recorded in #26367 does not establish exhaustive worldwide novelty or priority. Its citing-work readings, INSPIRE citation count and repository-search results were not independently reproduced; the source reading here is the v3 TeX, not a comparison of all versions or an independent check that v3 is the latest version.

The Hamiltonian eigenstate correspondence, independence and completeness of the physical bubble-state construction, the remaining spectrum, entanglement claims, asymptotic estimates and open boundary conditions are not formalized by this module. The statements in “Computed, not formalized” and “Argued, not formalized” are not additional formal results. The variable-distance extension, endpoint evaluations, energy-symmetry identity and small-length classification have prose arguments but no separate compiled declarations here. The distinct extremal-energy and non-bubble questions remain open in the scope of this dossier.
