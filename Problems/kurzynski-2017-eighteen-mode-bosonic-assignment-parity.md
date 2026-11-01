---
slug: kurzynski-2017-eighteen-mode-bosonic-assignment-parity
bibkey: kurzynski2017contextualityidentical
doi: 10.1103/PhysRevA.95.012133
url: https://arxiv.org/abs/1609.01250v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.result
---

# Eighteen-mode bosonic occupation assignments exist exactly for even particle numbers

## Problem

P. Kurzyński, *Contextuality of identical particles*, Phys. Rev. A 95(1), 012133 (2017), arXiv:1609.01250v1, asks in “Contextuality of $N>2$ bosons” (`contextuality_fermions.tex`, line 233):

> The Hardy-like proof shows that there is the state-dependent contextuality in the 18-mode scenario for any $N>0$. However, the lack of the state-independent contextuality was only shown for $N=2$. It is possible that for some $N>2$ the bosonic occupation numbers of 18 modes cannot be assigned in a non-contextual way. This would require further research, since for large numbers of particles there are many ways in which the particles can be distributed between the modes.

The source's bosonic model assigns a nonnegative integer to each mode, independently of the context, with the occupations in every context summing to the particle number $N$ (lines 70–76, Eq. (1)). A mode $v_{ij}$ belongs to contexts $i$ and $j$ (line 83); the nine contexts are displayed in lines 132–221. The definitions and source locator are also recorded in [the literature note](../Library/Observer/kurzynski2017contextualityidentical.md).

The formal definition `modes` is the set

$$
E=\{(1,2),(1,6),(1,7),(1,8),(2,3),(2,8),(2,9),(3,4),(3,7),
(3,9),(4,5),(4,7),(4,8),(5,6),(5,8),(5,9),(6,7),(6,9)\}.
$$

For $i\in\{1,\ldots,9\}$, put $C_i=\{(a,b)\in E:a=i\text{ or }b=i\}$. The definition `IsNoncontextualAssignment` requires one function $v:\mathbb N\times\mathbb N\to\mathbb N$ satisfying $\sum_{p\in C_i}v(p)=N$ for every such $i$. Values outside $E$ are unrestricted and do not enter any context sum.

Issue [#24135](https://github.com/the-omega-institute/trureturing/issues/24135) fixes the statement `claim`: for every $N\in\mathbb N$, such an assignment exists if and only if $N$ is even. This classification is proved.

## Motivation

The source distinguishes an obstruction to assigning occupations from contextuality witnessed only after imposing constraints from a particular quantum state. Its question asks whether the 18-mode assignment obstruction returns beyond two bosons. Classifying all particle numbers answers that question without enumerating the increasingly numerous distributions of particles among modes.

## Gap

The bounded literature check recorded in #24135 covers:

- arXiv:1609.01250v1, whose question remains at line 233;
- Crossref, reporting seven citations, and Semantic Scholar, reporting six distinct citing works, together with OpenCitations COCI;
- full-text readings of arXiv:1707.04656, 1801.02338, 1802.08424, 1806.06637 and 1906.09041, reported as containing no arbitrary-boson classification for this 18-mode set;
- a repository duplicate check, reporting no existing settlement of this question; the recorded doily parity result concerns a different incidence structure.

The Springer chapter DOI 10.1007/978-3-319-72478-2_17 and the APS article full text were inaccessible to that check; only their abstracts and references were available.

`not-found-in-searched-scope`.

## Route

1. **Double count.** For every natural-valued function $v:\mathbb N\times\mathbb N\to\mathbb N$, the private lemma `incidence_double_count` proves
   $\sum_{i=1}^{9}\sum_{p\in C_i}v(p)=2\sum_{p\in E}v(p)$.
   Each listed pair has two distinct endpoints in $\{1,\ldots,9\}$, so its occupation occurs exactly twice in the left-hand sum.
2. **Necessity.** For every $N\in\mathbb N$ and $v:\mathbb N\times\mathbb N\to\mathbb N$ satisfying `IsNoncontextualAssignment` at $N$, the private lemma `assignment_even` substitutes the nine conservation equations into the double count to obtain $9N=2\sum_{p\in E}v(p)$. Since $9$ is odd, $N$ is even.
3. **Sufficiency.** For every $m\in\mathbb N$, the private lemma `even_assignment` constructs an assignment for $2m$: give occupation $m$ to the modes in
   $S=\{(1,2),(1,6),(2,8),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9)\}$
   and zero to every other pair. Each of the nine contexts contains exactly two members of $S$, so its sum is $2m$. The construction includes $m=0$.

The theorem `result` combines the two directions for every natural $N$.

## Falsifier

The classification would not answer the source's question if the occupations or contexts differed from its model. The module uses the eighteen labels in the source's nine displayed contexts, one natural-valued occupation per label shared across contexts, and the conservation equation in every context. Extending the domain of $v$ to all natural-number pairs adds no constraint: those outside `modes` never occur in a context sum, and any assignment on the eighteen labels extends by zero.

Existence of an even-$N$ assignment supplies neither a probability distribution reproducing quantum measurements nor a non-contextual model for every even-$N$ state. The classification concerns precisely the existence of the occupations required by Eq. (1).

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.lean.json`.

Declaration statements:

- `result`: `sha256:32d3e1f79957d958759dbf7e0c09b61168b326c0b2210377d580de10ef26d7ce`;
- `claim`: `sha256:cd316031b921834ec361445cbcfc2052fe679fc798cee4abc2d204695991d755`.

## Triage

Tier 1 question of a 2017 paper, preregistered in issue #24135 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $N$, including zero, there exists a natural-valued function on pairs of natural numbers whose occupations sum to $N$ in each of the nine specified contexts if and only if $N$ is even.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *The structure of the witness.* For every natural $m$, `even_assignment` supplies an assignment for $2m$. Its selected set $S$ consists of the edges of the cycle $1,2,8,4,7,3,9,5,6,1$: the consecutive pairs, written with the smaller endpoint first, are exactly the nine listed elements of $S$. Each context is a vertex of this cycle and meets its two adjacent edges. This explains the two selected modes per context without a search over particle distributions, including the zero assignment when $m=0$.
- *Extension with explicit hypotheses.* Consider a finite set of modes and a family of an odd number $r$ of contexts, with every mode belonging to exactly two distinct contexts. A natural-valued assignment with common context sum $N$ would give $rN=2\sum_pv(p)$ by counting each mode twice, hence $N$ must be even. If that family also has a subset of modes meeting each context in exactly two modes, then for every $m\in\mathbb N$, occupation $m$ on that subset and zero elsewhere gives every sum $2m$. These incidence and subset hypotheses therefore suffice for the same classification; double incidence alone supplies only the necessary parity condition. This general statement is not a declaration of the module.
- *Sharpness and particle number.* Every odd $N>2$, starting at $N=3$, answers the source's existential question affirmatively; every even $N$ admits an assignment. Arbitrarily large odd and even numbers therefore retain different assignment behavior. In particular, increasing particle number does not yield an eventual absence of the assignment obstruction for this fixed set.
- *Effect on the paper.* Kurzyński's question at line 233 and the corresponding unresolved assignment issue in the conclusion at line 237 are settled for these eighteen modes. The source's Hardy-like state-dependent argument for every $N>0$ (lines 227–233) is compatible with this classification: it imposes state-specific constraints beyond the nine conservation equations. The separate possibility of other state-independent contextuality inequalities for two particles (line 113), and the questions for arbitrary dimensions or other mode sets (line 242), remain open in this settlement. No measurement inequality, bosonic Fock-space realization or fermionic classification is supplied by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The Crossref and citation-search readings, the five citing-work readings and the repository-wide duplicate check rely on the reports in #24135. The Springer chapter and APS full-text contents remain unverified; the source quotation and context labels here are checked against the arXiv v1 TeX.

The cycle interpretation, the general incidence-family argument and the consequences discussed under “Argued, not formalized” have no separate Lean declarations in this module. The source's quantum-state calculations and Hardy-like probabilities are not independently verified here. The connection to physical measurements, alternative contextuality inequalities, other mode sets, relaxed particle-number conservation and operational large-$N$ limits is not formalized. These remain outside the proved occupation-assignment classification.
