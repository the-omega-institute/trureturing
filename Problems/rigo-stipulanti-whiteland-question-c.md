---
slug: rigo-stipulanti-whiteland-question-c
bibkey: rigostipulantiwhiteland2022binomial
doi: 10.1016/j.ejc.2024.103932
url: https://arxiv.org/abs/2201.04603v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/ThueMorseFactorRigidity.result
---

# Rigo–Stipulanti–Whiteland Question C

## Problem

Michel Rigo, Manon Stipulanti and Markus A. Whiteland, “Characterizations of families of morphisms and words via binomial complexities,” arXiv:2201.04603v2, Section 7.1, Question C, asks whether for each $\ell\ge1$ there is a word $w$ with unbounded $b_w^{(1)}$ and

$$
b_w^{(1)}\prec b_w^{(2)}\prec\cdots\prec b_w^{(\ell-1)}\prec b_w^{(\ell)}=p_w,
$$

and whether a pure morphic word can be chosen. The settled range is the positive answer for every integer $\ell\ge2$, with a witness over at most four letters in the standard morphic coding sense. The source’s $\ell=1$ case is excluded by Remark 7.1 together with the required unboundedness. The optional pure-morphic fixed-point refinement remains outside the claim.

The source definitions are the scattered subword count $\binom{u}{x}$, $k$-binomial equivalence by equality of all counts for patterns of length at most $k$, $b_w^{(k)}(n)=\#(L_n(w)/\sim_k)$, and $f\prec g$ when $f(n)<g(n)$ for infinitely many $n$.

## Motivation

Issue [#23400](https://github.com/the-omega-institute/trureturing/issues/23400) specifies this published open problem. The settling declaration is `D5.S1.Words.Complexity.ThueMorseFactorRigidity.result`, with admission basis `open-problem-resolution (#23400; Proved)`. The Scribe result carries one `OpenProblemResolutionClaim` with resolution `Proved` for this dossier.

## Gap

The source asks for arbitrary hierarchy height and an unbounded first binomial complexity. The construction supplies the missing universal argument: a lacunary marker projection is reconstructed by its 2-profile, while the coded Fibonacci/Thue–Morse projection supplies every strict refinement and the overlay preserves the hierarchy. Literature completeness remains `ASSUMED-UNVERIFIED`.

## Route

For $\ell\ge2$, put $k=\ell-2$. Start with the Fibonacci fixed point, apply the Thue–Morse morphism $k$ times, and overlay it with a binary marker word whose marker positions grow at least threefold. The identity

$$
\binom{u}{01}=\sum_d r_d-\frac{h(h-1)}2
$$

recovers the marker count and offset sum, and lacunarity makes consecutive marker blocks uniquely recoverable from the 2-profile. Uniform recurrence lifts the source strict inequalities through all-zero marker gaps. A synchronized starred substitution with positions $p_n=F_{3n+2}$ gives the standard morphic coding over four product letters. The `result` gives the hierarchy conclusion.

## Falsifier

An in-range factor whose 2-profile agrees with a distinct marker factor, a failure of the overlay implication, a missing strict split at some hierarchy level, or a failure of the synchronized coding would falsify the delivered claim. A prior proof in the searched literature would change the literature boundary but would not change the compiled theorem. The pure-morphic fixed-point refinement and optimal alphabet bound are outside the claim.

## Evidence

The Lean module and Blueprint Scribe state the proposition for every $\ell\ge2$.

The [finite experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/624bd0b7012da160736c055604807d3c26178d4f/docs/reports/rigo-stipulanti-whiteland-qc) uses command `python3 docs/reports/rigo-stipulanti-whiteland-qc/check.py`, exit code `0`, and script SHA-256 `7b1dca7b12549c12e04adb4d3c3744428a50109ec32651c8914de67bedcbe187`. It computes the source Theorem 7.4 finite example at lengths $6\le n\le15$ on the 240-iterate prefix, verifies binary marker 2-profile reconstruction at lengths $1\le n\le30$ on a 10,000-letter prefix, and checks abelian lower bounds for $1\le h\le6$. Its overlay checks use Fibonacci prefixes of length 2,500 expanded $k=0,1,2$ times, terminal levels $2,3,4$ at lengths $2\le n\le13$, and the abelian projection comparison at length 34. These finite checks support no uniform extension beyond the stated ranges.

The supporting state records are `Golden/Frozen/state/D5/S1/Words/Complexity/LacunaryBinomialMarkers.lean.json`, `UniformWordRecurrence.lean.json`, `ThueMorsePositionalRecovery.lean.json`, and `ThueMorseFactorRigidity.lean.json`. The unfinished four-slot escape audit for every newly authored public theorem, including the settling `result` and the three publicized owner theorems is tracked in [#23567](https://github.com/the-omega-institute/trureturing/issues/23567); no `declared_validated` registration is claimed.

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| First and second-order counts recover matching frame boundaries, or the framed words are equal; empty and short cases are included. | proved | kernel-checked `ThueMorsePositionalRecovery.Alignment.frame_alignment` |
| Common padding cancels for equal-length interiors in positional root divisibility; pullback through $X^2$ preserves root order over $\mathbb Q$. | proved | kernel-checked `ThueMorsePositionalRecovery.RootTransport.rootEq_cancel_padding` and `RootTransport.root_pullback_square` |
| One-step Thue–Morse expansion transfers $\mathrm{RootRigid}(w,d)$ to $\mathrm{RootRigid}(\mu w,d+1)$ for $d\ge1$, without uniform recurrence. | proved | kernel-checked `ThueMorsePositionalRecovery.Rigidity.rootRigid_mu` |
| The complemented golden base and induction establish $\mathrm{RootRigid}(\mathrm{core}(k),k+2)$ and top-profile injectivity for every $k$. | proved | kernel-checked `ThueMorsePositionalRecovery.Rigidity.rootRigid_core_zero`, `Rigidity.rootRigid_core`, and `Rigidity.top_profile_injectivity` |
| Lacunary reconstruction, recurrence transfer, strict refinements, factor recovery, and synchronized morphic realization give the hierarchy for every $\ell\ge2$. | proved | kernel-checked `ThueMorseFactorRigidity.morphic_result` and `ThueMorseFactorRigidity.result` |
| The finite source example, marker reconstruction and overlay identities hold in exactly the ranges in the experiment entry. | computed | immutable experiment script, command, exit code and SHA-256 in Evidence |
| A pure-morphic fixed-point witness is available for each hierarchy height. | open | no such assertion is made by `claim` or `morphic_result` |
| The four-letter upper bound is optimal. | open | the delivered construction gives an upper bound only |
| No later specialist publication settles the same problem. | open | literature completeness remains `ASSUMED-UNVERIFIED`; bounded source and literature reading in #23400 |
| The first level $\ell=1$ is excluded by Remark 7.1 and the unboundedness requirement. | proved | paper argument in The excluded first level; no Lean statement is claimed |

### The excluded first level

The exclusion of $\ell=1$ uses the source's Remark 7.1, rather than a Lean declaration in this delivery. That classification makes a word with $b_w^{(1)}=p_w$ ultimately periodic. If its preperiod length is $a$ and its period length is $q$, then for every factor length there are at most $a$ factors starting before the periodic tail and at most $q$ tail factors. Hence $b_w^{(1)}(n)\le p_w(n)\le a+q$ for every $n$, contradicting the required unboundedness. This is a paper argument using the cited classification.

### What the settlement shows

**Proved in this module.** Every $\ell\ge2$ has a four-letter coded morphic witness with unbounded first binomial complexity, strict inequalities through level $\ell$, and equality of level $\ell$ with factor complexity. The decisive mechanisms are lacunary 2-profile reconstruction, uniform-recurrence alignment, the Thue–Morse moment-order transfer, and the synchronized starred substitution. The argument does not require uniform recurrence for the one-step rigidity transfer itself.

**Computed only.** The finite machine check reproduces the source’s finite hierarchy examples, marker reconstructions and overlay identities in its recorded ranges. Those checks do not discharge the universal quantifiers.

**Open boundary.** The pure-morphic fixed-point refinement, an optimal alphabet bound, and exhaustive literature novelty remain outside this settlement. Source conclusions that require only the standard morphic coding may use the proved result; claims requiring the stronger pure-morphic fixed-point form need an additional theorem.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are `ASSUMED-UNVERIFIED`: the bounded searches in #23400 include rate-limited APIs and do not establish exhaustive worldwide absence of a later settlement. The finite experiment is not a proof premise. Four-slot escape registration for every newly authored public theorem, including the settling `result` and the three publicized owner theorems remains unfinished under [#23567](https://github.com/the-omega-institute/trureturing/issues/23567).
