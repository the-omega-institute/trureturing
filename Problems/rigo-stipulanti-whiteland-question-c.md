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

Issue [#23400](https://github.com/the-omega-institute/trureturing/issues/23400) preregistered this published open problem before the Lean proof. The frozen settling declaration is `D5.S1.Words.Complexity.ThueMorseFactorRigidity.result`, with admission basis `open-problem-resolution (#23400; Proved)`. The Scribe result carries one `OpenProblemResolutionClaim` with resolution `Proved` for this dossier.

## Gap

The source asks for arbitrary hierarchy height and an unbounded first binomial complexity. The construction supplies the missing universal argument: a lacunary marker projection is reconstructed by its 2-profile, while the coded Fibonacci/Thue–Morse projection supplies every strict refinement and the overlay preserves the hierarchy. Literature completeness remains `ASSUMED-UNVERIFIED`.

## Route

For $\ell\ge2$, put $k=\ell-2$. Start with the Fibonacci fixed point, apply the Thue–Morse morphism $k$ times, and overlay it with a binary marker word whose marker positions grow at least threefold. The identity

$$
\binom{u}{01}=\sum_d r_d-\frac{h(h-1)}2
$$

recovers the marker count and offset sum, and lacunarity makes consecutive marker blocks uniquely recoverable from the 2-profile. Uniform recurrence lifts the source strict inequalities through all-zero marker gaps. A synchronized starred substitution with positions $p_n=F_{3n+2}$ gives the standard morphic coding over four product letters. The kernel-checked `result` is the complete formal settlement.

## Falsifier

An in-range factor whose 2-profile agrees with a distinct marker factor, a failure of the overlay implication, a missing strict split at some hierarchy level, or a failure of the synchronized coding would falsify the delivered claim. A prior proof in the searched literature would change the literature boundary but would not change the compiled theorem. The pure-morphic fixed-point refinement and optimal alphabet bound are outside the claim.

## Evidence

The Lean module and Blueprint Scribe establish the exact proposition for every $\ell\ge2$. The finite experiment is helper evidence only: repository `the-omega-institute/trureturing-experiments`, commit `624bd0b7012da160736c055604807d3c26178d4f`, report `docs/reports/rigo-stipulanti-whiteland-qc/`, command `python3 docs/reports/rigo-stipulanti-whiteland-qc/check.py`, exit code `0`, final line `ALL_CHECKS_OK`, and script SHA-256 `7b1dca7b12549c12e04adb4d3c3744428a50109ec32651c8914de67bedcbe187`.

The supporting state records are `Golden/Frozen/state/D5/S1/Words/Complexity/LacunaryBinomialMarkers.lean.json`, `UniformWordRecurrence.lean.json`, `ThueMorsePositionalRecovery.lean.json`, and `ThueMorseFactorRigidity.lean.json`. The unfinished four-slot escape audit for non-result public declarations is tracked in [#23567](https://github.com/the-omega-institute/trureturing/issues/23567); no `declared_validated` registration is claimed.

## Triage

| Item | Status | Evidence kind |
| --- | --- | --- |
| First and second-order counts recover boundary letters unless the two opposite-alignment words are already equal alternating words; empty and short cases are included. | proved | kernel-checked declarations on the live proof path |
| Common padding cancels for positional root divisibility. Pullback through $X^2$ preserves the remaining root order because $X+1$ is coprime to $X-1$ over $\mathbb Q$. | proved | kernel-checked declarations on the live proof path |
| One-step Thue–Morse expansion increases the necessary moment order by one for every binary source with RootRigid w d, d ≥ 1; uniform recurrence is not required for this rigidity transfer. | proved | kernel-checked declarations on the live proof path |
| The complemented golden base and induction prove RootRigid (core k) (k+2) for every k, supplying the requested injectivity and then the entire hierarchy. | proved | kernel-checked declarations on the live proof path |
| Round-one lacunarity, recurrence transfer, strict refinements, aligned recovery, and synchronized morphic identities are preserved. | proved | kernel-checked `result` and consumed supporting declarations |
| Finite checks are consistent with the proof; they do not establish its universal quantifiers. | computed | pinned experiment at commit `624bd0b7012da160736c055604807d3c26178d4f` |
| The optional pure-morphic fixed-point refinement is outside the binding claim and is not settled here. | open | excluded scope of `claim` |
| An optimal alphabet bound and exhaustive literature novelty are not settled. | open | excluded scope; literature completeness `ASSUMED-UNVERIFIED` |
| Literature completeness for the source and later specialist literature screen. | ASSUMED-UNVERIFIED | bounded source and literature search recorded in #23400 |

### What the settlement shows

**Proved in this module.** Every $\ell\ge2$ has a four-letter coded morphic witness with unbounded first binomial complexity, strict inequalities through level $\ell$, and equality of level $\ell$ with factor complexity. The decisive mechanisms are lacunary 2-profile reconstruction, uniform-recurrence alignment, the Thue–Morse moment-order transfer, and the synchronized starred substitution. The argument does not require uniform recurrence for the one-step rigidity transfer itself.

**Computed only.** The finite machine check reproduces the source’s finite hierarchy examples, marker reconstructions and overlay identities in its recorded ranges. Those checks do not discharge the universal quantifiers.

**Open boundary.** The pure-morphic fixed-point refinement, an optimal alphabet bound, and exhaustive literature novelty remain outside this settlement. Source conclusions that require only the standard morphic coding may use the proved result; claims requiring the stronger pure-morphic fixed-point form need an additional theorem.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are `ASSUMED-UNVERIFIED`: the bounded searches in #23400 include rate-limited APIs and do not establish exhaustive worldwide absence of a later settlement. The finite experiment is not a proof premise. Four-slot escape registration for public declarations other than the designated `result` remains unfinished under [#23567](https://github.com/the-omega-institute/trureturing/issues/23567).
