---
slug: albors-et-al-2024-bad-science-matrix-five
bibkey: alborsetal2026badscience
doi: 10.2140/involve.2026.19.443
url: https://arxiv.org/abs/2408.00933
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.result
---

# The exact five-dimensional bad science optimum

## Problem

Albors, Bhatti, Ganjoo, Guo, Kunisky, Mukherjee, Stepin and Zeng,
*On the Structure of Bad Science Matrices*, arXiv:2408.00933v2,
Section 1.4, ask: “We do not know whether this matrix is indeed optimal.”
The matrix is their displayed real $5\times5$ matrix $A_*$, and the
admissible matrices have rows of Euclidean length one.
The journal reference is Involve 19 (2026), 443–460,
DOI [10.2140/involve.2026.19.443](https://doi.org/10.2140/involve.2026.19.443).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Real square matrices and the uniform sign-cube average in Section 1 | `beta`, with `Matrix (Fin n) (Fin n) ℝ`, Boolean sign vectors and weight $2^{-n}$ | The function-space norm is the sup norm. The sign expression is literal; the proofs reuse `IsingUniquenessSets.sgn` through definitional equality. |
| “rows are normalized to have ℓ²-length 1” | `UnitRows` | Every row's sum of squared real entries equals one. |
| The displayed matrix of Section 1.4 | `Astar` | All 25 entries and the factor $1/(2\sqrt3)$ agree with the source. |
| “this matrix is indeed optimal” | `claim` and `result` | Every real $5\times5$ matrix satisfying `UnitRows` has $\beta(A)\le\beta(A_*)$; there is no extra hypothesis. |

The declarations belong to
`D5.S3.Combinatorics.Hamming.BadScienceFiveOptimality`.

## Motivation

The result determines the exact five-dimensional optimum
$\max_A\beta(A)=(2+3\sqrt3)/4$.
The source's candidate therefore supplies the $n=5$ entry in its table of
optimal values. The dimensions $n\le4$ have the source's existing results.

## Gap

[Preregistration #17586](https://github.com/the-omega-institute/trureturing/issues/17586)
contains the source quotation, complete quantifiers, literature readings and
settlement criterion. This is an external named open-problem settlement,
with admission basis `open-problem-resolution (#17586; Proved)` and no atom.
The proof is classified `bind-only` under the repository's normalization
criterion; the admission basis is the named problem's settlement.

## Route

For an antipodal-free subset $S$ of the five-cube, let $m=|S|$ and
$u=\sum_{x\in S}x$. Cube orthogonality and Cauchy–Schwarz give
$\|u\|_2^2\le16m$. The parity/Hamming estimate gives
$\|u\|_2^2\le m^2+4m+4\lfloor m^2/4\rfloor$.
Combining the two estimates yields the affine majorant
$L(m)=(2\sqrt3-2)m+8-4\sqrt3$ for $\|u\|_2$.
The five oriented winning-row cells have total cardinality 16, and hence
$16\beta(A)\le\sum_iL(m_i)=8+12\sqrt3$.
The private lemmas `lemma1`, `lemma2`, `lemma3`, `lemma4` and `Astar_beta`
are the corresponding kernel-checked steps used by `result`.

## Falsifier

A real $5\times5$ matrix with unit rows and
$\beta(A)>(2+3\sqrt3)/4$ would contradict `result` together with
`Astar_beta`. The sign encoding, uniform weight, sup norm and all matrix
entries are explicit in the definitions.

## Evidence

The Lean module and its Blueprint mirror are
`D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.lean` and
`Blueprint/D5/S3/Combinatorics/Hamming/BadScienceFiveOptimality.scribe.cs`.
The sole public theorem is `result : claim`. Its axiom closure is contained
in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit for `result` is unfinished:
[issue #17688](https://github.com/the-omega-institute/trureturing/issues/17688).
The dependent matrix source requires reconstruction, a faithful realization
bridge, positivity and whole-family sensitivity evidence; these compiled
registration proofs are absent. No validated registration is claimed.

### Experiment

[Experiment directory at commit 5022ea1b310af5f8558e33bd9ae582a915776d73](https://github.com/the-omega-institute/trureturing-experiments/tree/5022ea1b310af5f8558e33bd9ae582a915776d73/docs/reports/albors-et-al-2024-bad-science-matrix-five).
Command: `python3 docs/reports/albors-et-al-2024-bad-science-matrix-five/check.py`
in that experiments checkout; exit 0, `ALL_OK`.
The SHA-256 of `check.py` is
`d03730def270c83af83bd90e05530fea92fecd4f4793bedc3b1ef70167f70b84`.
The run uses NumPy 2.4.2 and SymPy 1.14.0.

The exact symbolic computation gives
$\beta(A_*)=1/2+3\sqrt3/4$, with 24 image sup norms $\sqrt3$ and eight
image sup norms 2, and verifies its unit rows.
Exhaustive antipodal-free subsets for $0\le m\le7$ give maximal squared
sum lengths $0,5,16,29,48,61,80,101$.
The run tests 20,000 random antipodal-free subsets with $8\le m\le16$.
A local ascent with 400 starts and 400 proposals per start reaches
$1.791563127$, below $1.799038106$. Those sampled checks establish no
universal claim; the universal inequality is the Lean result.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked:** `lemma3` bounds every antipodal-free
  five-cube sum by $L(m)$. `lemma4` sums the bound over five oriented cells
  of total size 16 to obtain $16\beta(A)\le8+12\sqrt3$.
  The two-set with its first four coordinates positive and last coordinate
  variable has norm 4, equal to $L(2)$. The four-set with its first three
  coordinates positive and last two coordinates variable has norm
  $4\sqrt3=L(4)$. These sharpness examples are proved in prose by their
  sums $(2,2,2,2,0)$ and $(4,4,4,0,0)$.
- **Strength — kernel-checked:** `result` proves the universal inequality,
  `Astar_beta` its exact attained value, and `Astar_norm` the 32 image norms.
  The counts 24 and eight are checked within `Astar_beta`.
  **Admissibility — proved in prose:** the first three rows of $A_*$
  have three entries of absolute value $1/\sqrt3$; the last two have four
  entries of absolute value $1/2$. Each squared row length is one.
  These facts give the exact optimum.
- **Consequences — proved in prose:** the universal upper bound and this
  admissible attaining matrix settle the source's $n=5$ table entry.
- **Equality-cell restriction — proved in prose, not formalized:** the
  estimates used for $L(m)$ are strict for integer $m\ne2,4$.
  For $m=0$ this follows from $L(0)>0$; for $m=1,3,5$ the positive
  squared gaps are $43-24\sqrt3$, $8\sqrt3-13$, $43-24\sqrt3$;
  for $m\ge6$ use
  $L(m)^2-16m=8[(2-\sqrt3)m(m-6)+14-8\sqrt3]>0$.
  Equality therefore requires five sizes in $\{2,4\}$ whose sum is 16,
  namely $\{4,4,4,2,2\}$.
- **Open:** uniqueness of the extremizer up to symmetries, and the
  optimum in dimensions $n\ge6$. The cell-size restriction does not
  classify all extremizing matrices.
- **Experiment — computed:** the pinned experiment entry above gives
  the exact value and counts, the exhaustive range $0\le m\le7$, and
  the stated sampled ranges; no program or dataset is embedded here.
- **Literature — literature reading:** the preregistration records the
  source's Section 1.4, Steinerberger arXiv:2402.03205 (“We have not tried
  to prove that any of our potentially optimal configurations are
  optimal”), and Sinha arXiv:2509.10580, which lists the five-dimensional
  matrix as conjectured. No proof was found in that checked scope.
  Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness, including the unread journal version of record
and unlocated citing work, is `ASSUMED-UNVERIFIED`. The literature readings
are attributed to the orchestrator in #17586. Numerical sampling does not
establish uniqueness or an optimum for $n\ge6$. The four-slot escape
audit remains unfinished under #17688.
