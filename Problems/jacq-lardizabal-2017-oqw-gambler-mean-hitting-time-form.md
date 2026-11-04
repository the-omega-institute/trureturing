---
slug: jacq-lardizabal-2017-oqw-gambler-mean-hitting-time-form
bibkey: jacqlardizabal2017oqwhalfline
doi: 10.1007/s10955-017-1876-x
url: https://arxiv.org/abs/1701.08400v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result
---

# The Jacq–Lardizabal mean-hitting-time form is false

## Problem

T. S. Jacq and C. F. Lardizabal, *Open Quantum Random Walks on the Half-Line: The Karlin–McGregor Formula, Path Counting and Foster's Theorem* (J. Stat. Phys. 169, 547–594, 2017; arXiv:1701.08400v3), state the following in Remark 5.3 of the source TeX `JL_rev2.tex`, lines 1291–1293:

> Numerical experiments allows us to recognize a behavior that such OQW has in common with Example 5.1, namely, that the mean hitting time has the form $E_{k,\rho}(\tau)=1+h(M,M-k)\rho_{11}+h(M,k)\rho_{22}+j(M,k)Re(\rho_{12}),$ where $h, j$ are functions of $M$ and $k=1,\dots, M-1$, with $j$ being a function satisfying $j(M,k)=-j(M,M-k)$. We conjecture that this holds for the gambler's ruin problem associated to *every* pair or matrices $L$, $R$ with $L^*L+R^*R=I$ inducing an OQW on vertices $\{0,\dots, M\}$. A proof of this statement is, up to our knowledge, unknown.

The formal `claim` fixes two-dimensional complex matrices $l,r$ with $l^*l+r^*r=1$, every natural $m$ with $3\le m$, and functions $h,j:\mathbb N\to\mathbb N\to\mathbb R$. It requires the stated antisymmetry for every $k$ with $1\le k\le m-1$ and, for every such $k$ and every `IsDensity` matrix $\rho$, requires `meanHittingTime` to be different from $\top$ and its `toReal` value to equal $1+h(m,m-k)(\rho\ 0\ 0).re+h(m,k)(\rho\ 1\ 1).re+j(m,k)(\rho\ 0\ 1).re$. Here `IsDensity` is positive semidefiniteness together with trace one, and `meanHittingTime` has codomain `ℝ≥0∞`, the extended nonnegative reals.

## Motivation

For a nearest-neighbour open quantum walk, the normalization $L^*L+R^*R=I$ makes the first-visit expansion a natural candidate for a universal formula. The conjectured form would reduce the mean hitting time to two diagonal real entries and the real part of one off-diagonal entry, with a reflection relation for $j$. A counterexample determines that this reduction cannot be used for all complex pairs of transition matrices.

## Gap

The bounded literature check recorded in issue [#24081](https://github.com/the-omega-institute/trureturing/issues/24081) retained the conjecture in the source and found no settlement in the searched related literature or in the repository. It does not establish an exhaustive worldwide search.

`not-found-in-searched-scope`.

## Route

1. The module defines `wordOperator` by mapping `false` to $l$ and `true` to $r$, reversing the mapped list, and taking its matrix product. `position` starts at $k$ in $\mathbb Z$ and adds $1$ for each `true` and $-1$ for each `false` in the first $t$ letters. `firstAbsorbs` requires every strict prefix to have position strictly between $0$ and $m$ and the full word to end at $0$ or $m$. `absorbedMass` sums the real parts of $\operatorname{trace}(W\rho W^\mathsf H)$ over the length-$n$ words produced by `List.sections (List.replicate n [false,true])` that satisfy `firstAbsorbs`; `meanHittingTime` is `∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (absorbedMass l r m k ρ n)`.
2. `word_operator_append` proves, with no additional hypotheses, that `wordOperator l r (a ++ b) = wordOperator l r b * wordOperator l r a`.
3. Given matrices $l,r$, a hypothesis `hz : l * r = 0`, a list $w$ with `hn : 3 ≤ w.length`, and `hw : firstAbsorbs 3 1 w`, `stopped_word_zero` proves `wordOperator l r w = 0`. Its case split uses the prefix conditions in `hw` and the factorization from `word_operator_append`; the only viable first two letters are `true,false`, whose branch product is $l*r$.
4. Under the same `hz : l * r = 0`, `absorbed_mass_tail` proves for every $n$ with `3 ≤ n` that `absorbedMass l r 3 1 ρ n = 0`. Without extra hypotheses, `absorbed_mass_one` identifies the time-one mass with $(\operatorname{trace}(l\rho l^\mathsf H)).re$, and `absorbed_mass_two` identifies the time-two mass with $(\operatorname{trace}((r*r)\rho(r*r)^\mathsf H)).re$.
5. `mean_two_step`, assuming `hz : l * r = 0`, combines those three lemmas and gives
   $\operatorname{meanHittingTime}\,l\,r\,3\,1\,\rho=\operatorname{ENNReal.ofReal}(\operatorname{trace}(l\rho l^\mathsf H)).re+2\,\operatorname{ENNReal.ofReal}(\operatorname{trace}((r*r)\rho(r*r)^\mathsf H)).re$.
6. `result` takes $u=(1,i)$ and $v=(1,-i)$, indexed by `Fin 2`, and sets $l=\frac12vu^\mathsf H$, $r=\frac12vv^\mathsf H$, $\rho=\frac12uu^\mathsf H$, and $\sigma=\frac12vv^\mathsf H$. Entrywise normalization gives $l^\mathsf H l+r^\mathsf H r=1$ and $l*r=0$; the two matrices satisfy `IsDensity`. The same calculation gives equal real values for $(\rho\ 0\ 0)$ and $(\sigma\ 0\ 0)$, for $(\rho\ 1\ 1)$ and $(\sigma\ 1\ 1)$, and for $(\rho\ 0\ 1)$ and $(\sigma\ 0\ 1)$. Applying `mean_two_step` gives means $1$ and $2$ at $m=3,k=1$. If `claim` held, its common affine expression would give the same value for these two density matrices, which yields the contradiction used by `result`.

## Falsifier

The formalization tests the source reading at the level of stopped words. It uses complex $2\times2$ matrices, Boolean words with `true` as a right step, integer positions, and first absorption at $0$ or $m$. Its `absorbedMass` is the real part of the unnormalized branch trace, and its `meanHittingTime` is an extended nonnegative sum. The `claim` quantifies all normalized pairs, all $m\ge3$, all interior $k$, and all positive-semidefinite trace-one matrices, then requires finiteness and the exact three-entry affine expression. Thus the refutation does not rely on a numerical approximation or on replacing the source's complex matrix entries by real ones.

## Evidence

The canonical source is `D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:0742c8b709ddd0d322069d0d94f1c7f8d677593d9439582579bf3b7b8e86a30d`;
- `claim`: `sha256:662dc063246bfa96dca8574139d470e85259076a6d70210d4dace2ede7e071db`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2017 paper, preregistered in issue #24081 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** The declaration has type `¬ claim`, so the formal universal three-entry mean-hitting-time statement is false under the definitions in the module.

**Computed, not formalized:** none.

**Argued, not formalized.**

- **Mechanism.** The reset pair sends the two initial internal directions represented by $u$ and $v$ to a common direction through $l$ and keeps the $v$ direction fixed through $r$, while $l*r=0$. For the restricted walk with $m=3$ and $k=1$, the first-absorption conditions leave the one-step left branch and the two-step right-right branch; the length-at-least-three tail is removed by the hypotheses of `stopped_word_zero` and `absorbed_mass_tail`. The two density matrices have the same two diagonal real entries and the same real upper-right entry, but their stopped means are $1$ and $2$. The separating information is therefore carried by the imaginary part of the off-diagonal entry for this pair.
- **Nearby statements.** A formula that also allows an $\operatorname{Im}(\rho\ 0\ 1)$ term, restrictions to particular pairs, and questions in higher internal dimension are not formalized here. The source's Theorems 1.6–1.7 and its formulas for particular pairs are outside `claim`; this settlement does not refute those statements.
- **Effect on dependent statements.** Any argument that uses Remark 5.3's universal form for every normalized pair must be restricted or replaced. No source theorem beyond that conjectural form is claimed to depend on it by this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and searches recorded in issue #24081 and does not establish exhaustive novelty or priority. The amended formula with an imaginary-part term, higher-dimensional analogues, and walks for which absorption is not almost sure remain open here. The mechanism and scope explanations in `Argued, not formalized` are not separate Lean declarations. The source's other theorems and pair-specific formulas were not formalized by this module.
