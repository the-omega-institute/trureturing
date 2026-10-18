---
slug: dhamapurkar-deng-2023-lattice-walk-cross-integral-refutation
bibkey: dhamapurkar2023latticemixing
doi: 10.1016/j.physa.2023.129252
url: https://arxiv.org/abs/2309.16352v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.result
---

# The cross-integral bound for continuous-time walks on two cycles

## Problem

S. Dhamapurkar and X.-H. Deng, *Quantum walk mixing is faster than classical on periodic lattices*, Physica A 630, 129252 (2023), arXiv:2309.16352v1, Conjecture 1 in its case d = 2 (Eq. (15)):

> $\left| \int_{0}^{T} n_1(t) n_2(t) dt \right|\leq 32 n_1(n_2 \log(n_2))^2+ 32 n_2(n_1 \log(n_1))^2$

for odd, relatively prime cycle orders $n_1 > n_2$. Here $n_i(t)$ is the time-dependent part of the transition amplitude product on $\mathbb{Z}_{n_i}$, Eq. (B8): $n(t) = \sum_{j \neq k,\, j+k \neq n} e^{-it\sin(\pi(j+k)/n)\sin(\pi(j-k)/n)} w^{l(j-k)}$ with $w = e^{2\pi i/n}$ and displacement $l$. The verbatim statements are in [the literature note](../Library/QuantumChannels/dhamapurkar2023latticemixing.md).

Issue [#18528](https://github.com/the-omega-institute/trureturing/issues/18528) fixes the reading: the bound for all odd coprime $n_1 > n_2$, all displacements and every $T \ge 0$. This is refuted.

## Motivation

The paper's mixing-time theorem for the walk on $\mathbb{Z}_{n_1} \times \mathbb{Z}_{n_2}$ (Theorem 0.5) uses Eq. (15) to control the cross term of the time-averaged transition probability. The source supports it by simulations for odd coprime pairs in [10, 200].

## Gap

Issue #18528 records the literature check before any Lean:
- arXiv v1 is the only version; the published version was not read;
- the one citing work listed by Semantic Scholar, arXiv:2304.01572, read in full, cites the paper once in a list of references;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Take $n_2 = 10^{10} + 1$, $n_1 = 10^{10} + 3$, $l_1 = l_2 = 1$ and $T = 1$, and write $A_n(t) = \sum_{j<n} e^{i(t/2)\cos(2\pi j/n)} w^j$.
1. **The identity.** For odd n ≥ 3, $n_1(t) = |A_n(t)|^2 - (n - 1)$: the full double sum is $|A_n(t)|^2$, the diagonal contributes n and the antidiagonal $j + k = n$ contributes −1.
2. **Early times.** For odd n ≥ 3 and $0 < t \le 1$, $\operatorname{Im} A_n(t) \ge nt/8$, from $\sin u \ge u/2$ on $[0, 1/2]$ and $\sum_j \cos^2(2\pi j/n) = n/2$. So $|A_n(t)|^2 \ge n^2/256$ on $[1/2, 1]$.
3. **The integral.** With $0 \le |A_{n_i}|^2 \le n_i^2$, $\int_0^1 n_1 n_2 \ge n_1^2 n_2^2/131072 - (n_1 - 1)n_2^2 - (n_2 - 1)n_1^2 \approx 7.63 \cdot 10^{34}$.
4. **The comparison.** $\log n_1 < 24$, so the right side of Eq. (15) is at most $\approx 3.69 \cdot 10^{34}$.

## Falsifier

The theorem would not refute the conjecture if the module's quantities differed from the source's. The module takes:
- Eq. (B8) literally, with the excluded pairs $j = k$ and $j + k = n$, the phase sign and $w^{l(j-k)}$;
- the norm of the complex integral over [0, T], the natural logarithm and the hypotheses of Conjecture 1;
- T = 1, which the conjecture covers: it bounds the integral up to an arbitrary T, and the source plots it as a function of T.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.lean` (429 lines).
- **Definitions.** It defines `walkTerm` and `claim`, and proves `result : ¬ claim`.
- **Reuse.** It uses:
  - the sine-square sum `sum_sin_sq` of `EndAmplitudeCosineSumZeros`, made public at that owner by removing `private` and re-pinned;
  - Mathlib's interval integral, exponential and sine bounds, and geometric sums of roots of unity.
- **Escape registration** of the owner theorem: `Reg/D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.lean` (`sum_sin_sq`, `declared_validated`). `result` is the designated refutation result and is exempt.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/LatticeWalkCrossIntegralRefutation.lean.json`, statement `sha256:14eabca2ccbfed8c8c941f068102551aec240b6aef49780fc59ed88c3689f199`.

Declaration statements:
- `result`: `sha256:84dea8368d99f986d3e77b2460e35d14655b83d6540e53dad9aa1e032dbf6a1c`;
- `claim`: `sha256:f0b93a62bd0a8feb077abe2c9ce65e4d56fb6875b8df6a23c602614580a025ce`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #18528 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the identity, the early-time bound, the integral comparison and the numerical comparison are instantiations of existing lemmas and finite normalization | open-problem-resolution |
| `walkTerm`, `claim` | bind-only | none | definitions used by `claim` |
| the identity, amplitude, integral and comparison helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |
| `EndAmplitudeCosineSumZeros.sum_sin_sq` (made public) | bind-only (consumed by its owner and on the proof path of `result`) | none | consumed helper |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. `result` refutes the closed `claim` at one explicit instance, so `utility` is `certified-instance` with `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Eq. (15) fails at $n_2 = 10^{10} + 1$, $n_1 = 10^{10} + 3$, $l_1 = l_2 = 1$, $T = 1$.

**Computed, not formalized** (orchestrator, recorded in #18528):
- $n(t) = |A_n(t)|^2 - (n - 1)$ to $1.5 \cdot 10^{-12}$ for odd $n \le 101$;
- $\operatorname{Im} A_n(t)/(nt/8) \ge 1.94$ on (0, 1] for $n$ up to 100 001;
- for $(n_1, n_2) = (201, 199)$, $\int_0^1 n_1 n_2 \approx 8.6 \cdot 10^5$, far below the bound, consistent with the source's numerics.

**Argued, not formalized.**
- *Mechanism.* Before the walk spreads, the amplitude to a neighbouring vertex is coherent: $A_n(t)/n \to i J_1(t/2)$ as $n \to \infty$, so $n_1(t)$ is of order $n^2$ for $t$ of order 1. The cross integral therefore grows like $n_1^2 n_2^2$, while Eq. (15) allows only order $n^3 \log^2 n$. With the limiting constant $\int_0^1 J_1(t/2)^4\,dt \approx 1/1400$, the violation at $T = 1$ sets in for $n$ of order $10^7$, beyond the source's range $[10, 200]$.
- *The application time.* The search seat argues that the family $n_2 = 2^k + 1$, $n_1 = 2^k + 3$ ($k \ge 60$) violates Eq. (15) also at the time $T = 1600(n_1 + n_2)(\log n_1)^2$ used in Theorem 0.5. Its argument needs a proof of the one-factor bound of the source's Lemma 0.4.
- *Effect on Theorem 0.5.* Its proof uses Eq. (15), so the claimed mixing time for $\mathbb{Z}_{n_1} \times \mathbb{Z}_{n_2}$ is not established by the source's argument. Whether the mixing time itself holds (the source's Conjecture 2) is not addressed here.
- *A repaired form.* The early-time term suggests bounding the cross integral by $C n_1^2 n_2^2 + O(n^3 \log^2 n)$, or restricting to $T$ beyond the spreading time with the early part treated separately. Neither is proved here.

**Effect on the paper.** Conjecture 1 in its case d = 2, as stated, is false. The mixing-time result for two cycles needs a different control of the cross term.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published version of the paper was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
