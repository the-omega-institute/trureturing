---
slug: braun-bruegge-2022-symmetric-edge-polytope-facet-sum-conjecture-5-1
bibkey: braunbruegge2023facetsymmetricedgepolytope
doi: null
url: https://arxiv.org/abs/2201.13303v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture.result
---

# Braun–Bruegge Conjecture 5.1

## Problem

B. Braun and K. Bruegge, *Facets of Symmetric Edge Polytopes for Graphs with Few Edges*, arXiv:2201.13303v4, Conjecture 5.1 (Conjecture 3.15 in v1), asks for two endpoint maxima and two monotone transfers of the facet sum from Proposition 4.4. The verbatim statement is recorded in #19695 and the cited Library note.

For sorted positive natural numbers $a\ge b\ge c$ of common parity, the literal source specialization is

$$
F(a,b,c)=\sum_{j=0}^{c}\binom cj\binom b{(b-c)/2+j}\binom a{(a-c)/2+j}.
$$

The natural divisions are exact on this domain. Outside it, the Lean definition remains a total natural-valued expression; the conjecture asserts nothing there.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Proposition 4.4, three entries, ordered and of common parity | `F`, `Admissible` | The sum and the five domain conjuncts are literal binding conventions. |
| $n=2k$, $k\ge2$, sum $n+1$, maximum at $(n-1,1,1)$ | `result.1` | Every admissible triple with that sum is bounded by the endpoint. |
| $n=2k-1$, $k\ge3$, sum $n+1$, maximum at $(n-3,2,2)$ | `result.2.1` | Natural subtraction has the source value under the stated bound on $k$. |
| Transfer from the third coordinate | `result.2.2.1` | $c\ge3$ makes $(a+2,b,c-2)$ positive and sorted. |
| Transfer from the second coordinate, preserving order | `result.2.2.2` | The additional condition $c\le b-2$ is exactly preservation of the lower order inequality. |

The endpoint triples themselves satisfy the domain and sum conditions. There are no additional hypotheses on the four assertions.

## Motivation

The endpoint bounds describe the extremal facet counts for the three-coordinate family, while the transfers identify how the count responds to increasing imbalance. The source's Theorem 4.9 states a different upper bound by $M(n)$; it is not on this module's dependency path and is not re-proved here.

## Gap

The source labels all four assertions as a conjecture in v1–v4. The literature screen recorded in #19695 inspected relevant passages of Braun–Bruegge–Kahle (arXiv:2204.07239v4), Mori–Mori–Ohsugi (arXiv:2312.11287v3 and arXiv:2511.22981v2), D'Alì–Juhnke-Kubitzke–Koch (arXiv:2307.04933v1), and Cuchilla et al. (arXiv:2507.18846v2), without finding a settlement. Two citing full texts and several later author papers remain uninspected. No MathDB page or google-deepmind/formal-conjectures entry was located in that screen. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The proof uses centered binomial rows. At a distance $r$ from the center, the row is $\binom m{(m-r)/2}$ when $r\le m$ and the parities agree, and is zero otherwise. Reflection combines the two signs of the distance, with multiplicity one at zero and two elsewhere.

Vandermonde preserves the mass of the product of the receiver and donor rows under $(a,c)\mapsto(a+2,c-2)$. The difference of those products is nonnegative near the center and nonpositive farther away. The remaining centered row is nonincreasing with distance. Subtract its minimum weight on the positive-difference support: each weighted difference becomes nonnegative, and the subtracted constant contributes zero by mass preservation. This proves the transfer inequality. Strong induction on the two smaller coordinates reduces to the endpoint triples.

The original private binomial monotonicity declaration `choose_le_of_middle` is used through `open private` from `D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound`; its source is unchanged. Mathlib's binomial identities and finite-sum lemmas supply the algebraic and summation steps. These are consumed applications, not separate escape-witness admission.

## Falsifier

The four inequalities must hold for all admissible natural triples, with the two endpoint ranges and the second transfer's order constraint intact. A proof only for bounded triples, or only for weights at least three, would not establish the endpoint reductions. A registration of a projected inequality alone would not audit the complete conjunction.

## Evidence

The settling declaration is `D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.result`. Its proposition is `claim`, with all four source assertions. Public definitions are `F`, `Admissible`, and `claim`; the transfer and normalization lemmas are private and consumed.

| Public theorem | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `D5.S3.Combinatorics.BinomialBases.BraunBrueggeFacetSumConjecture.result` | bind-only | none | open-problem-resolution (#19695; Proved) |

The ratio, crossing, mass and weighted-transfer assertions are classified conservatively as bind-only under the repository's normalization rule. This delivery claims settlement of the external named problem, not a separately admissible general content module. Its utility classification is `none`: the Lean statements are symbolic; finite computation only corroborates them.

The escape audit for `result` is unfinished: [#20246](https://github.com/the-omega-institute/trureturing/issues/20246). Missing evidence is a lawful typed registration of the original complete conjunction, including source reconstruction, equivalence, variation, sensitivity and observational dependence. No registration is labelled `declared_validated`.

### Finite corroboration

[Experiment directory at commit `01e2c5c35eea4026e363dc01694bafc7d98f7e53`](https://github.com/the-omega-institute/trureturing-experiments/tree/01e2c5c35eea4026e363dc01694bafc7d98f7e53/docs/reports/braun-bruegge-2022-symmetric-edge-polytope-facet-sum-conjecture-5-1).

Command: `/opt/homebrew/bin/python3 /Users/auric/trureturing-experiments/docs/reports/braun-bruegge-2022-symmetric-edge-polytope-facet-sum-conjecture-5-1/check.py`; exit 0. Script SHA-256: `d08ed56843e46ff9d0d3bc6dd547cad7a9905a3aa67a44cc00df61759d80fe30`.

The checker tests 58,088 admissible triples with $4\le n\le200$, verifying both endpoint bounds and both applicable transfers. It checks mass zero and the transfer-difference sign pattern for common-parity pairs $3\le c\le a<60$. It computes $F(9,1,1)=252$ and $F(8,2,2)=392$. These are finite computations, not the universal proof.

## Triage

- **Proved, kernel-checked:** `result` establishes all four assertions with the binding definitions unchanged.
- **Proved, kernel-checked:** the transfer mechanism is expressed by the private `delta_identity`, `delta_single_crossing`, `pair_mass_transfer`, and `centered_transfer`, consumed by `first_transfer`, `second_transfer`, and `result`.
- **Proved, kernel-checked:** the private `maximum_of_transfers` and `result_of_transfers` cover the endpoint reductions, including final donor steps $3\to1$ and $4\to2$; `result` gives the two maxima. No extra lower bound of three is imposed on the remaining weight in `centered_transfer`.
- **Computed:** the experiment entry gives the exact tested ranges, 58,088 triples, sign pattern and the two values. A numerical extension beyond those tested ranges is open as a computation; the four universal assertions are proved by `result`.
- **Admission assessment:** open-problem-resolution (#19695; Proved), with literature completeness `ASSUMED-UNVERIFIED`. The symbolic declarations have utility `none`.
- **Escape-witness assessment:** bind-only, conservatively, for the ratio/single-crossing/weighted-transfer assertions and their composition. No separate general-module admission is claimed. Four-slot audit evidence is unfinished under #20246.
- **Open:** complete the remaining literature screen. The uninspected citing works and later-author papers prevent a completeness claim.

### What the settlement shows

**Proved, kernel-checked:** the decisive mechanism is the equal-mass, single-crossing comparison combined with an antitone weight, instantiated in the centered rows and consumed by `result`. The proof handles arbitrary natural parameters in the stated sorted common-parity domain, including the endpoint chains; it is not bounded by the experiment.

**Proved in prose:** for $k\ge2$, expanding the two terms at $(2k-1,1,1)$ gives $2\binom{2k-1}{k-1}=\binom{2k}{k}$ by reflection and Pascal's identity. For $k\ge3$, expanding the three terms at $(2k-4,2,2)$ gives
$\binom{2k-4}{k-3}+4\binom{2k-4}{k-2}+\binom{2k-4}{k-1}=2\binom{2k-4}{k-3}+4\binom{2k-4}{k-2}$ by reflection. These closed forms explain the extremal values; no additional Lean theorem is asserted for them.

**Open:** equality classification, strictness of the transfers, mixed-parity triples, and extensions to more than three coordinates. The proved maximum inequalities do not assert uniqueness. The source's other results, including Theorem 4.9, retain their stated scope; this module supplies the four conjectural inequalities and makes no new claim about their dependency proofs.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the recorded search is partial, and absence of a hit does not prove novelty. The escape audit has the concrete missing evidence listed in #20246. The mathematical theorem's axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
