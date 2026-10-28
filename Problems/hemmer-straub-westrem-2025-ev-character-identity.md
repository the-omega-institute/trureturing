---
slug: hemmer-straub-westrem-2025-ev-character-identity
bibkey: hemmerstraubwestrem2025riordan
doi: 10.37236/14401
url: https://arxiv.org/abs/2509.02796v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result
---

# The Hemmer–Straub–Westrem Ev character identity

## Problem

Hemmer, Straub and Westrem, *New identities in the character table of symmetric groups involving Riordan numbers*, arXiv:2509.02796v1, Conjecture 2.3, equation (2.4), asks whether, for every partition $\lambda\vdash n$,

$$
\sum_{\widetilde\lambda\in\operatorname{Ev}(\lambda)}
\sum_{\mu\in R_3(2n)}(-1)^{\ell(\widetilde\lambda)}
\chi^\mu_{\widetilde\lambda}
=\sum_{\widetilde\lambda\in\operatorname{Ev}(\lambda)}
\chi^{(n,n)}_{\widetilde\lambda}.
$$

The statement here has $n\geq1$. Each occurrence of a part $a$ independently contributes either $(2a)$ or $(a,a)$; coincident cycle types retain multiplicity. The set $R_3(2n)$ consists of decreasing triples of even natural numbers with sum $2n$, including zero padding. Section 6 asks for the extension from single part sizes to all partitions. The journal version is Electronic Journal of Combinatorics 33(1) (2026), P1.57, DOI 10.37236/14401. Preregistration: [#17766](https://github.com/the-omega-institute/trureturing/issues/17766).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Every partition of positive size | `claim`: every natural `n`, `1 ≤ n`, and `lam : Nat.Partition n` | Positive parts and their sum follow from the partition type. |
| Power-sum product | `powerSumProd` | Product of Mathlib's three-variable `MvPolynomial.psum`, with repeated parts retained. |
| Frobenius character formula | `vandermonde3` and `frobChar` | The coefficient at the partition plus $(2,1,0)$ of the Vandermonde times the power-sum product. |
| Independent doubling choices | `evTypes` | Both recursion branches and the empty-list case retain multiplicity. |
| Even partitions with at most three parts | `R3` | Fixed-sum triples, decreasing order, and all entries even. |
| Sign and two-row character | `claim` | The sign is the integer $(-1)^{\operatorname{length}(\tau)}$; $(n,n)$ is padded by zero. |
| Equality (2.4) | `result : claim` | No single-part-size or sorting hypothesis. |

The identification of `frobChar` with the ordinary irreducible character is the classical Frobenius formula, attested through the source's Lemma 3.1 and Stanley's Corollary 7.17.4. This representation-theoretic identification is a literature input, not a Lean construction of representations or Specht modules. The public definitions retain the preregistered coefficient conventions, with the polynomial-first coefficient API.

## Motivation

`D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result` proves the coefficient identity for every partition of every positive size. Under the stated Frobenius interpretation, it settles the $N=1$ version of Conjecture 2.3, including mixed part sizes. Its admission basis is `open-problem-resolution (#17766; Proved)`; there is no anchor atom.

## Gap

The source establishes the single-part-size case. The preregistration's source and citation checks found no general settlement in the searched literature. Westrem's dissertation, DOI 10.37099/mtu.dc.etdr/1892, was not read in full. The Internet Archive capture of its landing page from 2025-08-21 has an abstract describing a Chapter 4 proof that a special case of the alternating Ev sum vanishes; it indicates no general proof of Conjecture 2.3. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For an ordered list of positive parts $a_1,\ldots,a_r$ of sum $n\geq1$, put

$$
P(X)=\prod_{i=1}^r(X^{2a_i}+X^{a_i}+1),\qquad
Q(t)=\prod_{i=1}^r(t^{a_i}+1+t^{-a_i}).
$$

The private theorems `ev_minus` and `ev_plus` express the two Ev sums through products of $p_a^2-p_{2a}$ and $p_a^2+p_{2a}$. The factor identity `minus_factor` and the symmetric homogeneous coefficient detector `coefficient_detector` give `left_coefficient`. The two-variable specialization and `alt_boundary_homogeneous` give `right_coefficient`. Both equal

$$
2^r\bigl([X^n]P-[X^{n+1}]P\bigr).
$$

The private theorem `list_identity` equates the Ev sums for every such ordered list, and `result` applies it to partition parts. These are declarations of `D5.S3.Combinatorics.Partitions.HemmerStraubWestrem`; all are on the settling proof's dependency path.

In Laurent notation, $P(t)=t^nQ(t)$ and $Q(t)=Q(t^{-1})$. Therefore $[X^n]P=[t^0]Q$ and $[X^{n+1}]P=[t^1]Q=[t^{-1}]Q$, giving $[X^n]P-[X^{n+1}]P=\operatorname{CT}((1-t)Q)$. This conversion is proved here in prose; Lean checks the equivalent ordinary-polynomial coefficient difference.

## Falsifier

A counterexample would be a positive-size partition for which the two coefficient sums in `claim` differ. The coefficient theorem is kernel checked. A failure of the literature-based interpretation of `frobChar` would concern the representation-theoretic bridge, which is outside the formalized coefficient theorem.

## Evidence

Formal source: [HemmerStraubWestrem.lean](../D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.lean). The public theorem is `D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.result`; its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The module imports only pinned Mathlib and has `generality: G`, `utility: none`.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c2f9851db34fcbf5f7ef46049604108d99e12a6a/docs/reports/hemmer-straub-westrem-2025-riordan-character-identity). Command: `git -C /Users/auric/trureturing-experiments show c2f9851db34fcbf5f7ef46049604108d99e12a6a:docs/reports/hemmer-straub-westrem-2025-riordan-character-identity/check.py | python3 -I`; exit 0. Script SHA-256: `37086ef7b63625069d023b791acf4d231a5c737a0fc2c55ce87af4cef89f8bab`. All 194 partitions with $1\leq n\leq11$ satisfy the identity and the common constant-term formula. All 192,914 character pairs used agree between Murnaghan–Nakayama and Frobenius coefficient calculations. The common values include $-4$ for $(2,1)$, $12$ for $(2,2)$, $48$ for $(1,1,1,1)$, and $16$ for $(4,3,2,1)$. These are finite computations, not a proof of the unbounded identity.

The four-slot escape audit of `result` is unfinished: [#18551](https://github.com/the-omega-institute/trureturing/issues/18551). The missing evidence is an HSW-specific dependent-family reconstruction, exact source selection, statement-to-law bridge, variation, sensitivity and actual observational dependence. No Reg mirror or `declared_validated` registration is claimed.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Kernel-checked coefficient form: `left_coefficient`, `right_coefficient`, `coefficient_detector`, `minus_factor`, `ev_minus`, `ev_plus` | Both Ev sums equal $2^r([X^n]P-[X^{n+1}]P)$. The Laurent constant-term expression follows by the prose derivation in Route; it is not a separate Lean statement. |
| Strength | Kernel-checked: private `list_identity` | Every ordered list of positive integers with positive sum satisfies the identity. Sorting and the single-part-size restriction are unnecessary. |
| Consequence for Conjecture 2.3 | Kernel-checked: public `result` | The preregistered $N=1$ coefficient identity holds for all positive-size partitions. The character interpretation uses the literature bridge described above. |
| Consequence for weighted sums | Proved in prose | Multiplying the pointwise equality by any chosen weights and summing over a finite set of partitions preserves equality by distributivity. This supplies the pointwise input to the source's $N=1$ weighted-sum questions; it supplies no closed evaluation of the remaining partition sum. |
| Neighbouring questions | Open | The $N\geq2$ identities, the closed form of Conjecture 6.1, and explicit bijective proofs are not settled here. |
| Experiment | Computed | Exactly the 194 partitions with $1\leq n\leq11$ and the 192,914 character comparisons in Evidence. |
| Literature | Literature reading; completeness `ASSUMED-UNVERIFIED` | The preregistration's source and citation screen and the dissertation landing-page abstract support the bounded literature status in Gap. The dissertation full text is unread. |

## ASSUMED-UNVERIFIED

Literature completeness remains unverified, including the unread dissertation full text. The classical character interpretation is cited literature, not a Lean theorem. Bounded reuse probes that exhausted their search budgets do not establish absence of all stronger owners. The unfinished four-slot escape audit is tracked by #18551 and does not assert a validated registration.
