---
slug: op-onn2023good
bibkey: onn2023supmodular
doi: 10.48550/arXiv.2309.07700
url: https://arxiv.org/abs/2309.07700v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount.result
---

# Onn's good-permutation count and characterization

## Problem

Shmuel Onn, *On Supmodular Matrices*, arXiv:2309.07700v1, Section 2, page 4, immediately before Lemma 2.2, asks:

> An interesting question suggested by a referee is to count and characterize, for every $m$ and $n$, those permutations which are good for all $1\leq i<m$ and $1\leq j<n$.

The source defines goodness by the four entries of each adjacent square: the maximum is on one main diagonal and the minimum is on the other diagonal. The settlement uses rank arrays represented by equivalences $(\mathrm{Fin}\ m \times \mathrm{Fin}\ n) \simeq \mathrm{Fin}(mn)$ and the source's one-based labels.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every positive natural pair $(m,n)$ | `claim` quantifies $m,n : \mathbb{N}$ with $0<m$ and $0<n$ | All positive dimensions and both orientations are included. |
| Good at every adjacent square | `D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.Good` | The four-entry maximum/minimum condition is literal. |
| Count of good permutations | `goodCount m n = proposedCount m n` in `claim` | The counted object is the finite subtype of rank-array equivalences satisfying `Good`. |
| Characterization in every dimension | `Good σ ↔ Structure σ` in `claim` | `Structure` contains the one-dimensional, two-row, transposed two-column, and $3\times3$ cases. |
| Two-row chain description | `TwoChains` and `two_good_iff` | The split index includes $k=0$ and $k=n$. |
| Three-by-three alternatives | `TypeA`, `TypeB`, and `three_good_iff` | The center and both ordered-chain alternatives are retained. |
| No positive enumeration in the general count | `rowsEvenEquiv` and `count_two` | The two-row count is obtained from even subsets and the parity theorem. |

## Motivation

The source establishes which dimensions can admit universal good permutations and asks for the missing count and characterization. The proof identifies an order-theoretic mechanism: the column signs of a good two-row array have a unique split, with at most one adjacent sign change, and overlapping local squares constrain the three-row case. This gives a uniform description of the positive cases and a finite exact count for the exceptional $3\times3$ case.

## Gap

The source question leaves the count and complete characterization unstated. The final journal text and complete later-literature comparison were not accessible; literature completeness is recorded as `ASSUMED-UNVERIFIED`.

## Route

The supporting module proves the local sign split, two-chain characterization, transposition, the $3\times3$ local alternatives, and the large-rectangle obstruction. The settling module constructs the bijection between two-row rank arrays and even subsets of $\mathrm{Fin}(2n)$, counts the two $3\times3$ types as $36$ each, and combines the cases into `result`.

The source's parity count is reused from `D5.S3.Combinatorics.SubsetSpectrum.parity_counts`, whose owner is repinned in this delivery. The experiment is corroborative evidence and supplies no premise of the Lean proof.

## Falsifier

A counterexample to the local sign split, a missing two-row chain arrangement, an additional $3\times3$ type, or a good array in a dimension excluded by the overlapping-block obstruction would falsify the corresponding declaration. The independent finite checks test these mechanisms through their stated finite ranges.

## Evidence

The settling declaration is `D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount.result : claim`, and its Scribe node carries `OpenProblemResolutionClaim` with resolution `Proved` for this dossier. The settling module has `generality: I`, `utility: none`, and admission basis `open-problem-resolution (#26707; Proved)`. The supporting module has `generality: I`, `utility: none`, and escape-witness admission basis.

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/0ef78b1c4735982a86a1626e00b2f727bbbd9295/docs/reports/onn-2023-good-permutation-enumeration), file `check.py`, at commit `0ef78b1c4735982a86a1626e00b2f727bbbd9295`. The referenced blob exists at that revision and its SHA-256 is `bfc565ffaac0ef0e7b24b2885ca285692ffa2648b679ca01840aa0e373bc0e82`. Running `python3 check.py` from `/tmp/op-onn2023good/rework4` exits 0 and ends with `ALL_CHECKS_OK`. It checks all 35 positive ordered dimension pairs with $mn\leq12$, two-chain equality in both orientations for widths $1$ through $6$, and an independent unpruned $9!$ classification.

The escape audit is unfinished for the public theorem targets named in [issue #30704](https://github.com/the-omega-institute/trureturing/issues/30704). No four-slot registration is claimed validated.

## Triage

1. **Proved — Mechanism.** Local sign constraints forbid a negative-to-positive transition. The unique split cuts the two rows into disjoint increasing chains and includes the endpoint splits with one empty chain. Evidence: kernel-checked `D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.pairgood_sign_split` and `pairgood_iff_chains`.
2. **Proved — Uniform count.** Good two-row rank arrays are equivalent to even-cardinality subsets of $\mathrm{Fin}(2n)$ for every positive width; no positive enumeration is used. Evidence: kernel-checked `D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount.rowsEvenEquiv` and `count_two`, using the repinned `D5.S3.Combinatorics.SubsetSpectrum.parity_counts`.
3. **Proved — Dimension three.** Four compatible local squares give exactly `TypeA` or `TypeB`; each has center label $5$ and two independent ordered two-chain interleavings, giving $36+36$. Evidence: kernel-checked `three_good_iff`, `typeA_center`, `typeA_card`, `typeB_card`, and `count_three`.
4. **Proved — Known obstruction.** Overlapping $3\times3$ blocks rule out $3\times4$ and larger rectangles, with transposition covering the opposite orientation. Evidence: kernel-checked `no_three_four`, `no_good_large`, and `result`.
5. **Proved — Extent.** The sign-split and local-compatibility lemmas use arbitrary natural-valued rows and arrays under their adjacent-distinctness hypotheses, beyond the finite rank-label specialization. Evidence: kernel-checked `pairgood_sign_split`, `three_local_iff`, and `no_three_four`.
6. **Computed — Finite corroboration.** The pinned experiment checks all 35 positive ordered dimension pairs with $mn\leq12$, two-chain exact set equality in both orientations for widths $1$ through $6$, and an independent $9!$ classification. Command: `python3 check.py` (working directory `/tmp/op-onn2023good/rework4`); exit 0; script SHA-256 `bfc565ffaac0ef0e7b24b2885ca285692ffa2648b679ca01840aa0e373bc0e82`; final line `ALL_CHECKS_OK`.
7. **Open — Surviving neighbours.** The settlement does not settle the covering number $p(m,n)$, existence of non-permutable real matrices, decision complexity, or analogous counts allowing tied labels. Evidence: no declaration in this delivery states any of these claims.
8. **Open — Novelty.** Published priority remains unverified because the final journal text and complete follow-up coverage were not accessible. Evidence: the literature screen recorded in issue #26707 and the Library note; the missing comparison is explicit.

### What the settlement shows

**Kernel-checked:** `result` proves the count and characterization in every positive dimension. The decisive mechanism is the unique two-row split, including the endpoints, the even-subset bijection, the two compatible $3\times3$ types, and the overlapping-block obstruction. **Computed:** the finite corroboration has exactly the range stated in item 6. **Open:** the surviving neighbouring questions and complete literature-priority comparison remain outside this settlement. No change to other source results is claimed.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The arXiv source and its cited definitions were read, but the final journal text and complete follow-up coverage were not accessible. No worldwide-priority claim is made.
