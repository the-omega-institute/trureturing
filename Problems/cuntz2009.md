---
slug: cuntz2009
bibkey: cuntz2009integralmodulardata
doi: 10.1007/s10801-008-0139-y
url: https://arxiv.org/abs/math/0611233v2
triage: theorem
motivation_gids:
  - D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result
---

# Cuntz's integral Fourier zero-free column question

## Problem

Michael Cuntz, *Integral modular data and congruences*, Section 7, Question (5), arXiv:math/0611233v2 p. 21, journal p. 380, asks:

> Does an integral Fourier matrix $s$ exist with a column $k$ such that $\forall i$ $s_{ik}\ne0$ and $\exists i$ $s_{ik}\ne\pm1$?

The answer is negative for the exact existential assertion. Preregistration: [#22614](https://github.com/the-omega-institute/trureturing/issues/22614). The source note is [Cuntz](../Library/Fourier/cuntz2009integralmodulardata.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive finite size and an integer square matrix | `claim` quantifies `n`, `hn`, `s` | All sizes; source indices $1,\ldots,n$ correspond to `Fin n`, with source index one represented by zero. |
| Definition 4.1(1): first column one and nonzero determinant | First two conjuncts of `FourierAxioms` | Integer determinant, unchanged. |
| Definition 3.1: positive square roots | Third conjunct of `FourierAxioms` | Every square root is positive. |
| Definition 4.1(2): $ss^T=\operatorname{diag}(d)$ | Fourth conjunct of `FourierAxioms` | Exact integer-to-real cast; $d$ is existentially quantified by `IsIntegralFourierMatrix`. |
| Definition 4.1(3): $\sqrt{d_j}s_{ij}=\sqrt{d_i}s_{ji}$ | Fifth conjunct of `FourierAxioms` | Every pair of indices. |
| Definition 4.1(4): integral structure constants | Sixth conjunct of `FourierAxioms` | Every triple; each real sum equals an integer witness. |
| A zero-free column containing a nonunit | Final witnesses of `claim` | Every entry nonzero and some entry different from both $1$ and $-1$. |
| Negative answer | `result` | The exact negation of `claim`. |

Definition 4.1 names integral Fourier matrices before adding congruence conditions (5)–(6); neither these conditions nor a $T$-matrix is required. The matrix equation fixes row norms. The reversed indices in Definition 3.1's explanatory norm sum are not an additional hypothesis. No extra binder or conjunct weakens the source question.

## Motivation

A zero-free column is necessarily a sign vector. The obstruction follows from orthogonality, normalization and integrality, independently of the source's further structure.

## Gap

The source presents Question (5) as open. The literature screen recorded in #22614 located no full settlement within its searched scope. Its completeness is ASSUMED-UNVERIFIED.

### Literature status

The preregistration records a Semantic Scholar list of eight citing works, seven screened and one inaccessible publisher PDF, against eleven citations reported by OpenAlex. OpenAlex citing-work and author queries returned HTTP 429. Cuntz's arXiv author list supplied 51 records; later relevant papers 0704.2384 and 0809.5186 were read in relevant parts. The matrix-specific searches included Singh's 1610.05353 and 1610.05763. Broad arXiv result sets and later papers unrelated by title and abstract were not exhaustively read. Google returned interstitial pages, which supply no absence evidence. These are attributed preregistration readings, not a new exhaustive literature search.

## Route

Let $A$ be the real cast of $s$ and $D=\operatorname{diag}(d)$, with $d_i>0$. Since $AA^T=D$,

$$A(A^TD^{-1})=I,\qquad (A^TD^{-1})A=I.$$

The second identity follows from the first for square matrices. Its diagonal entries give

$$\sum_i\frac{s_{ik}^2}{d_i}=1.$$

The first column is one, hence $\sum_i1/d_i=1$. In a zero-free integer column, every square is at least one. Equality of the two positive weighted sums forces every square to be one. The private helpers `weighted_column_squares`, `positive_weight_integer_square_rigidity` and `zero_free_column_units` implement this argument and are consumed by `result`.

## Falsifier

The refutation would fail if a square integer matrix satisfying the stated axioms had a zero-free nonunit column. The kernel-checked `result` excludes precisely this existential assertion. Rational entries, an unnormalized first column or a rectangular matrix lie outside the surviving rigidity statement.

## Evidence

Settling node: `D5/S3/Fourier/CuntzZeroFreeColumnRefutation.result`. The claim has type `Prop` and the result has type `Not claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). It is the only public theorem; all three proof helpers are private.

### Experiment entry

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/24cdaf67b657be7d3d325e35b345349a99ce0755/docs/reports/cuntz-integral-fourier-zero-free-column/), script `check.py`, command `python3 check.py`, exit 0. Script SHA-256: `55dd994bb876901a2ee5d0f4be187ac928c6006a9aadfdd394c838b2b4bbb1ea`. Final reading: `ALL_CHECKS_OK`. The script uses exact integer and rational arithmetic. The readings below concern the pinned script and its stated finite scope.

## Triage

### What the settlement shows

1. **Proved, kernel-checked — exact negative answer.** `result` refutes the unchanged positive-size existential assertion in Section 7(5).

2. **Proved, kernel-checked — surviving general statement.** Private `zero_free_column_units` treats arbitrary square integer matrices whose first column is one and whose row Gram matrix is diagonal with positive entries. It does not require a determinant premise, symmetrization, fusion integrality or $T$.

3. **Proved, kernel-checked — mechanism.** Private `weighted_column_squares` proves the weighted column-square sum equals one. `zero_free_column_units` specializes this to the first column to obtain the reciprocal-norm sum. Private `positive_weight_integer_square_rigidity` forces a nonzero integer column to have every square one by equality of positive weighted sums.

4. **Computed — source example and finite enumeration.** The experiment entry checks the source's 13-dimensional example, all $13^3=2197$ structure constants, Fourier equations (1)–(4) and congruence conditions (5)–(6). It enumerates square integer matrices of sizes $1,2,3,4$ with entries in $[-2,2]$, first column one and mutually orthogonal rows, up to row permutation: respectively $1,1,8,26$ matrices, $36$ total. Every matrix passes the weighted Gram, reciprocal-norm, balance and zero-free-column checks.

5. **Computed — necessary structural boundaries.** Exact checks verify orthogonality and zero-free nonunit columns for rational rows $(1,7/5),(1,-5/7)$, unnormalized integer rows $(1,2),(2,-1)$, and rectangular integer rows $(1,1,2),(1,1,-1)$. These show why each named condition of the general helper matters; they are not Fourier-matrix counterexamples.

6. **Computed — zero/excess balance.** Throughout the enumeration window and the source example, the script checks

   $$\sum_{i:s_{ik}=0}\frac1{d_i}=\sum_{i:|s_{ik}|\ge2}\frac{s_{ik}^2-1}{d_i}.$$

   A universal balance theorem is not formalized here. The identity is explained by separating zero, unit and larger-square terms in the weighted sum; the asserted computational coverage is only the finite window and source example.

7. **Open — classifications and further source questions.** Equal-norm classification, classification of all Fourier matrices and existence of a $T$-matrix are not settled. The argument imposes no change on the source's proved results and supplies no classification or $T$ construction. A question asking for an example of the excluded zero-free nonunit type has no witness; other questions require their own arguments.

8. **Open — exhaustive literature absence.** No full settlement was located within the preregistration's searched scope. Unread or inaccessible sources and later unindexed results remain outside that claim.

## ASSUMED-UNVERIFIED

Completeness of the external literature screen is ASSUMED-UNVERIFIED. Literature readings are attributed to the preregistration producers. The finite checker does not prove an unbounded enumeration, the universal balance identity, either classification, or existence of $T$.
