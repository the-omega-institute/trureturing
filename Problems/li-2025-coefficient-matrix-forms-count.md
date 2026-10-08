---
slug: li-2025-coefficient-matrix-forms-count
bibkey: li2025genuinely
doi: 10.48550/arXiv.2510.16561
url: https://arxiv.org/abs/2510.16561v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.result
---

# The coefficient matrix of a 2p-term separable qubit state has 2^(p-1) forms

## Problem

D. Li, *A necessary and sufficient condition for genuinely entangled n-qubit states with six non-zero
coefficients*, arXiv:2510.16561v1, Section 6, closes with the question: "What to do next is how to find
the forms of the corresponding coefficient matrices. When $m=4$, there are two forms [Li-24]. When $m=6$,
there are four forms. How many forms of the corresponding coefficient matrices are there when $m=2p$?"
Here an $n$-qubit state with $m=2p$ non-zero coefficients $b_i$ on basis states $B_1<\cdots<B_m$, $p$
prime, is separable and not trivially separable. It factors as a two-term state with complementary strings
on qubits $p_1<\cdots<p_k$ times a $p$-term state on the remaining qubits, and its corresponding
coefficient matrix is the $2\times p$ array $(\alpha_r\beta_j)$, whose entries are the $b_i$. The verbatim
statements are in [the literature note](../Library/QuantumBounds/li2025genuinely.md).

Issue [#14459](https://github.com/the-omega-institute/trureturing/issues/14459) reads a form as the
$2\times p$ array of indices $i$, with the source's conventions: the first row is the one whose row-factor
string has bit 0 at $p_1$, and the columns follow the increasing column-factor strings.

## Motivation

Li's criterion for genuine entanglement checks the support against the separable shapes and the
coefficient matrix for proportional rows. The list of forms is the finite catalog that this check runs
through. Li computed it by hand for $m=4$ and $m=6$ and asked for general $m=2p$.

## Gap

The source and Li's earlier work give the factorization of a separable support but no count for $m>6$.
Issue #14459 records the literature check before any Lean: no later work, including Li's 2023–2026 papers,
answers the question; `not-found-in-searched-scope`.

## Route

Let $q$ be the most significant row-factor qubit. Every qubit above $q$ belongs to the column factor, and
at $q$ the first row has 0 and the second row 1. Group the column strings by their bits above $q$. Within a
group every first-row entry precedes every second-row entry, and groups are consecutive intervals. Reading
the $2p$ strings in order and recording their rows gives $T^{a_1}B^{a_1}\cdots T^{a_k}B^{a_k}$ for a
composition $(a_1,\dots,a_k)$ of $p$, which determines the form. Every composition is realized on
$\lceil\log_2k\rceil+\lceil\log_2\max a_i\rceil+1$ qubits and on any larger number.

## Falsifier

A form of the source outside the composition pattern, a composition that cannot be realized without a
fixed qubit, or a catalog convention of the source that counts differently. The source's own catalogs for
$m=4$ and $m=6$ are the two-element and four-element cases of the answer.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/QubitSupportCoefficientForms.lean`, with `result`.
The axiom closure of `result` is exactly `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorry`, `native_decide` or new axiom. The module statement is
`sha256:389b9416ae89bddd36fa8331b2140f6fa054390979a40b27ff59a356f7ec73df`, the `result` statement
`sha256:ba3470efa78426fe50e181ee3403495d0cac0ab3cd5938c87c04b1b60c7161d4`. The Freeze event is
`sha256:a5a22aa21e1bdfb2067817da88fd5ba5ab58ed17c19a76cbf157680e38332b0e`; it has no project-level
prerequisite (the module imports Mathlib only).

## Triage

Tier 1 closing question of an October 2025 paper (no citing work), preregistered in issue #14459 before
any Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | necessity, realization | open-problem-resolution |

`necessity` (every form is the form of a composition, by grouping the column strings by their bits
above the top row qubit) and `realization` (every composition occurs at each
$n\ge2\lceil\log_2p\rceil+1$) are content and lie on the live proof of `result`, as do `forms_eq_range`,
`monotone_composition` and `realization_data`. The other theorems of the module (`formOf_injective` and
the private order and bit lemmas) are bind-only instances of Mathlib's `Composition`, `Nat.testBit` and
`Finset` facts, each used on the proof of `result`. The settlement is admitted as an external
open-problem resolution.

Utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $p\ge1$ the forms of the corresponding coefficient matrix are exactly
$2^{p-1}$, one for each composition of $p$, and all of them occur on every number of qubits
$n\ge2\lceil\log_2p\rceil+1$. For $p$ prime this answers the question; $p=2,3$ give the source's two and
four forms.

**Argued, not formalized.**
- *Mechanism.* Binary order compares the most significant differing qubit. The row factor's top qubit
  splits each block of column strings with a common high prefix into a first-row run followed by a
  second-row run of the same length, so the form records only how the column strings cluster by their
  bits above that qubit.
- *Fixed $n$.* A composition with $k$ parts and largest part $a$ occurs on $n$ qubits exactly when
  $\lceil\log_2k\rceil+\lceil\log_2a\rceil\le n-1$. Exhaustive enumeration agrees for $p\le5$ and
  $n\le7$; for example $p=5$, $n=4$ has 13 forms. Only the bound $n\ge2\lceil\log_2p\rceil+1$
  is formalized.
- *Composite $p$.* The count of $2\times p$ forms does not use primality. For composite $p$ a $2p$-term
  separable support can also factor with other sizes, so the $2\times p$ forms are then one family among
  several; primality is what makes the $2\times p$ shape the only one, as in the source.

**Open.** The forms of separable supports with other factor sizes ($m=gh$, $g,h>2$) and of multipartite
factorizations are not counted here.

**Effect on the paper.** The question of Section 6 is answered; the separability test for $m=2p$ runs over
$2^{p-1}$ forms.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or the absence of
an independent answer.
