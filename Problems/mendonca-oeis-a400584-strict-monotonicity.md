---
slug: mendonca-oeis-a400584-strict-monotonicity
bibkey: mendonca2026a400584
doi: null
url: https://oeis.org/A400584
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MendoncaMinPlusTriangle.result
---

# Strict decrease in Mendonça's min-plus configuration triangle

## Problem

J. R. G. Mendonça's [OEIS A400584, revision 28](https://oeis.org/A400584) states: “Conjecture: T(n,k) > T(n,k+1) for n >= 3 and 1 <= k < 2^n.” The associated [technical note](https://oeis.org/A400584/a400584.pdf) gives the counting recurrence as Proposition 2. The complete source quotations and conventions are in [preregistration #19612](https://github.com/the-omega-institute/trureturing/issues/19612) and [the Library note](../Library/RecurrenceComposition/mendonca2026a400584.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Complete plane binary tree of depth $n$ | `LabeledTree n`: one leaf at zero, one labeled root with two ordered equal-depth subtrees at successor depth | Left and right positions remain distinct; no quotient by swaps. |
| Each internal vertex is labeled by addition or minimum | The two constructors of `Op` and the operator parameter of `LabeledTree.node` | Exactly the source's two labels. |
| Every leaf equals one; each vertex applies its operator | All three recursion cases of `value` | Literal source evaluation. |
| Number of labelings with root value $k$ | `T n k`, the `Nat.card` of the root-value subtype | Counts labelings rather than possible values; finiteness is constructed privately. |
| $n\ge3$ and $1\le k<2^n$ | All natural-number binders and all three guards of `claim` | The same range, including every adjacent pair through the last column. |
| $T(n,k)>T(n,k+1)$ | `result : claim` | The strict comparison has only its sides reversed syntactically. |
| Depth-zero convention $T(0,1)=1$ | The leaf constructor and the private `T_zero` helper | The source recurrence's initial condition; no additional hypothesis on the conjecture. |

## Motivation

**Proved (kernel-checked):** `D5/S1/Recurrence/MendoncaMinPlusTriangle.result` settles the full quantified strict finite-depth conjecture. The module's admission basis is `open-problem-resolution (#19612; Proved)`; its generality is I and its utility header is `none`. There is no atom or coverage claim.

## Gap

The source reports weak monotonicity attributed to unpublished work of Albert Chen, independently discovered by Tam Cheetham-West, via Auffinger and Cable. Weak decrease permits the ties in the first two rows. The source explicitly leaves strict decrease from depth three unproved. The bounded literature screen recorded in #19612 found no strict finite-row settlement; exhaustive completeness is `ASSUMED-UNVERIFIED`.

## Route

The ordered root decomposition gives the min-plus counting recurrence. For a positive strictly decreasing integer sequence $a_1,\ldots,a_m$, with $m\ge2$ and zero extension beyond $m$, put

$$
b_k=a_k^2+2a_k\sum_{j=k+1}^{m}a_j+\sum_{i=1}^{k-1}a_i a_{k-i}.
$$

The private `Preservation.adjacent_difference` helper proves

$$
b_k-b_{k+1}=\sum_{i=1}^{k-1}(a_i-a_k)(a_{k-i}-a_{k+1-i})
 +a_{k+1}(2a_k-a_{k+1})
 +2(a_k-a_{k+1})\sum_{j=k+2}^{m}a_j.
$$

All terms are nonnegative. A strictly positive term is available in each range: the central product when $k<m$; the term at $i=1$ when $k=m$; and the term at $i=k-m$ when $m<k<2m$. The private `Preservation.strict_preservation` helper proves the resulting strict inequalities. The tree-count bridge, positivity of every supported value, and the strict depth-three base give `result` by induction. These are consumed private results of this module, not separate published theorems.

## Falsifier

A natural depth $n\ge3$ and a column $1\le k<2^n$ with $T(n,k)\le T(n,k+1)$ would falsify the assertion. A different source convention that identifies exchanged children, changes the leaf values or counts unordered trees would invalidate the stated source correspondence. The Lean definition retains the ordered source convention.

## Evidence

**Proved (kernel-checked):** `D5.S1.Recurrence.MendoncaMinPlusTriangle.result`, with axiom closure contained in `{propext, Classical.choice, Quot.sound}`. The Scribe displays the full proposition and records one Proved resolution claim on that settling declaration.

**Computed:** the published [experiment directory at commit `925b29bf588f3e7ce47bc4373618d6b406b960c4`](https://github.com/the-omega-institute/trureturing-experiments/tree/925b29bf588f3e7ce47bc4373618d6b406b960c4/docs/reports/mendonca-2026-oeis-a400584-strict-monotonicity). Command: `python3 /Users/auric/trureturing-experiments/docs/reports/mendonca-2026-oeis-a400584-strict-monotonicity/check.py`; exit 0, `RESULT PASS`; `check.py` SHA-256: `63bb76481701e57e9699defede0cf209d963d47f5c9dc2025782286a7ffafc72`. The exact scopes are:

- All labelings at depths zero through four agree with the recurrence, including $2^{15}$ labelings at depth four.
- Rows zero through twelve have $2^n$ positive entries and total $2^{2^n-1}$; rows three through twelve strictly decrease.
- The adjacent-difference identity holds for rows one through ten and 4000 random strictly decreasing positive sequences of lengths two through ten (seed 400584).
- The three positive-term cases hold for rows three through ten and the same 4000 random sequences, for $1\le k<2m$. The identity also checks $k=2m$.

The experiment is finite evidence. The unbounded assertion is supported by `result`.

The four-slot escape audit of the only public theorem, `D5.S1.Recurrence.MendoncaMinPlusTriangle.result`, is **unfinished**: [issue #19724](https://github.com/the-omega-institute/trureturing/issues/19724) specifies the source-family realization, sensitivity and observational-dependence evidence that is missing. No `declared_validated` registration is claimed.

## Triage

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Settlement | **Proved (kernel-checked):** `D5.S1.Recurrence.MendoncaMinPlusTriangle.result` establishes every source pair at every depth from three onward. |
| Tier 1 | **Proved in prose:** the quoted fourth COMMENT explicitly calls the displayed strict inequality a conjecture and states it is not proved in general, meeting the external explicitly posed tier-1 criterion. The evidence is the source reading in #19612. |
| Admission basis | **Proved in prose:** #19612 identifies the conjecture and conventions before the proof; the sole public theorem is its settlement; the Scribe and this dossier identify that result; the header states `utility: none`. Thus the delivery uses `open-problem-resolution (#19612; Proved)`. |
| Mechanism and integer extension | **Proved (kernel-checked private helper):** `D5.S1.Recurrence.MendoncaMinPlusTriangle.Preservation.strict_preservation` is over integer-valued inputs, with $m\ge2$, positivity and strict decrease on $[1,m]$, and zero extension after $m$. It gives strict decrease for $1\le k<2m$. The source rows are an application of this more general consumed helper. |
| Significance | **Proved (kernel-checked):** `result` quantifies over every natural depth $n\ge3$, so the settlement extends beyond a finite verification range. No empirical or publication-priority claim follows from compilation. |
| Cutoff | **Computed:** the published experiment gives rows one and two as $(1,1)$ and $(3,2,2,1)$, respectively, and row three as $(39,25,20,17,14,8,4,1)$. **Proved (kernel-checked private helper):** `row_three_strict` establishes the seven adjacent strict comparisons at depth three. |
| Source's partial results | **Literature reading:** the source's support, recurrence and extreme entries retain their meanings; the strict result strengthens weak decrease on its stated range. The cited unpublished weak result is not on this module's dependency path. No theorem here claims to settle other questions of the cited works. |
| Independent review and escape registration | **Open:** the postpublication independent review is outside this mathematical settlement; the four-slot audit remains unfinished under #19724. The source, Scribe, dossier and canonical frozen module record are the delivery surfaces. |

The lower cutoff is sharp for a statement that all rows from a given depth strictly decrease: the computed ties exclude cutoffs one and two. The proof of preservation works over $\mathbb Z$ under its explicit positivity and finite-support hypotheses; no signed-input or non-strict-input extension is asserted. Such extensions, and other source questions, remain outside the proved statements.

## ASSUMED-UNVERIFIED

Literature completeness and global priority remain `ASSUMED-UNVERIFIED`. The bounded screen in #19612 and the source checks include OEIS revision 28, the associated technical note, Auffinger–Cable arXiv:1709.07849, Mendonça arXiv:2608.12295, and six citing works. Wiley full text and the submitted q-ary manuscript were unavailable to that screen. These limits do not strengthen the mathematical claim. The four-slot escape audit remains unfinished under [#19724](https://github.com/the-omega-institute/trureturing/issues/19724).
