---
slug: sra2609-koteljanskii
bibkey: sra2026koteljanskii
doi: 10.48550/arXiv.2609.39979
url: https://arxiv.org/abs/2609.39979v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result
---

# Sra's reciprocal-permanent Lorentzian question

## Problem

Suvrit Sra, *A Koteljanskii inequality for permanents*, arXiv:2609.39979v1,
Section 4(d), asks:

> Is $f_A$ Lorentzian for every inverse $M$-matrix $A$?

Here, for $n\ge1$,

$$f_A(x_0,x)=\sum_{S\subseteq[n]}\operatorname{per}(A_S)^{-1}
x_0^{n-|S|}\prod_{i\in S}x_i.$$

An inverse $M$-matrix is entrywise nonnegative, invertible, and has inverse
off-diagonal entries at most zero. The empty principal permanent is one.
Lorentzian means the coefficient-topology closure of the recursively defined
strict Lorentzian class of Brändén–Huh, Definition 2.1; it is not defined here
by only a necessary Hessian test. The complete source expressions are in
[the source note](../Library/QuadraticForms/sra2026koteljanskii.md) and
[the Lorentzian note](../Library/Combinatorics/brandenhuh2020lorentzian.md).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Every positive dimension, every real inverse $M$-matrix | `claim`: $n>0$, real `Matrix (Fin n) (Fin n)`, `InverseMMatrix` | No symmetry or strict-entry-positivity assumption is added. |
| Principal-submatrix permutation permanent | `PSW.principalPermanent`, `Matrix.permanent` | The subtype supplies exactly the selected indices, including the empty case. |
| Displayed reciprocal polynomial | `reciprocalPolynomial` | `none` is $x_0$ and `some i` is source variable $x_{i+1}$. |
| Brändén–Huh positive homogeneous class, strict recursion, closure | `positiveHomogeneous`, `quadraticHessian`, `strictlyLorentzian`, `Lorentzian` | All degree-$d$ coefficients are quantified; eigenvalue indices count multiplicity; finite-dimensional coefficientwise epsilon approximation expresses the closure. |
| Affirmative universal assertion is false | `result` | The theorem proves the literal negation of `claim`. |

## Motivation

`D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.result`
refutes the assertion at dimension five. The public result is the designated
refutation result (`basis=refutes`) and is exempt from four-slot escape
registration (CLAUDE.md §3.9). It is the module's only public theorem.

## Gap

Preregistration [#21688](https://github.com/the-omega-institute/trureturing/issues/21688)
quotes the published question, fixes the literal definitions and classifies
it as Tier 1. Its literature screen identifies no settlement in the searched
scope. The matrix is Sra's published Theorem 1.2 witness; its ordinary
permanent-product failure is credited to that source. The distinct conclusion
here is the negative answer to the reciprocal-polynomial question.
Proof shape is bind-only; admission is `open-problem-resolution (#21688; Refuted)`.

## Route

The literal positive matrix is

$$A=\begin{pmatrix}
13&1&7&7&7\\1&13&7&7&7\\1&1&7&7&7\\1&1&1&7&7\\1&1&1&1&7
\end{pmatrix}.$$

The private theorems `witness_positive` and `inverseM` certify its hypotheses.
`coefficient_table` and `witness_coeff` compute the relevant coefficients.
The three derivatives in the last three coordinates have Hessian restriction
to $\operatorname{span}(e_0,e_1+e_2)$ with first pivot $1/273$ and
determinant $1/20783363328$ (the exact values are computed below).
`close_plane_positive` proves that this restriction remains positive definite
when every degree-five coefficient changes by less than $10^{-12}$.
`two_plane_excludes_unique` contradicts the exactly-one-positive-eigenvalue
requirement reached after three steps of the strict Lorentzian recursion.
`result` applies this contradiction to a strict approximation supplied by
the literal closure definition.

## Falsifier

The affirmative assertion would force the displayed matrix's reciprocal
polynomial into that closure. Its fixed positive two-plane excludes every
sufficiently close strict approximation. The kernel-checked `result` is the
negation of the full assertion. Symmetric or symmetrizable reciprocal
polynomials are a separate, unresolved restriction here.

## Evidence

The formal source is
[SraReciprocalPermanentLorentzianRefutation.lean](../D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation.lean);
its canonical exposition is the corresponding Blueprint Scribe.
Private theorem names below are qualified by that module's namespace.

The rational experiment is
[sra-koteljanskii at `fc05f5ee612010d382cf8772f7bf43a1cb830aa1`](https://github.com/the-omega-institute/trureturing-experiments/tree/fc05f5ee612010d382cf8772f7bf43a1cb830aa1/docs/reports/sra-koteljanskii).
The checked script is `docs/reports/sra-koteljanskii/check.py`, SHA-256
`bf8bef761479549a67a05ccf46ec6e0ebe90c9adf347d014cec66ea510a92a75`.
Command: `python3 /tmp/op-sra2609/check.py`,
using the bytes read by `git show` from that immutable revision; exit 0,
`ALL_CHECKS_OK`. It checks the displayed matrices and the scopes stated in
Triage; it is computational evidence, separate from the Lean proof.

## Triage

### What the settlement shows

1. **Proved (kernel-checked):** `result` refutes the unchanged universal
   assertion at $n=5$. `witness_positive` and `inverseM` certify the literal
   matrix's strict entrywise positivity and inverse-$M$ property.
   `coefficient_table`, `close_plane_positive` and `two_plane_excludes_unique`
   establish the persistent positive two-plane obstruction to strict
   approximation. These are the mechanism of this refutation.
2. **Computed:** for this published $A$, the four principal permanents are
   $546,9996,9996,182784$, with product ratio $832/833$.
   The differentiated Hessian two-plane has first pivot $1/273$ and
   determinant $1/20783363328$. Evidence: the immutable experiment above,
   the stated command, exit 0 and SHA-256. No other dimension or matrix
   family is claimed to be enumerated.
3. **Open:** Lorentzianity for symmetric or symmetrizable inverse $M$-matrices
   is not settled. The positive-diagonal-scaling extension is not separately
   formalized. In the source, symmetric inverse $M$-matrices satisfy ordinary
   permanent log-supermodularity, so the particular strict overlapping-product
   failure used here does not supply a symmetric counterexample.
4. **Proved (kernel-checked in the companion module):**
   `SraSymmetricAlphaPermanentRefutation.result` refutes Section 4(b).
   Its private `witness_positive`, `inverseM`, `symmetric`, `difference` and
   `interval_failure` certify the displayed symmetric $4\times4$ inverse
   $M$-matrix and its failure for every $0<\alpha\le1/200$.
   The difference is $\alpha^2(\alpha+1)(2401\alpha^2+1617\alpha-16)$.
   The full companion statement and evidence are in
   [its dossier](sra2609-symmetric-alpha-permanent.md).
5. **Computed:** for that fixed companion matrix, all $256$ subset pairs
   satisfy the inequality at each of $\alpha=1/2$ and $\alpha=1$; the
   selected difference at $\alpha=1/200$ is
   $-63153999/320000000000$. Evidence: the same immutable experiment,
   command, exit 0 and SHA-256. This is a finite check at two orders, not
   a classification of parameter ranges.
6. **Open:** the remaining universal alpha parameter ranges and the source's
   tree case are not newly classified or formalized. **Literature reading:**
   no proved theorem of the source relies on an affirmative answer to either
   open question; the refutations change those answers and the reported
   numerical evidence, while the source's established theorems retain their
   stated hypotheses. The source's distinguished orders and tree result are
   not on this module's dependency path.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration's screen
covers the source v1, Brändén–Huh v8, arXiv metadata and selected full texts,
Semantic Scholar, Crossref, MathOverflow and MathDB. OpenAlex supplied no
citation list; the broad 200-result full-text query was not exhaustively
read, and web search supplied no reliable relevant hits. Semantic Scholar's
zero indexed citations is an index reading, not proof of no prior solution.
No journal version was identified or read.
