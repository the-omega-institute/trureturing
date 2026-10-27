---
slug: sra2609-symmetric-alpha-permanent
bibkey: sra2026koteljanskii
doi: 10.48550/arXiv.2609.39979
url: https://arxiv.org/abs/2609.39979v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result
---

# Sra's symmetric alpha-permanent question

## Problem

Suvrit Sra, *A Koteljanskii inequality for permanents*, arXiv:2609.39979v1,
Section 4(b), asks:

> For symmetrizable inverse $M$-matrices and $\alpha\notin\{\tfrac12,1\}$,
> decide whether $S\mapsto\operatorname{per}_\alpha(A_S)$ is log-supermodular.

The order is positive as in equation (3.1). The universal affirmative
assertion quantifies over $n\ge1$, every real symmetrizable inverse $M$-matrix,
every permitted positive order, and every pair of index subsets.
The source definitions are quoted in
[the Library note](../Library/QuadraticForms/sra2026koteljanskii.md).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Every $n\ge1$, real inverse $M$-matrix | `claim`, imported `InverseMMatrix` | Exactly the source's nonnegativity, invertibility and inverse off-diagonal sign conditions. |
| Positive diagonal similarity to symmetry | `Symmetrizable` | The diagonal function is strictly positive; its pointwise reciprocal gives the inverse diagonal. |
| Equation (3.1), all cycles including fixed points | `alphaPermanent` | `cycleType.card` counts nontrivial cycles, and the fixed-point cardinality adds one-cycles. |
| Principal restriction, including the empty case | `principalAlphaPermanent` | `Matrix.submatrix` on the index subtype; empty product and permutation sum give one. |
| $\alpha>0$, $\alpha\ne1/2,1$ and every $S,T$ | `claim` | All three order conditions and both subset binders are retained. |
| Log-supermodular inequality | `claim` | The $S,T$ product is at most the union-intersection product. |
| Universal affirmative assertion is false | `result` | Literal negation of `claim`. |

## Motivation

`D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result`
refutes the assertion. The public result is the designated refutation result
(`basis=refutes`) and is exempt from four-slot escape registration
(CLAUDE.md §3.9). It is the module's only public theorem.

## Gap

Preregistration [#21689](https://github.com/the-omega-institute/trureturing/issues/21689)
quotes the source, fixes the definitions and records the Tier 1 literature
screen. No settlement was identified within that scope; completeness remains
qualified below. Proof shape is bind-only; admission is
`open-problem-resolution (#21689; Refuted)`.

## Route

The fixed witness is

$$B=\begin{pmatrix}7&2&1&2\\2&7&2&1\\1&2&7&2\\2&1&2&7\end{pmatrix}.$$

Private `witness_positive`, `inverseM` and `symmetric` certify strict entrywise
positivity and the source hypotheses. With zero-based
$S=\{0,1,2\}$ and $T=\{0,2,3\}$, `difference` proves that the
union-intersection product minus the $S,T$ product is

$$\alpha^2(\alpha+1)(2401\alpha^2+1617\alpha-16).$$

`interval_failure` proves strict negativity for every $0<\alpha\le1/200$.
`result` specializes to $\alpha=1/200$ and contradicts the universal
inequality. The imported `InverseMMatrix` is the same definition used in
the reciprocal-polynomial module; there is no second inverse-$M$ definition.

## Falsifier

The displayed matrix with $\alpha=1/200$, $S$ and $T$ satisfies all source
hypotheses and violates its affirmative inequality. The argument refutes the
universal assertion without classifying all remaining positive orders.

## Evidence

The source is
[SraSymmetricAlphaPermanentRefutation.lean](../D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.lean),
with its canonical Blueprint Scribe. Private theorem names below belong to
that namespace.

The rational experiment is
[sra-koteljanskii at `fc05f5ee612010d382cf8772f7bf43a1cb830aa1`](https://github.com/the-omega-institute/trureturing-experiments/tree/fc05f5ee612010d382cf8772f7bf43a1cb830aa1/docs/reports/sra-koteljanskii).
Its `docs/reports/sra-koteljanskii/check.py` has SHA-256
`bf8bef761479549a67a05ccf46ec6e0ebe90c9adf347d014cec66ea510a92a75`.
Command: `python3 /Users/auric/.sshx/91c5c2dbd5cffa0eefe2cd71/attempt-1/check.py`,
using the immutable revision's bytes read by `git show`; exit 0,
`ALL_CHECKS_OK`. This checks the fixed witnesses, the factorization and the
finite subset tests below, separately from the Lean proof.

## Triage

### What the settlement shows

1. **Proved (kernel-checked):** `result` refutes the universal affirmative
   extension. `witness_positive`, `inverseM`, `symmetric`, `difference` and
   `interval_failure` certify that this symmetric positive $4\times4$
   inverse $M$-matrix fails throughout $0<\alpha\le1/200$, with the
   factorization displayed above.
2. **Computed:** all $256$ subset pairs for this fixed $B$ satisfy the
   inequality at each of $\alpha=1/2$ and $\alpha=1$; the selected difference
   at $\alpha=1/200$ equals $-63153999/320000000000$. Evidence: the immutable
   experiment, stated command, exit 0 and SHA-256 above. No other parameter
   range is asserted to have been enumerated.
3. **Open:** remaining universal alpha ranges and the source tree case are
   not newly classified or formalized. **Literature reading:** the source's
   theorem and remark retain the distinguished orders and tree hypotheses;
   no proved source theorem assumes an affirmative answer to either open
   question. Those source results are not on this module's dependency path.
4. **Proved (kernel-checked in the companion module):**
   `SraReciprocalPermanentLorentzianRefutation.result` refutes Section 4(d).
   Its mechanism is a persistent positive two-plane after three coordinate
   derivatives at a strictly positive $5\times5$ inverse $M$-matrix.
   **Computed:** its relevant permanents are $546,9996,9996,182784$,
   product ratio $832/833$, first pivot $1/273$, determinant
   $1/20783363328$, by the same immutable experiment. **Open:** symmetric
   reciprocal-polynomial Lorentzianity and a separately formalized positive
   diagonal scaling extension. The precise evidence and scope are in
   [the companion dossier](sra2609-koteljanskii.md).

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration's screen
includes source v1, Brändén–Huh v8, arXiv, Semantic Scholar, Crossref,
MathOverflow and MathDB. OpenAlex yielded no citation list; broad full-text
results were not all read, and web search produced no reliable relevant
hits. Zero indexed citations does not exclude an undiscovered solution.
No journal version was identified or read.
