---
slug: kag329479-binarynull
bibkey: kagey2019a329479
doi: null
url: https://oeis.org/A329479/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.result
---

# Kagey's order-eight recurrence for binary null polynomials modulo three

## Problem

Peter Kagey's OEIS A329479, revision 25, final FORMULA line, states:

> Conjectured recurrence: a(n) = 2a(n-1) + 2a(n-2) - 5a(n-3) - 2a(n-4) + 10a(n-5) - 4a(n-6) - 4a(n-7) + 8a(n-8).

The source NAME is: “Number of degree n polynomials f with all nonzero coefficients equal to 1 such that f(k) is divisible by 3 for all integers k.” Thus $a(n)$ counts distinct integer polynomials of degree exactly $n$, with leading coefficient one, every coefficient in $\{0,1\}$, and $3\mid f(k)$ for every integer $k$. The source offset is one. The conjecture is interpreted for every natural $n\ge9$, using integer arithmetic for the counts and natural subtraction for the indices.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Degree $n$ integer polynomials | `a`: subtype of `Polynomial Int` with `natDegree = n` | Exact degree; distinct polynomials remain distinct |
| All nonzero coefficients equal one | `a`: every coefficient is zero or one, with `Monic` | For the positive degrees used here, monicness expresses the forced leading one |
| Divisible by three for all integers | `a`: divisibility of every integer evaluation | Full universal condition |
| Eight-term recurrence | `claim`; `result` proves it | All eight coefficients and signs retained |
| Offset one | Guard $9\le n$ | Every preceding index is at least one |

The source COMMENT describes strings of length $n$, while the NAME and six degree-seven examples use polynomial degree $n$. The formal count follows the NAME and examples, so the coefficient string has length $n+1$. No recurrence-defined sequence or quotient by polynomial functions replaces this count.

## Motivation

Preregistration [#21714](https://github.com/the-omega-institute/trureturing/issues/21714) identifies the final conjectured recurrence as the named external problem. The settling declaration is `D5.S3.Combinatorics.BinaryNullPolynomials.KageyA329479Recurrence.result`. There is no digestion atom; its admission basis is `open-problem-resolution (#21714; Proved)`.

## Gap

The source calls the recurrence conjectured. The literature screen in #21714 found no settlement in its retrieved OEIS entry/history, exact arXiv metadata and full-text identifier searches, the screened Kagey papers, MathOverflow results, or the pinned author programs. Li's *Null Polynomials modulo m*, math/0510217v2, treats unrestricted coefficients and does not provide this binary-count recurrence. The analogous modulus-four OEIS proof concerns a different entry. OpenAlex and Semantic Scholar were rate-limited, MathDB was blocked, and broader web and citation coverage is incomplete. Completeness is `ASSUMED-UNVERIFIED`.

## Route

Evaluation at zero forces the constant coefficient to be zero. A degree-$n+1$ polynomial is then determined by its $n$ interior Boolean coefficients and leading one. The private `countEquiv` constructs an equivalence between the valid coefficient words and the literal integer-polynomial subtype, with `reconstruct` proving recovery of the polynomial.

For a zero-constant polynomial, the remaining null condition is precisely vanishing at $1$ and $-1$ in $\mathbb Z/3\mathbb Z$. These values, together with zero, exhaust the residue field. The private `residue_cases` applies the existing public `Complexity.TapeToStacks.fin_three_cases` after the residue interpretation and the equality $2=-1$.

Prepending a coefficient $b\in\{0,1\}$ changes the encoded polynomial by $f\mapsto X(b+f)$. Its evaluation pair changes by $(u,v)\mapsto(b+u,-b-v)$. The backward transition is therefore $(u,v)\mapsto(u-b,-v-b)$. The target pair $(1,-1)$ is the evaluation pair of $X$. The private `contribution_eq` proves the evaluation invariant by structural induction. `words_eq_v` directly applies `CiglerCycleWalkTransfer.weighted_walks_eq_pow`, and `a_eq_v` identifies the count with the resulting nine-state matrix column.

The private `vector_eight` proves the degree-eight identity on all nine starting states by exact finite arithmetic. The private `vector_recurrence` propagates it to every nonnegative shift by the linear transition. `result` transfers this identity to the polynomial counts for every $n\ge9$.

## Falsifier

A failure of the coefficient-word equivalence, a polynomial evaluation pair incompatible with the backward transition, or a state violating the degree-eight column identity would invalidate this argument. A recurrence verified only on finitely many degree values would not establish the universal target. The kernel-checked `result` has the full universal statement.

## Evidence

The Lean source is `D5/S3/Combinatorics/BinaryNullPolynomials/KageyA329479Recurrence.lean`; its Blueprint Scribe displays both complete defining bodies and the expanded proposition of `result`. The sole public theorem is `result`. The source note is `Library/Digit/kagey2019a329479.md`, with the OEIS URL and no identified DOI or arXiv source.

The escape audit of `result` is unfinished: [#22573](https://github.com/the-omega-institute/trureturing/issues/22573). No validated four-slot registration is asserted; the missing evidence is the faithful source reconstruction, bridge and family variation/sensitivity/dependence for the unbounded guarded cardinality recurrence.

### Experiment

The [experiment directory at commit b1521c681870c913ae870b8e7ea618d2f8ba63a9](https://github.com/the-omega-institute/trureturing-experiments/tree/b1521c681870c913ae870b8e7ea618d2f8ba63a9/docs/reports/kagey-a329479-rec) contains `check.py`. Its SHA-256 is `fd20df54edc80be52283806510a9e90b38424c8e8ce29e6621f8d8dcc607c633`. Measurement of the pinned bytes uses `python3 /tmp/op-kag329479/check.py`, exit 0 (`ALL_CHECKS_OK`), using Python 3.14.8 and SymPy 1.14.0. From that experiments revision the reproduction command is `python3 docs/reports/kagey-a329479-rec/check.py`.

The checker reproduces all 37 printed terms and all six degree-seven polynomials; exhaustively checks monic binary polynomials at degrees $1$ through $18$ by Horner evaluation; compares joint evaluation dynamic programming with the parity-binomial formula at degrees $1$ through $1000$; checks the recurrence at indices $9$ through $1000$; and checks the periodic binomial identity for $m=0,\ldots,501$. Exact rational cancellation also verifies the rational generating-function identity. These are computed supporting results; the all-degree proof is the Lean theorem.

## Triage

1. **Proved; kernel-checked:** evaluation at zero forces the constant coefficient to vanish for binary coefficients (`zero_constant`); conditional on zero constant, the null condition is exactly vanishing at $1$ and $-1$ modulo three (`null_iff`). Both private declarations belong to the settling module and are used in `countEquiv`.
2. **Proved; kernel-checked:** the degree-eight recurrence holds for every starting state of the same terminal-column transfer family, for every nonnegative shift (`vector_recurrence`, private). The terminal column remains the one ending at $(1,-1)$; arbitrary target columns are not asserted.
3. **Computed:** the pinned checker reproduces the published initial data and finite checks through degree $1000$, with the command, exit code, SHA-256 and precise scopes given in the Experiment subsection. These finite checks support the unbounded theorem without replacing its proof.
4. **Open:** no uniform theorem for other moduli is established. Their joint evaluation states require separate analysis.
5. **Open:** minimality of the recurrence order and independent settlements of neighbouring OEIS entries are not formalized.

### What the settlement shows

The decisive mechanism is the reversible polynomial/word correspondence and the polynomial-evaluation invariant, followed by a fixed terminal-column annihilator propagated by linearity. Its all-start-state extension is proved by `vector_recurrence`; it does not depend on the chosen initial pair $(0,0)$ used to extract the source count. The finite annihilator and its propagation are consumed auxiliary facts, rather than separate general-modulus claims.

The final recurrence line of A329479 is proved. The two product formulas involving A024493 and A024495 are source context; independent formal settlements of those entries and minimality of order eight remain open here. No other source theorem relying on the conjectured recurrence was identified in the retrieved entry; completeness of that source-dependency screen is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The external literature and citing-work screen is incomplete for the reasons stated under Gap. Source priority and the absence of any external settlement are not kernel conclusions. The NAME/example interpretation and the offset-derived starting index are the binding conventions of #21714. Four-slot escape registration remains unfinished under #22573. No assertion is made about other moduli, recurrence minimality or independent neighbouring entries.
