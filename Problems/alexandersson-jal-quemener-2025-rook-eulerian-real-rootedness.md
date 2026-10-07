---
slug: alexandersson-jal-quemener-2025-rook-eulerian-real-rootedness
bibkey: alexanderssonjalquemener2025rook
doi: 10.48550/arXiv.2502.05939
url: https://arxiv.org/abs/2502.05939v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/MultisetRookEulerianRealRootednessRefutation.result
---

# Full multiset rook-Eulerian real-rootedness on Ferrers boards

## Problem

Alexandersson, Jal and Quemener, *Real-rootedness of rook-Eulerian polynomials*,
arXiv:2502.05939v1, Section 3.3, Conjecture 28, first clause:

> For Ferrers boards, the polynomial $R(\lambda,\alpha;t)$ is real-rooted.

The section defines $\lambda_i>\mu_i$ at every row; for a Ferrers board
$\mu=0$, so $\lambda_1\le\cdots\le\lambda_n$ has strictly positive entries.
The content $\alpha=(\alpha_1,\ldots,\alpha_k)$ consists of nonnegative
integers with sum $n$. The fitting words have these multiplicities and satisfy
$0<w_i\le\lambda_i$. Equation (10) defines
$R=\sum_{w\in W}t^{\operatorname{asc}(w)}$, where asc counts strict adjacent
ascents. The exact universal claim quantifies every $n>0$, every $k$, every
such board, and every such content.

## Motivation

The earlier six-row counterexample refutes the interlacing clause of the same
Conjecture 28. It leaves this first clause undecided. The new theorem
`MultisetRookEulerianRealRootednessRefutation.result` directly negates a
standalone claim for the full source polynomial, with every source condition.
The two results concern distinct clauses of one published conjecture.

## Gap

This is a Tier 1 named conjecture clause. Research issue #13765 records the
exact first clause, the source conditions and the proposed full certificate
and recurrence bridge. It honestly discloses that exploratory Lean work had
already begun, and does not assert a pre-probe registration. The prior #12894
registers only the interlacing work. The existing bounded screen examined the
arXiv version record, queries
`all:"rook-Eulerian"` and `all:"multiset" AND all:"rook" AND all:"interlacing"`,
and MathDB searches for "rook-Eulerian", "multiset rook" and "Alexandersson Jal";
it found no settlement in that scope. The source states the conjecture in v1.
This is a bounded finding, not a claim of worldwide priority.

## Route

Use $n=120$, $k=6$, the positive monotone board
$\lambda=(2^3,3^4,4^{10},5^2,6^{101})$, and
$\alpha=(6,1,4,8,1,100)$. Exponents on the row values denote repetitions.
Both the largest row length and alphabet size are 6.

A generic theorem identifies the original word sum with a recurrence on
remaining row bounds, remaining letters and the preceding letter. Its
first-letter branches are disjoint and exhaustive. The complete finite
certificate then proves

$$R=t^2Q,$$

$$Q=1+261t+21704t^2+591814t^3+5372605t^4+18550680t^5
 +27147806t^6+17137014t^7+4318325t^8+352440t^9.$$

Translate by $t\mapsto t-9/1000$. If the resulting degree-nine polynomial
$P$ split over the reals, the existing Newton inequality and Vieta's formula
would require $4p_1^2\ge9p_0p_2$ for its first three coefficients. Exact
rational coefficients violate this inequality. Translation preserves
splitting; the factor $t^2$ adds only zeros at the origin. Hence the complete
source polynomial fails real-rootedness.

## Falsifier

Any omitted recurrence branch, incorrect letter erasure, incorrect strict
ascent exponent, mismatch with the original W or R, failure of board
positivity or content sum, coefficient mismatch, or incorrect direction of
the Newton inequality would invalidate the witness. The source's
positive-row and nonnegative-content conditions must be retained.

## Evidence

The public conclusion is `result : ¬ claim`, where claim is the standalone
first real-rootedness clause. The live proof consumes the generic counting
bridge, the full finite recurrence certificate, the exact source-polynomial
equality, the admissibility of board/content, and the exact non-splitting
certificate. Generated numerical data is not a trusted premise. The witness
certificate contains 1769 states and 3235 edges; the root is state 1768.
The reusable bridge is `MultisetRookEulerianWordRecurrence.W_sum_eq_dp`,
the exact obstruction is in `MultisetRookEulerianNonrealCertificate`, and
the certificate occupies dependency-ordered `MultisetRookEulerianCertificate`
blocks. The root declaration is `Block64.dag_1768`; the principal `claim`
and `result` retain their module and names.

Real-rootedness uses Mathlib's `Polynomial.Splits` over $\mathbb R$ directly.
No `native_decide`, `sorry`, or new axiom is used.

## Triage

Tier 1; first-clause refutation under `admission_basis: escape-witness`,
research issue #13765. The complete original-word-sum recurrence bridge is
the substantive witness on the result’s live proof path. An independent
source review identifies this bridge as content; the generated finite
equalities are consumed proof helpers. The utility is `certified-instance` with the typed
refutation of claim. Information-escape registration is paused under current
CLAUDE.md section 3.9. Per-declaration proof shape and active consumers are
reported in the ordinary delivery review.

### What the settlement shows

- **Proved by this result:** positivity and monotonicity of a Ferrers board do
  not suffice for real-rootedness with arbitrary nonnegative content. The
  obstruction is in the full polynomial, and appears as an exact translated
  Newton-inequality failure.
- **Proved in the cited literature:** rectangular-board real-rootedness and
  the rectangular interlacing theorem retain their additional shape
  hypothesis. The nonrectangular witness does not contradict them. The
  primary paper's distinct-letter result likewise retains its hypothesis.
- **Open:** the smallest failing size; a structural characterization of
  boards and contents for which the full polynomial is real-rooted; whether
  other explicit content restrictions recover the first clause. These are
  separate prospective questions, not conclusions of the certificate.
- **Consequence:** the source's conjectured extension to general multiset
  content cannot establish general Ferrers-board real-rootedness. Existing
  theorems with rectangular-board or distinct-letter assumptions are
  unaffected. Any argument using the universal first clause requires a
  revised hypothesis or a different route.

## ASSUMED-UNVERIFIED

The bounded literature screen does not prove global priority. No minimality
or exhaustive classification follows from this single witness. Source and
generated certificate data acquire mathematical authority only through the
actual accepted Lean result and its axiom closure.
