---
slug: oeis-a396596-divisor-power-union
bibkey: switkay2026divisorpowerunion
doi: null
url: https://oeis.org/search?q=id:A396596&fmt=text
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation
---

# A396596 divisor-power union: a counterexample

## Problem

Hal M. Switkay, OEIS A396596, contribution August 31, 2026, revision 65:

> Natural numbers k such that the sum of the x-th powers of the divisors of k achieves a record, for some x <= 0.

The selected COMMENTS assertion is:

> We conjecture that the present sequence can be constructed simply as a union of highly composite numbers and deeply composite numbers.

The primary URL in this dossier is byte-for-byte the URL in the source note's
`Verified locator`. The source note is
`Library/notes/switkay2026divisorpowerunion.md`, referenced as
`D5/L/switkay2026divisorpowerunion`.

The complete statement mirror, including the two needed definitions and the
closed proposition that the single result negates, is:

```lean
noncomputable def DivisorPowerSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ) ^ x

def StrictDivisorPowerRecord (n : ℕ) (x : ℝ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n →
    DivisorPowerSum m x < DivisorPowerSum n x

def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    ((∃ x : ℝ, x ≤ 0 ∧ StrictDivisorPowerRecord n x) ↔
      (StrictDivisorPowerRecord n 0 ∨
        ∃ B : ℝ, B < 0 ∧ ∀ x : ℝ, x ≤ B →
          StrictDivisorPowerRecord n x))

theorem result : ¬ claim
```

The last line is a type display; the proof remains solely in the Lean module.
Every positive divisor is summed, and every smaller positive natural is
compared strictly at one common real exponent. The empty predecessor case
at 1 is allowed; zero candidates are excluded. The right-hand eventual
quantifier ranges over all real exponents below one negative real threshold,
following A095848's NAME, “all sufficiently low (i.e., negative) values of k,”
read in the real-parameter setting of A396596. It is not a test of finitely
many exponents or an assumed lexicographic characterization.

## Motivation

`question_answered`: whether every positive natural that is a strict record
for some real exponent at most zero is highly composite or deeply composite,
with the converse included in the registered iff. A single record outside
both classes refutes that full assertion.

The first-tier, source-labelled target was publicly preregistered at
https://github.com/the-omega-institute/trureturing/issues/8081,
created `2026-09-15T11:22:40Z`. The pinned registration SHA-256 is
`8d4e74e669b36db6b938f2c31c793001f29bbf38386d8906799ded077e827237`.
It preceded numerical and Lean probes. No difficulty or historical-priority
inference follows from the tier.

## Gap

`dominating_theorem_search: not-found-in-searched-scope`. The preregistration
records lexical target/conclusion-shape searches of D5, Problems, Library and
Blueprint at `b7d245a444b19b4036490129a61d9c01370052e0` and pinned Mathlib's
arithmetic/power scope. It found no complete target there. Earlier repository
results treat square-root-rank lcm divisibility and prime-exponent power
scores; the latter sum over prime exponents, not positive divisors.

The preregistration's source/history assessment read the complete A396596,
A095848, A002182 and A095849 originals; full bodies of 6022, 6006, 7335,
6072, 6067 and all 12 comments; and 8054's different A094802 factorial/lcm
target. All-state GitHub search at `2026-09-15T10:51:20Z` returned exact
A396596: 0 and deeply-composite: 6, both `incomplete_results=false`.
The 11:19 UTC search returned the same counts. These are historical bounded
readings supplied by the registration, not fresh search or ownership claims.

The 1944 Alaoglu–Erdős original scan at printed page 465, section 6(7),
supports a near-zero negative-exponent characterization. Its complete
23-page extracted text has damaged or absent equations, so the registration
does not claim a complete mathematical reading or proof-level exclusion;
no full union settlement was located in the readable prose. The complete
four-page Burdette–Stewart 2020 text, arXiv:2009.03306v1, including appendix,
addresses a different prime-multiplication/division graph problem. Its
computation was not reproduced. The source note retains the access limits.
No exhaustive literature absence is asserted; an earlier full settlement
would invalidate this candidate's unresolved-problem eligibility.

## Route

Write `S(n,x) = DivisorPowerSum n x`, `R(n,x) = StrictDivisorPowerRecord n x`,
`N = 32125373280` and `L = 232792560`. The following describes the exact
argument in the canonical source.

First, reciprocal divisor pairing gives `S(n,-4) = sigma_4(n)/n^4` for
positive `n`. A local induction proves soundness of a prime-power
factorization certificate: when the listed bases are prime and their powers
pairwise coprime, the product of geometric sums is `sigma_k` of their product.
For N it yields

```text
sigma_4(N) = 1152780338446808124302790430032176310391296,
S(N,-4) = 1678677187106139216341549972195017
          / 1551005573419488074754054309120000.
```

The analytic step proves, for real `r ≥ 1`,

```text
1/(r+1)^4 + 1/(3*(r+1)^3) ≤ 1/(3*r^3).
```

Telescoping and the exact first 64 terms bound the reciprocal fourth-power
sum of any finite set of positive naturals strictly by `108232327/100000000`.
If a positive `m` is not divisible by `L = lcm(1,...,19)`, some
`1 ≤ d ≤ 19` does not divide `m`. Both `d` and `2d` are absent from its
divisors. Inserting those distinct missing terms into the finite-set bound
subtracts at least `1/19^4 + 1/38^4`, placing `S(m,-4)` strictly below
`S(N,-4)`. This covers every nonmultiple without a prime-signature assumption.

Every positive multiple of L below N is `kL` with `1 ≤ k ≤ 137`. The local
137-row certificate checks primality, pairwise coprimality, exact product
`kL`, and the strict cross-multiplied sigma inequality for each row. Its
soundness then gives `S(kL,-4) < S(N,-4)`. Together the two branches establish
the full predecessor obligation `R(N,-4)`; the rows alone are not a claim
that a sampled family exhausts all predecessors.

At zero, `H = 27935107200 < N` also has 3072 positive divisors. Thus
`S(H,0) = S(N,0)`, which excludes the strict record at zero.

For `M = 26771144400 < N`, every N-divisor at most 26 is an M-divisor;
25 divides M but not N. After common divisors cancel, the N-only contribution
is at most `N*27^x`, while the M-only contribution is at least `25^x`.
For every real `x ≤ -1000`, the exact inequality
`N*(27/25)^x < 1` gives `N*27^x < 25^x`. The proof derives the threshold
from `(27/25)^10 > 2` and a natural-power bound, with no decimal approximation.
Hence `S(N,x) < S(M,x)` throughout that real half-line. For an arbitrary
proposed `B < 0`, choosing the real exponent `min(B,-1000)` contradicts
eventual record membership. Applying `claim` to N and exponent −4 therefore
contradicts both right-hand alternatives and gives the closed `¬ claim`.

Empirical discovery only selects the candidate. The analytic bound,
certificate soundness and full real endpoint exclusions carry the
proof. No minimality assertion, other numerical candidate, floating-point
proof, or prime-signature completeness assumption is used.

## Falsifier

A predecessor with `0 < m < N` and `S(N,-4) ≤ S(m,-4)` would defeat the
record witness. A missing or invalid certificate row, failure of the
finite-set bound or its missing-divisor application, an incorrect divisor
count tie, or failure of the real half-line comparison would defeat the
corresponding proof obligation. A mismatch between the displayed claim and
the source union would defeat source fidelity even if the Lean type compiled.
An earlier complete published settlement would defeat eligibility, separately
from the arithmetic correctness of this witness.

## Evidence

The canonical Lean source has 400 lines and SHA-256
`a1c5e9d02f64b50fd33f475cbbb8b8e17c3f3e7917030c600ddfe934d2929ed4`.
Its four authored declarations are `DivisorPowerSum`,
`StrictDivisorPowerRecord`, `claim`, and `result : ¬ claim`; all proof helpers
are local to `result`. The selected module builds successfully on Lean
v4.33.0 and Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
The only two build warnings concern the required single-line structured headers.

The full expanded original-claim negation checker and all-constant standard
axiom audit validate the theorem's complete domains and closed type.
An independent mirror also checked the complete predecessor argument and
all 137 exact arithmetic rows. These checks do not establish global priority
or exhaustive literature absence.

## Triage

`theorem` denotes the refutation route. The semantic classification is:

- The two definitions and `claim` are needed source encodings with assessed
  literature provenance; theorem proof-shape classification is inapplicable
  to these definitions. They are not separate certified-instance results.
- For `result`, `proof_shape: content`: the local analytic bound, certificate
  soundness and full real endpoint exclusions supply the content.
- `computational_content.kind: certified-instance`; `bounded-enumeration`
  also applies. The typed `refutes` basis is the closed original-claim negation required by
  the stricter case.
- `utility.basis: refutes=gid:D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.claim`;
  result GID: `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.result`.
- `admission_basis: open-problem-resolution`; `escape_witness: none`.
  Direct frozen project dependencies: none, so no frozen dependency GID or
  statement identity is asserted. Mathlib imports are not project freezes.
- Scribe attaches `OpenProblemResolutionClaim` with this exact slug and
  `ResolutionKind.Refuted` to `result`; this binds the
  formal conclusion to the exact external problem. No atom or coverage is involved.

## ASSUMED-UNVERIFIED

Source fidelity and proof-shape/utility classification are semantic review
judgments, distinct from kernel checking.

Bing's relaxed results, DuckDuckGo's challenge, arXiv API 429 and an optional
urllib 403 supply no absence evidence. The subsequent official OEIS HTTP 200
with identical A396596 bytes resolves only that fetch. The 1944 equation
extraction remains damaged; uninspected papers, inaccessible monographs and
full databases remain outside the bounded search.

The result addresses the selected universal union claim alone. It does not
claim all superabundant numbers fall outside either class, settle A095849's
intersection conjecture, verify the source's finite superabundant observation,
establish a least counterexample, or assert global priority. OEIS definitions
and conjecture are attributed to the cited entries; the proof is
repo-derived. Citation and short quotation follow https://oeis.org/LICENSE.
