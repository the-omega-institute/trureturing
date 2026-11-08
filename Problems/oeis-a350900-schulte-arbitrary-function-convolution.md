---
slug: oeis-a350900-schulte-arbitrary-function-convolution
bibkey: schulte2022a350900
doi: null
url: https://oeis.org/A350900
triage: theorem
motivation_gids:
  - D5/S3/Arith/RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity
  - D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.rowSum
---

# Schulte's complete arbitrary-function gcd-quotient conjecture

## Problem

The source is Werner Schulte's OEIS A350900 COMMENTS assertion, attributed
January 21 2022, in revision 13 (`%I #13 May 24 2024 11:58:43`):
https://oeis.org/A350900/internal. The complete sentence is:

> Conjecture: Let f be an arbitrary arithmetic function. Define for n > 0 the sequence a(f; n) = Sum_{i=1..n, k=1..n} f(gcd(i,n)/gcd(gcd(i,k),n)); a(f; n) equals Dirichlet convolution of f(n)*A000010(n) and A057660(n); if f is multiplicative, then a(f; n) is multiplicative; row sums of this triangle use f(n) = n (see formula section).

Let P be the positive integers and let f range over every function P -> C.
For every positive natural n, and independently for every i,k in 1..n, put

$$
q_n(i,k)=\frac{\gcd(i,n)}{\gcd(\gcd(i,k),n)},\qquad
A_f(n)=\sum_{i=1}^{n}\sum_{k=1}^{n}f(q_n(i,k)).
$$

Both gcds and the division are natural-number operations. The denominator
is positive and divides the numerator; q is positive, its product with the
denominator is the numerator, and q divides n. The square is ordered and
includes the diagonal. It is defined independently of the proposed answer.
For positive m define

$$
H(m)=\sum_{e\mid m}e\varphi(e),\qquad
A_f(n)=\sum_{d\mid n}f(d)\varphi(d)H(n/d).
$$

Here A000010 is Euler's totient phi. The first formula for H is the A057660
FORMULA in revision 177 (`Sep 27 2026 00:09:24`), verified at
https://oeis.org/A057660/internal. Divisor sums use positive divisors and
the factors are cast into C. The right side is Dirichlet convolution of
the pointwise product f*phi with H. The identity imposes no multiplicativity,
reality, positivity or boundedness condition on f.

Multiplicative has the normalized OEIS convention
https://oeis.org/wiki/Multiplicative_arithmetic_functions:
f(1)=1 and f(ab)=f(a)f(b) for every coprime pair of positive integers.
Under precisely these hypotheses the second source clause asserts
A_f(1)=1 and A_f(ab)=A_f(a)A_f(b) for every such pair. Complete
multiplicativity is not assumed. Every choice of the extension value f(0)
gives the same positive-n square. Finally f(d)=(d:C) recovers the existing
natural-valued rowSum after casting. The separate triangle-symmetry comment
is outside this assertion, and there is no additional source target at n=0.

## Motivation

The original nested quotient has a joint arithmetic structure. Fixing
g=gcd(i,n) makes the inner quotient g/gcd(g,k), a function of period g.
Since g divides n, complete periods and their totient-sized gcd fibres
separate the arbitrary weight from the counting. A second gcd-fibre
regrouping then supplies the divisor convolution. The existing identity-weight
row sum supplies a compatibility check, not the general arbitrary-function
assertion.

## Gap

Source year: 2022; Tier 1 under CLAUDE §3.6. The qualification is the explicit
small OEIS conjecture and a complete route using mature arithmetic-function
ingredients, with no equivalent whole settlement located in the checked
scope. The tier does not assert global unsettledness or priority.

The bounded primary-source reading retained in the source note and
[preregistration #27597](https://github.com/the-omega-institute/trureturing/issues/27597)
distinguishes the following results from the whole nested-quotient assertion:

- Toth, *A Survey of Gcd-Sum Functions* (2010), records the arbitrary-weight
  single-gcd Cesaro identity and the divisor formula for H:
  https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.tex.
- Bordelles, *A Multidimensional Cesaro Type Identity and Applications*
  (2015), Proposition 2, concerns arbitrary complex functions of separate
  gcd(i_j,n) coordinates. Its later complete-multiplicativity assumptions
  do not supply this unrestricted conclusion:
  https://cs.uwaterloo.ca/journals/JIS/VOL18/Bordelles/bord21.tex.
- Shonhiwa, *Investigations in number theoretic functions* (1996), Chapter 2,
  printed pp.51–87, contains single-gcd Cesaro, weighted-lcm and beta/gamma/H
  divisor identities. No equivalent whole assertion was located in that
  inspected chapter. Its institution record is
  https://researchrepository.wvu.edu/etd/9760/ and DOI is
  https://doi.org/10.33915/etd.9760. The obtained archived institution PDF is
  https://web.archive.org/web/20261021155450id_/https://researchrepository.wvu.edu/cgi/viewcontent.cgi?article=10757&context=etd.
- The retained readings of Toth (1998), U338, von zur Gathen et al. (2004),
  El-Farrah (2015), Haukkanen (2025), arXiv:1306.1020 and arXiv:2110.07271
  concern regular gcds, cyclic-group averages, subgroup expectations,
  semilattice identities or Menon-type ingredients. They are not located
  whole-target settlements. Their exact locators and reading scopes are in
  the preregistration; no comprehensive fresh rereading is claimed.

The whole-statement search covered existing D5 declarations, including
private suppliers, pinned Mathlib, the source histories and the bounded
literature above. Mathlib's gcd periodicity, complementary-divisor sums,
totient multiplicativity and ArithmeticFunction convolution laws are reused.
The old f=id result and Manyama's equivalent A373059 formula concern that
specialization. They are not new resolutions of the arbitrary-function
assertion. Current repository issue searches for A350900 and the exact phrase
"arbitrary arithmetic function" returned 5 and 8 hits respectively, with
`incomplete_results=false`; no whole-target ownership collision was located.
These index searches do not establish global absence.

No corresponding theory volume or digestion source/atom was located in the
relevant A350900, Schulte and gcd-quotient searches. The canonical route is
deposit-uncovered; there is no invented theory or atom precondition.

Both Gould–Shonhiwa, *Functions of GCD's and LCM's*, Indian Journal of
Mathematics 39(1) (1997), 11–35, and Shonhiwa–Gould, *A generalization of
Cesaro's function and other results*, 39(2) (1997), 183–194, remain unread.
The thesis is not established to be either article. A verified equivalent
whole prior settlement disqualifies the external-resolution admission basis.

## Route

The proof preserves the original square and proceeds by the following
identities, with no additional hypothesis on the arbitrary weight.

1. Replace 1..n by 0..n-1 in each index. The endpoint values coincide.
   Gcd associativity and commutativity rewrite the inner argument as
   g/gcd(g,k), where g=gcd(i,n).
2. Split the inner sum into n/g complete periods of length g. Group one
   period by e=gcd(g,k), whose multiplicity is phi(g/e), and reindex d=g/e.
   The inner sum becomes `(n/g)*Sum_{d|g} phi(d)*f(d)`.
3. Group the outer index by g=gcd(n,i), with multiplicity phi(n/g).
   The complex-valued fibre formula applies the frozen real-weight theorem
   F1 separately to real and imaginary parts.
4. Let G be the pointwise product of the zero extension of f with phi,
   B=id pointwise-multiplied by phi, and Z=zeta, one on positive integers
   and zero at zero. With stars now denoting Dirichlet convolution,
   H=B*Z and the regrouped square is `B*(Z*G)=G*(B*Z)`. Expand the last
   expression to obtain the unrestricted source identity.
5. Pinned normalized multiplicativity of totient, id and zeta, and closure
   under pointwise multiplication and Dirichlet convolution, give the
   conditional source clause, including one. Quotient positivity removes
   dependence on the extension value at zero. Natural-cast distribution
   through the two original sums gives the f=id bridge to F2.

The namespace below is
`D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution`. A consumer listed
in a row gives the directed dependency `consumer -> row declaration`.
All theorem rows have `proof_shape: bind-only` and `escape_witness: null`.
Helpers are admitted only as live consumed auxiliaries of the one result;
the host's `admission_basis` is `open-problem-resolution`.

| Declaration | proof_shape | Actual consumers | Direct frozen suppliers | Frozen suppliers after inlining this delivery |
| --- | --- | --- | --- | --- |
| gcd_sum | bind-only | inner, square_AF | F1 | F1 |
| sum_periodic | bind-only | inner | none | none |
| icc_range | bind-only | square_range | none | none |
| inner | bind-only | square_AF | none | F1 |
| square_range | bind-only | square_AF | none | none |
| G_apply_pos | bind-only | inner_AF, identity | none | none |
| B_apply | bind-only | H_eq, square_AF | none | none |
| H_eq | bind-only | identity | none | none |
| inner_AF | bind-only | square_AF | none | none |
| square_AF | bind-only | identity, closure | none | F1 |
| identity | bind-only | result | none | F1 |
| phi_mult | bind-only | closure | none | none |
| lift_mult | bind-only | closure | none | none |
| closure | bind-only | positive_closure | none | F1 |
| quotient_fidelity | bind-only | square_congr_positive | none | none |
| square_congr_positive | bind-only | positive_extension | none | none |
| positive_closure | bind-only | result | none | F1 |
| positive_extension | bind-only | result | none | none |
| row_sum_specialization | bind-only | result | F2 | F2 |
| result | bind-only | none (terminal source assertion) | F2 | F1, F2 |

All rows except result are private theorems. The following ten declarations
are definitions/adapters, with `proof_shape: not-applicable(definition)`;
none supplies escape content or a computational-utility claim.

| Definition | Actual consumers |
| --- | --- |
| square | A, square_range, square_congr_positive, row_sum_specialization |
| H | H_eq, identity, result |
| positiveLift | A, positive_closure, positive_extension, row_sum_specialization |
| A | positive_closure, positive_extension, row_sum_specialization, result |
| PositiveMultiplicative | positive_closure, result |
| lift | G, G_apply_pos, lift_mult |
| phi | G, B, phi_mult |
| G | G_apply_pos, inner_AF, square_AF, closure |
| B | B_apply, H_eq, square_AF, closure |
| Z | H_eq, inner_AF, square_AF, closure |

The last five definitions are private. Definitions have no additional direct
frozen supplier. The only frozen declaration references that survive
same-delivery inlining of the whole result are:

- F1: `D5/S3/Arith/RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity`,
  statement_id `sha256:de849381304118b256c3345a1bbe4e028f7bba2321af201dbc30705812d48947`,
  source SHA256 `2862249a6ff1c0322415ef7ef41eb891fba0a3b8ad29db9d0ec15c78765c5064`.
- F2: `D5/S3/ArithSums/SchulteGcdQuotientRowSumConvolution.rowSum`,
  statement_id `sha256:87afb46a2ac278ee3a3f9b1ebbd977940ba6ffa98542b03630b924cff7ea1deb`,
  source SHA256 `8ed252e5e9059f766040badd8f8358dca74394fab7d3f60122f3894d647a155f`.
  F2 is a frozen definition used in the result's row-sum clause, not an
  additional mathematical resolution.

Finite-block splitting, gcd normalization, divisor reindexing, casts,
existing pointwise/Dirichlet closure and conjunction packaging account for
the bind-only classification. Only the positivity projection of
quotient_fidelity survives through square_congr_positive; its exactness and
divisor fields are checked fidelity facts, not live escape content. No
unused companion or compiler-generated equation is credited as new content.

`utility: none`: every declaration concerns an unbounded symbolic function,
identity, transport or multiplicativity law. None has finite enumeration,
checking infrastructure, numerical reduction or a certified finite instance
as its main content. Other computational-utility fields are not applicable.

`question_answered`: the complete quoted arbitrary-function assertion,
registered before native target work in #27597, including its multiplicativity
and identity-weight interpretation.

`dominating_theorem_search`: `not-found-in-searched-scope` for an existing
whole settlement, after the repository/private, pinned-Mathlib and bounded
primary-literature comparison above. Existing general ingredients were found
and directly reused; neither their instantiation nor the old f=id result is
presented as a new general theorem or a separate solution.

## Falsifier

A counterexample would be a positive-domain complex function f and positive
n with unequal original-square and divisor-convolution values, or a
normalized multiplicative f and positive coprime a,b violating the consequent
(including normalization at one). A positive n and indices for which the
denominator does not divide the numerator, or dependence on the chosen
extension value at zero, would refute source fidelity. Failure of an audit
encoding is not such a counterexample. A verified equivalent whole prior
settlement invalidates the external-resolution qualification, not the Lean
identity.

## Evidence

The canonical mathematical source is
`D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.lean`, SHA256
`b79b73b381c310ede71aa5148063f3a809d6facd2a88ce6b70e2baea1d1dd481`.
Its retained source unit has base
`5f96fce7d1fb35e25954e40160c2be097126744c` and accepted tip
`3d569f7e3b970b3d5fcfc2455c1864beff1dbe13`. The public delivery integrates
dev `85dab17712f6bfa756241985ccd1ea01a31e46f5`; the complete publication tip
and cumulative diff are identified by the delivery PR. The frozen module is
addressed by
`Golden/Frozen/state/D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution.lean.json`.
The whole result's statement_id is
`sha256:c181e35eae2fb544678d11048f7262311f925e935b8b5635603b35997ca15812`.

| Source clause | Exact Lean counterpart |
| --- | --- |
| Arbitrary complex values on every positive integer | result's `f : PNat -> Complex`; no premise for the first conjunct |
| Every positive n, with no finite bound | first conjunct `forall n : Nat, 0 < n -> ...` |
| Original complete ordered square, diagonal included | independent square definition, two `Finset.Icc 1 n` sums; A composes it with positiveLift |
| Exact positive natural quotients | quotient_fidelity: positivity, q*denominator=numerator, q divides n; gcd divisibility supplies exactness |
| Pointwise f*phi, then Dirichlet convolution with H | first conjunct's divisor sum; H independently sums e*phi(e) |
| Normalized coprime multiplicativity, including one | second conjunct, PositiveMultiplicative, A f 1=1 and all positive coprime products |
| No restriction at zero | third conjunct quantifies every complex extension value z and every positive n |
| f=id gives the row sums | fourth conjunct for every natural n, including the common empty-sum value at zero; F2 is cast into Complex |

The accepted whole proof and current source-bound scoped evidence have only
`Classical.choice`, `Quot.sound` and `propext` in their axiom closure, with no
sorry or private axiom. This applies to all 30 authored included declarations;
the additional nine owner report rows are compiler internals, not extra
authored theorems. The six public definitions/result nodes have canonical
Scribe exposition of all four result conjuncts. The first canonical deposit
precedes the typed `OpenProblemResolutionClaim(Proved)` binding to this dossier.

The preregistration's immutable original body SHA256 is
`e1e39c7668d64ef4eb0d8437f220a18e94641e1a578643c86ea4fbac4caeb593`.
The successful native proof belongs to its already completed original
one-hour slot. This delivery resets no timing or forecast event and makes no
240-second or new prospective-credit claim.

The public source-bound audit remains **unfinished** under
[issue #27610](https://github.com/the-omega-institute/trureturing/issues/27610).
The faithful author attempt compiled, but the binding was
`declared_unresolved`: IE-C050 ClosedTruthReadout, `forbidden_dependency`,
`source.unsafe_or_external`, operand/readout `Nat.decLt`. The missing evidence
is a lawful enrolled-template/source-operand binding certificate for the
actual complete source. There is no retained invalid Reg source or placeholder
target and no claim of `declared_validated`. Delivery uses the CLAUDE §3.9
linked-issue exception; compilation, freezing and a typed resolution claim
do not complete this audit.

## Triage

`theorem`; the exact source assertion has the unrestricted identity and
conditional normalized multiplicativity described above.

- **Proved, in the whole result:** divisor convolution evaluates the original
  square for every positive-domain complex weight, including weights without
  any multiplicativity property. The decisive structure is complete-period
  gcd-fibre counting, not a restriction on f or an experimental finite range.
- **Proved, in the whole result:** multiplicativity is inherited under the
  normalized coprime law. Its value at one is part of the conclusion, so this
  result supports the source's multiplicative-sequence interpretation without
  silently substituting complete multiplicativity.
- **Proved, in the whole result:** the statistic ignores every extension value
  at zero and agrees with the existing rowSum at f=id. That bridge preserves
  the previously known specialization; it supplies no separate resolution.
  No additional downstream paper theorem depending on the full COMMENTS
  assertion was identified in the bounded inspected sources.
- **Applicability boundary:** n>0 supplies positive gcd denominators and
  complete periods of every divisor g. An arbitrary truncated rectangle or
  unordered triangle does not supply this exact-period step. No theorem for
  those domains, signed indices or infinite sums is asserted here.
- **Unresolved here, proposed generalization only:** determine which other
  coefficient semirings or rings support the same weighted counting identity.
  The present complex proof uses real/imaginary application of F1 and existing
  Complex arithmetic-function instances; it does not establish that general
  codomain statement.
- **Unresolved here, adjacent questions:** characterize truncated-rectangle
  boundary terms; determine an inverse or converse-multiplicativity statement
  for the transform f -> A_f; and address the separate triangle-symmetry
  assertion. These are research questions, not named new claims or a claim
  that the questions are globally open. They need their own source/literature
  qualification and any later Lean admission.

## ASSUMED-UNVERIFIED

Both 1997 originals, the complete later citation network, uninspected older
A057660 history, the 2008 Dirichlet-series catalogue and global historical
priority remain outside the verified scope. The thesis is not a substitute
for either unread article. Failed access and bibliographic mentions are not
negative evidence. A whole prior settlement remains possible outside the
searched scope and would disqualify the external-resolution basis.

The source-bound public audit is unfinished as specified in #27610; no lawful
binding certificate is delivered. No global absence, novelty, solution count,
strict timing credit, completed delivery review, required-CI success or merge
is inferred from the mathematical result or resolution metadata.
