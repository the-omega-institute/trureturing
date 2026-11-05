---
slug: oeis-a208509-affine-polynomial-pair-binomial-coefficients
bibkey: werner2022a208509
doi: null
url: https://oeis.org/A208509
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.werner_a208509
---

# Werner's all-column formula for the affine polynomial pair

## Problem

OEIS A208509 revision 28, FORMULA, attributes this conjecture to Knud Werner:

> Conjecture: T(n,k) = binomial(n-1,2*k+1) + binomial(n,2*k+1). - _Knud Werner_, Jan 11 2022

Clark Kimberling authored the sequence entry. Its companion A208508 revision 10
supplies the jointly generated first polynomial. The complete defining laws are
u(1,X)=v(1,X)=1, u(n,X)=u(n-1,X)+X*v(n-1,X), and
v(n,X)=u(n-1,X)+v(n-1,X)+1 for every n>=2, over Z[X].
For every natural n>=1 and every natural k>=0, T(n,k) is the coefficient of
X^k in this actual v(n,X), including all zero coefficients beyond its degree.
The formula's two natural binomial coefficients are cast to integers.
No assertion at n=0 is included.

## Motivation

The identity gives every coefficient of an unbounded family specified by a
coupled affine polynomial recursion. It connects that actual recursion to a
closed binomial expression without restricting rows, columns or degree.

## Gap

The bounded source and literature screen recorded in
`Library/RecurrenceComposition/werner2022a208509.md` found no complete proof or refutation
of this exact conjecture. The private-inclusive repository, pinned Mathlib
and third-party Lean screen found no full supplier. The frozen A208342 pair
has v_next=X*u+X*v and a different endpoint; no identification with this affine
second family was established. Elementary coefficient and Pascal identities
supply normalization, while the coupled coefficient invariant supplies the
missing whole-family argument. These findings do not establish global openness
or priority; unavailable searches are not zero-hit searches.

## Route

Use the actual pair recursion with stage m corresponding to source index m+1.
Simultaneously maintain, for every natural m,k, the first coefficient
choose(m,2*k)+choose(m+1,2*k)-[k=0] and the second coefficient
choose(m,2*k+1)+choose(m+1,2*k+1), interpreted in the integers.
The odd successor uses both preceding components. The even successor uses the
shifted odd component, with k=0 handled separately. Pascal identities close the
coupled steps; the degree-zero correction cancels the affine constant.
Project the second component at stage n-1 and use n-1+1=n for n>=1.

## Falsifier

A natural n>=1 and k>=0 for which the coefficient of X^k in the polynomials
from precisely the two initial values and both recurrences differs from the
stated integer binomial sum would refute the conjecture. A failure of either
component of the simultaneous invariant, the affine cancellation, or the
source-stage identification would invalidate this proof route. Agreement on a
finite prefix or a single column cannot prove the universal statement.

## Evidence

The single current public proof endpoint is
`D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.werner_a208509`,
with statement_id
`sha256:2611e9479e93d268bcc052fadc93f7932faa6757d6162378face9f7003475552`.
Its owning module is
`D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.lean`;
its current frozen member is
`Golden/Frozen/state/D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients.lean.json`.
The actual definition `pair` and the proof-local simultaneous invariant are
consumed by this endpoint; no second theorem or finite certificate is claimed.
The owning Scribe records the typed proved-resolution edge for this dossier.

The source statement and full indices were preregistered as Tier 1 before the
probe in [#26010](https://github.com/the-omega-institute/trureturing/issues/26010#issuecomment-6597349343).
The admission basis is `open-problem-resolution`; `utility: none` describes
this unbounded symbolic proof. The public theorem has `proof_shape: content`
through its live coupled invariant. Local arithmetic and normalization helpers
are bind-only and consumed by the invariant or final index transport; induction
syntax alone is not the content criterion. The theorem's accepted axiom closure
is `propext`, `Classical.choice`, and `Quot.sound`.

The original source snapshots are:

- A208509 revision 28: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A208/A208509.seq,
  SHA-256 `aad0c0fd287110c8b9f5ca1f7c4d4af77bbe3e71dcf284faf7e6baba1efb6c5a`.
- A208508 revision 10: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A208/A208508.seq,
  SHA-256 `c88c749749f5e4944ef974eab6217576a5195f85fd65a34f671aa5f4e53d3175`.

## Triage

`theorem`: the cited frozen endpoint proves the complete all-column conjecture
for the actual second polynomial, every n>=1 and every k>=0, including zero
tails. The first-component formula remains proof-local; it is not a separate
public result.

### What the settlement shows

- Proved by the cited endpoint: the coupled affine recursion has the stated
  odd-binomial coefficient formula throughout the full declared index range.
  The decisive mechanism is the simultaneous even/odd coefficient invariant
  and its degree-zero correction, which absorbs the added constant.
- Proved internally on the endpoint's live path: the first-component invariant
  is needed to propagate the second component, and the shifted second component
  propagates the first. This explains why an isolated second-component Pascal
  rewrite does not supply the whole induction.
- Open: changing the initial polynomials, the coefficient of X, the affine
  constant, or the coefficient ring requires a new statement and corresponding
  proof. This result supplies no such generalization. There is no finite range
  or numerical bound whose sharpness is being claimed.
- Supporting consequence: the exact A208509 conjecture can be used in its stated
  source range. No further source theorem depending on it was identified by the
  bounded screen. Consequences for other entries or conjectures, including an
  independent public A208508 endpoint, remain unasserted here.

## ASSUMED-UNVERIFIED

The bounded literature and supplier screen does not prove worldwide openness,
originality, exhaustive absence of a stronger supplier, or publication priority.
Semantic Scholar returned 429 and other restricted searches did not provide
usable coverage. The source-to-Lean interpretation is supported by the explicit
recursion, index correspondence and independent fidelity review; natural-language
source equivalence is not itself a kernel theorem. The typed resolution edge
records this repository's claim about the cited frozen result and does not
certify the conjecture's status elsewhere. Generalizations and unexamined
source-dependent consequences remain open.
