---
slug: mo515594-original-pascal-hadamard-positivity
bibkey: vsp2026pascalhadamard
doi: null
url: https://mathoverflow.net/questions/515594
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation
---

# Original Pascal Hadamard-minor positivity question

## Problem

VSP, MathOverflow 515594, original revision 1,
GUID 24043C19-8B17-4527-819F-D0DAEA1E8F86:

> Let $A = \left[\binom{i}{j}\right]$ for $0 \leq i,j \leq n$.
> We know that A is totally nonnegative, i.e., all its minors are nonnegative.
> Consider the matrix $A^{\circ r}=\left[\binom{i}{j}^r\right]$, where $r>0$ is real.
> Can we say that every minor of lower triangular matrix $A^{\circ r}$ below
> the main diagonal are positive, i.e. $\det(\binom{i}{j}^r)>0$ for
> $i=\alpha_1,\ldots,\alpha_k$, $j=\beta_1,\ldots,\beta_k$, and
> $\beta_1<\ldots<\beta_k<\alpha_1<\ldots<\alpha_k$?

Source: https://mathoverflow.net/questions/515594.
Exact revision: https://mathoverflow.net/revisions/24043C19-8B17-4527-819F-D0DAEA1E8F86/view-source.
Attributed to [VSP](https://mathoverflow.net/users/126770/vsp) under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The quotation normalizes mathematical spacing and omits the closing request
for help. The adaptation expresses the lists as Fin(k) functions, makes all
natural bounds explicit, and supplies an exact counterexample. The adapted
source exposition is shared under the same license.

The full assertion quantifies over every natural n and k, every pair
alpha,beta : Fin k -> Nat, and every real r>0. Each list is strictly
increasing, every index is at most n, and beta(j)<alpha(i) for every i,j.
The conclusion is det(Matrix.of((i,j) -> (Nat.choose(alpha(i),beta(j)) : Real)^r))>0,
with real rpow. For k=0, the determinant is one; this true additional case
does not change the original positive-size assertion's truth value.

The later appended all-size nonvanishing question for r>1 remains unresolved.
This dossier concerns only the independently posed original r>0 assertion.

## Motivation

The question asks whether strict separation protects Pascal minors against
the known general failure of total positivity under fractional Hadamard powers.

## Gap

The original full assertion was preregistered before the native probe:
https://github.com/the-omega-institute/trureturing/issues/18834.
It is an externally posed question from 2026. Bounded source
qualifications found no identified prior complete answer for this fixed
Pascal-family assertion. The inspected Hadamard-power section and
corrigendum of Fallat-Johnson-Sokal, arXiv:1612.02210v2,
DOI 10.1016/j.laa.2017.01.013 and DOI 10.1016/j.laa.2020.12.019,
give general TN/TP results and counterexamples, not an established answer
for this exact Pascal family. Their rank-two Hankel example has determinant
zero before powering, whereas the present Pascal minor has determinant one;
positive diagonal rescaling does not identify them.

The bounded qualifications also inspected selected related MO bodies and
Crossref/arXiv records. The Ashrafi-Gibson symmetric-Pascal article,
DOI 10.1016/j.laa.2005.02.041, was inaccessible; its material hypotheses and
any hidden implication remain unverified. Its title does not exclude prior
coverage. Worldwide priority, inaccessible material and uninspected equivalent
arguments remain unknown. General fractional-power failure alone is not a
novelty claim. Established prior complete coverage would give zero new-question
credit. No exhaustive literature clearance is claimed.

## Route

Choose n=5,k=3,alpha=(3,4,5),beta=(0,1,2),r=1/10.
The original strict separation is 0<1<2<3<4<5. The unpowered selected matrix
is [[1,3,3],[1,4,6],[1,5,10]], of determinant one. The actual Matrix.det_fin_three
expansion and Real.mul_rpow give
D=40^(1/10)+18^(1/10)+15^(1/10)-2*30^(1/10)-12^(1/10).
For q=1000000, exact tenth-power comparisons give upper numerators
1446126,1335142,1311020 for the roots of 40,18,15 and lower numerators
1405115,1282088 for the roots of 30,12. Hence
D<(1446126+1335142+1311020-2*1405115-1282088)/q=-30/1000000<0.

The proof applies the pinned determinant and real-power identities and exact
rational normalization. Every helper theorem has proof_shape: bind-only and
is used on a live proof path. The consumers are:

- `witness_det_negative` -> `witness_det_formula`;
- `witness_det_negative` -> `root_upper`;
- `witness_det_negative` -> `root_lower`;
- `result` -> `witness_det_negative`.

Here each arrow points from consumer to prerequisite. No private helper is a
separate mathematical contribution. The public theorem's direct project
frozen dependencies are empty; it reuses the pinned Mathlib determinant,
real-power and order results. The designated literal conclusion
result : Not claim has proof_shape: bind-only and
admission_basis: open-problem-resolution under issue 18834. No independent
content or priority claim is made for the helper chain.

## Falsifier

A mismatch between the original complete claim and its natural-index,
real-rpow determinant encoding, a failed exact tenth-power comparison, or
a missing proof of strict separation would invalidate this counterexample.
A prior complete equivalent answer would invalidate new-question credit.

## Evidence

The designated theorem is
`D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation.result`.
Its compiled type is literally `Not claim`, and `claim` has type `Prop`.
The corresponding Blueprint Scribe records a Refuted resolution of this
original question. The definitions use actual binomial entries and an
ordinary determinant; no abstract replacement family is assumed.

The mathematical input is the fixed Pascal family Nat.choose, every natural
n and k, strictly increasing bounded natural index lists, complete strict
separation, and every positive real exponent. The negation needs one actual
admissible minor, rather than a finite replacement for the original quantifiers.

### Current frontier

The later r>1 nonvanishing question, global literature priority and any
uninspected equivalent prior result remain unresolved. A single refuted
universal original question counts at most once after full accepted delivery.

## Triage

The literal universal positivity assertion is refuted by the admissible
negative determinant at exponent one tenth. One public theorem `result`
and its consumed private chain suffice. The appended r>1 question is
outside this conclusion. No extra theorem or new-question credit follows
from the helper identities.

### What the settlement shows

The proved refutation (the `result` GID above, using its consumed
`witness_det_negative` helper) shows the failure mechanism: strict row/column
separation and positive binomial entries do not preserve determinant positivity
under real fractional entrywise powers. At the same admissible witness even
nonnegativity fails, since the determinant is strictly negative. The
unpowered witness has determinant one, as the explicit matrix in Route shows;
this is not a counterexample created from an already singular minor.

The empty-minor case remains true with determinant one, as recorded in the
source bridge. No repaired all-size positivity range is established here.
The appended r>1 nonvanishing assertion remains open, so it is neither refuted
nor proved by this exponent-one-tenth example. No other result or question
in the source is claimed settled; only the original universal assertion is
refuted. Any proposed repaired range needs its own source qualification and
proof and is not an additional settlement in this dossier.

## ASSUMED-UNVERIFIED

Worldwide priority and inaccessible or uninspected equivalent prior arguments
remain unknown. The bounded qualifications are reused without an
exhaustive literature claim. The appended r>1 nonvanishing question is open.
