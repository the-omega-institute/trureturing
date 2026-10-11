---
slug: fiore-nasr-stone-2026-midpoint-negativity
bibkey: fiore2026squaresideddice
doi: null
url: https://arxiv.org/html/2606.20311v1
triage: theorem
motivation_gids:
  - D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result
---

# An odd midpoint refutes Fiore-Nasr-Stone Conjecture 6.8

## Problem

The complete Conjecture 6.8 of `fiore2026squaresideddice` states:

> In the remaining 33 pairs of the polynomials A_abcd and B_(2-a,2-b,2-c,2-d) (including the case where p != 2 for when a=b=c=d=1), one of the two polynomials will have a negative coefficient.

Definition 6.1 uses distinct natural primes p,q,r and exponents a,b,c,d
in {0,1,2}. At the midpoint a=b=c=d=1 both complementary tuples are
(1,1,1,1). The two complete integer polynomials are

$$A(p,q,r)=X\Phi_p^2\Phi_q^2\Phi_{pq}\Phi_{pr}\Phi_{qr}\Phi_{pqr},$$

$$B(p,q,r)=X\Phi_r^2\Phi_{pq}\Phi_{pr}\Phi_{qr}\Phi_{pqr}.$$

The literal closed `claim : Prop` universally quantifies over natural
p,q,r with `Nat.Prime p`, `Nat.Prime q`, `Nat.Prime r`, `p != q`,
`p != r`, `q != r` and `p != 2`, and asserts that some natural-index
coefficient of A or of B is strictly negative. There is no ordering
premise, prefix bound or scalar proxy.

## Motivation

The source expressly places this midpoint in Conjecture 6.8. At
(3,5,11;1,1,1,1), all domain hypotheses hold, with all primes odd and
r maximal. Thus the whole source conjecture implies negativity for this
specific pair. The formal midpoint universal assertion also implies
that same instance. Nonnegativity of both complete polynomials therefore
refutes both assertions without an equivalence between their domains.

## Gap

Table 2 repeats (2,1,1,2); its literal distinct rows do not support the
printed remaining-case count 33. Lemma 6.6 claims that odd-prime
multiples always have even sums, but 11=2*3+5. Neither this invalid
argument nor a silently corrected remaining-case domain supplies the
refutation. The expressly included midpoint clause fixes the target
independently of those defects.

## Route

For the mathematical abbreviation $G_m(X)=\sum_{0\le j<m}X^j$, cyclotomic
expansion gives

$$A(3,5,11)=X G_3(X)G_5(X)G_3(X^{11})G_5(X^{33}),$$

$$B(3,5,11)=X\left(\sum_{s\in S}X^s\right)G_{11}(X^{15}),
\quad S=\{0,3,5,6,8,9,10,12,13,15,18\}.$$

The sum over S is exactly $\Phi_{11}\Phi_{15}$. All these sums have
nonnegative coefficients. Coefficient convolution preserves this property;
expansion X to X^k inserts zeros. The identities prove the condition at
all natural indices, including the zero tails, inside the sole result.

## Falsifier

A failure of either complete factorization, a negative coefficient at any
index, or a source convention excluding (3,5,11;1,1,1,1) defeats this
route. The source explicitly includes that instance, and no change to
its prime domain or factors is permitted.

## Evidence

The formal endpoint is
`D5/S3/Factorization/Cyclotomic/FioreNasrStoneMidpointRefutation.result`,
with literal type `Not claim`. The only other declarations are midpointA,
midpointB and the closed Prop claim. Intermediate identities remain inside
result. Direct suppliers are the frozen
`GeometricSpectrumFactorization.geometric_sum_eq_cyclotomic_product`,
Mathlib's `Polynomial.cyclotomic_expand_eq_cyclotomic_mul`,
`Counterexample.cyclotomic_15` and standard expansion/coefficient laws.
The source's Lemma 6.6 is not used.

The prospective issue is
[15471](https://github.com/the-omega-institute/trureturing/issues/15471).
The source HTML is pinned by the SHA-256 in the Library note. The source
and literature intake contains no matching valid resolution in its bounded
search; that reading does not establish global absence or priority.

## Triage

Tier 1: a recent named conjecture. The endpoint uses the external named
`open-problem-resolution` basis and has `proof_shape: bind-only`:
existing suppliers, logical composition and normalization give the
counterinstance. No escape witness or new general positivity result is
claimed. Certified-instance utility is the actual `refutes` edge from
result to claim. The Scribe attaches the Refuted claim to this sole result.

### What the settlement shows

Proved within result: the common implementation (3,5,11) satisfies every
prime-domain hypothesis and both complete midpoint polynomials have
nonnegative coefficients at every natural index. The mechanism is
cancellation in $\Phi_{11}\Phi_{15}$ followed by nonnegative geometric
factors, so parity alone cannot force a negative coefficient.

Open: a corrected necessary-and-sufficient condition for midpoint B and
the classification of the other exponent tuples. The positive-factor
mechanism remains valid for this instance and does not contradict
Corollary 6.3, whose stated coefficient test does not exclude it.
No additional case or repaired theorem is claimed here.

The necessity direction of Lemma 6.6 and the midpoint exclusion in
Conjecture 6.8 fail at this instance. Results about other exponent tuples
and earlier prime-power cases are not changed or classified by result;
any use of that midpoint exclusion must be reassessed against the
counterexample.

## ASSUMED-UNVERIFIED

The complete remaining-case assertion is not encoded.
Literature coverage is bounded, with OpenAlex/Semantic Scholar rate limits
and unavailable endpoints. Physical dice realization, exhaustive priority
and a classification of other cases are outside the formal statement.
