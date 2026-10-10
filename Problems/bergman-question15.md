---
slug: bergman-question15
bibkey: bergman2014eggert
doi: 10.1090/conm/609/12101
url: https://arxiv.org/abs/1206.0326v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result
---

# Bergman's Question 15

## Problem

Bergman, *Thoughts on Eggert's Conjecture*, Question 15, asks:

> Suppose X is a finite subset of a commutative semigroup S with zero, n a
> positive integer such that the n-th power map is one-to-one on X and does not
> take any nonzero element of X to 0, and F a field of characteristic 0. Must
> every nonzero element of the span FX of X in F_0 S have nonzero n-th power?

The semigroup is associative and commutative with absorbing zero, with no
identity or finiteness assumption. The field is arbitrary of characteristic
zero. The subset may be empty or contain zero. The algebra is the free vector
space on the nonzero semigroup elements, with the semigroup zero sent to the
zero vector.

| Source clause | Lean meaning |
| --- | --- |
| arbitrary commutative semigroup with zero | `S : Type`, `SemigroupWithZero S`, `IsMulCommutative S` |
| characteristic-zero field | `F : Type`, `Field F`, `CharZero F` |
| finite subset | `X : Set S`, `X.Finite` |
| positive exponent | index `n : ℕ` represents exponent `n+1` |
| positive power without identity | `positivePower a 0 = a`, followed by repeated multiplication by `a` |
| injective power map on X | `Set.InjOn (fun s => positivePower s n) X` |
| nonannihilation on nonzero X | `∀ s ∈ X, s ≠ 0 → positivePower s n ≠ 0` |
| contracted algebra | `Contracted F S = {s : S // s ≠ 0} →₀ F` |
| contracted zero | `delta F S 0 = 0` |
| linear span | `Submodule.span F (delta F S '' X)` |
| claimed conclusion | every nonzero vector in this span has nonzero positive power |

The utility claim is closed over ordinary small carriers (`Type`), including
arbitrary infinite semigroups and fields. The algebra definitions remain
universe-polymorphic. The finite counterexample lies in these universes and
therefore also refutes the unrestricted mathematical question; no
finite-carrier restriction is imposed on the universal claim.

## Motivation

Distinct nonzero pure powers need not prevent cancellation among mixed
monomials. A primitive cube root makes three retained terminal coefficients
vanish simultaneously in characteristic zero.

## Gap

Injectivity controls the pure powers of the selected basis elements. It does
not constrain cancellation among mixed monomials in their linear span. The
counterexample must realize that cancellation in the actual contracted
algebra while satisfying every original antecedent.

## Route

Keep every positive exponent triple of degrees 1 through 5 as a singleton.
At degree 6 retain exactly the following three terminal classes:

| Class | Triples |
| --- | --- |
| A | (6,0,0), (3,3,0), (5,1,0), (5,0,1), (2,4,0), (4,2,0) |
| B | (0,6,0), (0,3,3), (0,5,1), (1,5,0), (0,2,4), (0,4,2) |
| C | (0,0,6), (3,0,3), (1,0,5), (0,1,5), (4,0,2), (2,0,4) |

All other degree-6 monomials and every higher-degree monomial become zero.
Multiplication adds exponents and applies this rule; a terminal element times
any element is zero. There are 59 elements and 58 nonzero basis labels.
The explicit finite table's associativity, commutativity and absorbing laws
are obligations checked inside its structure instances.

For X = {x,y,z}, exponent 6 and F = ℂ, the generator powers are the distinct
nonzero classes A,B,C. Put w = delta_x + ζ delta_y + ζ² delta_z, with ζ a
primitive cube root. The x coefficient is 1. Bilinear expansion gives each
terminal coefficient as 21(1+ζ+ζ²), hence zero. Positive-power expansion uses
no identity. The generic contraction's algebra laws are proved inline by
Finsupp induction and the original semigroup laws.

## Evidence

[Issue 15095](https://github.com/the-omega-institute/trureturing/issues/15095)
preregistered the literal question and the three exact terminal classes before
Lean probes. The external named final-result exception in AGENTS §3.2 applies:
`admission_basis: open-problem-resolution`, `proof_shape: bind-only`, with no
escape-witness claim. The only authored theorem is `result : ¬ claim`.

The question is Tier 1, a numbered subsidiary question with a short ordinary
countermodel. Its settlement is suspected-novel within bounded readings.
Fresh 2026-10-10 readings include arXiv v2, the author TeX/PDF and publication
index, Crossref metadata, arXiv all-field Eggert search (50 results),
MathOverflow advanced Eggert search (100 items), and Crossref top 10
bibliographic results. No Question-15 settlement was found in usable results.
Bergman's arXiv:1309.0053v1 discusses a different Question 15. Hammoudi's
2005 correction (DOI 10.2140/pjm.2005.220.197) does not settle Question 15.
Bergman's author TeX, lines 1335–1338, rejects both Hammoudi's full proof
and the erratum's claim of validity for the graded case. These readings give no worldwide
absence or priority guarantee. Blocked publisher access and rate-limited
searches are capability limits, rather than nonhits.

Pinned D5 searches include private declarations and reveal no exact supplier.
Mathlib supplies Finsupp linear extension and induction, semigroup laws,
primitive complex roots and their geometric sum. Its uncontracted monoid
algebra does not impose delta_zero = 0; its unital multinomial theorem does
not directly apply here. The bounded third-party reading of
lean-summer-research/lean-semigroup at
763be74d575a22c8dbb68a52c09367ab8a719fc3 supplies Green/Rees infrastructure,
with different pins and no established compatible license, and supplies no
located Question-15 answer. No code is transplanted.

## Falsifier

A mismatch in the absorbing multiplication, contraction, finite subset,
positive-power indexing, field characteristic, or nonzero witness invalidates
the proposed negative answer. An ordinary table computation does not replace
kernel verification. The target is the literal universal claim, rather than a
theorem assuming the displayed coefficient cancellation.

No assertion is made about Question 11, Question 16, Eggert's conjecture,
minimal semigroup size, minimal exponent, or all fields or exponents.

## Triage

Calculated: the exact 59-element table is associative and commutative with
absorbing zero, and the three generator sixth powers are distinct and nonzero.
The displayed vector has x coefficient one and zero sixth power. Proved: the literal
Question-15 assertion is refuted by this actual contracted complex semigroup
algebra. The positive-power index 5 is exponent six; the proof assumes no
finite identity or desired coefficient cancellation.

Ordinary mathematical consequence: retaining independent degree-six
monomials in the free commutative semigroup prevents this cancellation,
because each pure sixth-power coefficient separately reads the corresponding
scalar's sixth power. Identifying mixed and pure monomials into terminal
classes removes that separation. No general sufficient-condition theorem is
claimed here.

Calculated: the product-set sizes 3,6,10,15,21,3 in this example satisfy the
size inequality asked in Question 11. Open: Question 11, Question 16,
Eggert's conjecture, other fields or exponents, and minimality of this model.

## ASSUMED-UNVERIFIED

The settlement is suspected-novel within the bounded source and literature
readings in Evidence. Worldwide absence of an earlier settlement and priority
are unverified. The designated literal refutation result is exempt from the
four-slot audit; no four-slot registration or broader mathematical result is
claimed.
