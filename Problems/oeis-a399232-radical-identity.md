---
slug: oeis-a399232-radical-identity
bibkey: ferreira2026a399232
doi: null
url: https://raw.githubusercontent.com/oeis/oeisdata/2ce625d68f85e35e26e15c0d9681f69280c095e7/seq/A399/A399232.seq
triage: theorem
motivation_gids:
  - D5/S1/Deficit/AlmostAdditivity
---

# OEIS A399232 radical identity

## Problem

Rui Ferreira's first COMMENT in OEIS A399232 is:

> a(n) appears to satisfy rad(2*n+1) = (2*n+1)^2 / ((2*n+1)^2 - a(n)).

Its NAME is:

> a(n) = Sum_{k=1..4*n+2} (k^(4*n+1) mod (2*n+1)).

OFFSET `1,1` gives the domain `n >= 1`. The literal finite sum uses least
nonnegative natural remainders. The radical is the product of distinct
prime divisors. The full intended statement proves, for every such `n`,
strict positivity of the signed rational deficit `D=(2*n+1)^2-a(n)` and
the rational equality `rad(2*n+1)=(2*n+1)^2/D`. Natural truncated
subtraction and integer division are not the meaning of the quotient.
There is no squarefree or coprime restriction.

The immutable source is revision 23, Sep 01 2026, of the official export
at `2ce625d68f85e35e26e15c0d9681f69280c095e7`. Its author line is
`_Rui Ferreira_, Aug 23 2026`. Source quotations and adapted description
are attributed to Rui Ferreira and the OEIS Foundation Inc., under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
Source provenance is distinct from the repository proof.

## Motivation

The frozen `D5/S1/Deficit/AlmostAdditivity` uses the product of distinct
prime factors to control an arithmetic defect. The present question asks
whether a literal sum of odd-power remainders determines that same
prime-support quantity through its positive deficit. Mathlib's
`Nat.radical_eq_prod_primeFactors` identifies the radical used here with
that product. No new theorem comparing radical definitions is needed.

## Gap

The exact assertion is pre-registered in
[issue #14327](https://github.com/the-omega-institute/trureturing/issues/14327)
as a Tier 1 externally authored problem. Repository D5/private, Blueprint,
Library, Problems and digestion-content searches found no exact assertion.
The related YanevSigmaRadicalIdentity concerns divisor sums and does not
provide this odd-power remainder sum.

Bounded independent readings found OpenAlex works `A399232` count 0,
Math.SE title `A399232` items 0, and Math.SE structural query
`least nonnegative residues odd powers radical` items 0. Authenticated
GitHub code searches for `A399232 language:Lean`, formal-conjectures and
trureturing each returned count 0; global issues returned count 0.
These are bounded source-search readings, not proof of historical
openness. Stop the target if a published settlement of the same assertion
is identified.

## Route

Fix `n >= 1`, and set `m=2n+1`, `e=4n+1`, `r=rad(m)` and `q=m/r`.
Then `e` is odd and `e>=m`, while `r>0`, `r|m`, `rq=m` and `q>0`.
For each natural `x`, existing radical suppliers give

$$m\mid x^e\quad\Longleftrightarrow\quad r\mid x.$$

The forward direction is the direct application of
`exists_dvd_pow_iff_radical_dvd` with exponent witness `e`. For the
reverse direction, `Nat.dvd_radical_pow_self` gives `m|r^m`, and
`pow_dvd_pow_of_dvd_of_le` gives `r^m|x^e`. This uses the existing
generic factorization result, including the zero case.

Use the complete representatives `B={1,...,m}` and
`f(x)=x^e mod m`. The endpoint `m` represents zero. The supplier
`Nat.Ioc_filter_dvd_card_eq_div` counts exactly `q` zero values on `B`.
Periodicity `f(x+m)=f(x)` and the literal interval split into
`{1,...,m}` and `{m+1,...,2m}` give `a(n)=2S`, where
`S` is the sum of `f` over `B`.

Define the involution on these actual representatives by `t(m)=m` and
`t(x)=m-x` for `x<m`. Its residue is `-x` in `ZMod m`. Odd
exponentiation commutes with negation, and the least remainder of a
negative nonzero residue is its complement in `m`. Therefore

$$f(x)+f(t(x))+\begin{cases}m&r\mid x,\\0&r\nmid x\end{cases}=m.$$

Reindexing the sum by this involution and using the exact zero count
gives `2S+qm=m^2`, hence `a(n)+qm=m^2`. Cast this additive identity
to the rationals before subtracting. The signed rational deficit is
`D=qm>0`, and `rD=m^2` follows from `rq=m`. Division by the positive
deficit proves the exact quoted identity.

The power map is not assumed to permute residues. In particular all
prime-power and nonsquarefree moduli remain in scope. No neighboring
COMMENT or companion theorem is included.

## Falsifier

One natural `n>=1` with a nonpositive signed rational deficit or a false
quoted quotient would refute the full conjunction. Finite agreement
cannot establish the universal assertion.

## Evidence

The source SHA-256 is
`2d5409e351249e7e9d4853fea4ed5b8d0cce0c87c99dca1eab1de08cff080966`.
Its immutable fetch returned HTTP 200. The source-level proof above
uses pinned Mathlib radical, cardinality and residue-negation suppliers.
The exact theorem compiled successfully. Lean reports the axiom closure
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axiom.
Canonical report acceptance and admission checks remain pending.

## Triage

`theorem`, Tier 1. Resolution: proved for the exact universal conjunction
by the compiled theorem. Proof shape: bind-only, subject to independent
review of the actual proof. Admission basis: open-problem-resolution.
Utility: none, an unbounded symbolic identity. This mathematical
resolution does not assert canonical freezing or completed delivery.

## ASSUMED-UNVERIFIED

Worldwide absence of a prior proof and historical priority are unverified.
Live tentative wording is supported by the independent HTTP 200 source
observations; the implementation's direct request returned HTTP 403.
Canonical deposit, required checks and independent review remain pending.
