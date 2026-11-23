---
bibkey: pomerance2026makowski
authors: Carl Pomerance
year: 2026
title: "A bound for the Mąkowski–Schinzel conjecture concerning the arithmetic functions σ and ϕ"
doi: null
url: https://math.dartmouth.edu/~carlp/msconj2.pdf
claim: "Ranges n ≤ 10^60 and P(n) ≤ 10^6; §4 (p. 7) remarks without proof that rad(φ(n)) | 30 implies α(n) ≥ 1/2."
strata_touched:
  - D5/S3/Arith/Divisors/MakowskiSchinzel/Main
  - D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main
license: citation-only
triage: anchor
---

# Numerical ranges and a smooth-totient remark for the Mąkowski–Schinzel conjecture

Carl Pomerance, *A bound for the Mąkowski–Schinzel conjecture concerning the
arithmetic functions σ and ϕ*, preprint, version dated November 22, 2026.

The abstract states that the conjecture `σ(φ(n)) ≥ n/2` holds for every `n`
divisible only by primes at most `10^6`, and for every `n ≤ 10^60`. These are
literature ranges, separate from the condition `η(n)≤42` in the formal theorem
of `MakowskiSchinzel/Main`. No equivalence or implication between these
conditions is asserted, and these numerical claims are not Lean-verified results
here.

Section 4, page 7, contains the remark, quoted verbatim: "We remark that with a
little extra work one can show that if rad(ϕ(n)) | 30, then α(n) ≥ 1/2. That
is, the Mąkowski–Schinzel conjecture holds for those n with P(ϕ(n)) ≤ 5. It is
likely that this type of result can be further extended." The preprint gives no
proof of this remark.

The formal theorem of `MakowskiSchinzel/SmoothPredecessor/Main` assumes that
`q-1` is `97`-smooth for every prime divisor `q` of `n`. Since `q-1` divides
`φ(n)` for every prime `q | n`, the condition `rad(φ(n)) | 30` implies this
hypothesis, so the remark is a special case of that theorem.

## Verified locator

URL: https://math.dartmouth.edu/~carlp/msconj2.pdf.
Version dated November 22, 2026; abstract on page 1; the remark at the end of
Section 4 ("No small counter-examples"), page 7.
