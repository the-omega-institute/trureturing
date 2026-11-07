---
slug: karttunen-a378444
bibkey: karttunen2025a378444
doi: null
url: https://oeis.org/A378444
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result
---

# Karttunen's A378444 divisor-numerator parity formula

## Problem

OEIS A378444 states the unnumbered FORMULA conjecture

$$
\forall n\in\mathbb{N},\quad 1\le n\Rightarrow
\operatorname{A378444}(n)=\left\lceil\frac{\operatorname{A174273}(n)}{2}\right\rceil.
$$

Here $\operatorname{A378444}(n)$ counts positive divisors whose reduced
numerator $\operatorname{A083345}(d)$ is even, and $\operatorname{A174273}$ is
the divisor sum of the indicator that the exponent of 2 in the factorization
is even. The exact Lean proposition is `claim` in the settling module.

### Statement echo

The source's divisor condition is mirrored by `A378444`; the reduced numerator
is `A083345`; the parity indicator is `A035263`; and the divisor transform is
`A174273`. The positivity restriction is the hypothesis `1 ≤ n`. The ceiling
is taken after casting `A174273 n` to rationals and dividing by two.

## Motivation

The formula asserts an exact identity for every positive integer, including
the boundary value $1$, odd integers, powers of two, and mixed prime powers.
The source and preregistration are issue [#23534](https://github.com/the-omega-institute/trureturing/issues/23534).

## Gap

The source records the identity as conjectured. The bounded literature screen
associated with #23534 found no complete prior proof in its searched scope.
Completeness of that screen and originality beyond the retained source are
`ASSUMED-UNVERIFIED`.

## Route

For a divisor, write the exponent at two as $a$ and the remaining prime
exponents as a finitely supported function. An odd common denominator gives
the reduced-numerator parity criterion

$$
\operatorname{A083345}(d)\equiv 0\pmod 2
\Longleftrightarrow
a\equiv 0\pmod 2\ \wedge\ (a/2+\sum_{p\ne2}e_p)\equiv0\pmod2.
$$

Halving the even exponent at two bijects the selected divisors with the even
parity part of a finite exponent box. The alternating sum over that box
factors into one-dimensional geometric sums, so its value lies between zero
and one. This forces the even-parity count to be the ceiling of half the box
size. The inverse divisor transform identifies that box size with
$\operatorname{A174273}(n)$.

## Falsifier

A positive integer $n$ for which the divisor count and the stated ceiling
differ would refute `claim`. A failure of the reduced-numerator parity
criterion, the divisor-box bijection, or the alternating-sum bound would
invalidate the proof route.

## Evidence

- Kernel-checked declaration: `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result` proves `claim`.
- The public definitions and the settling theorem are in
  `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.lean`.
- The Scribe carries one `OpenProblemResolutionClaim` with resolution
  `Proved` on the settling declaration.
- The axiom closure of every public declaration is contained in
  `{propext, Classical.choice, Quot.sound}`.
- Experiment: [exact finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/bb903f915ef2e272629d6b1de220f6b98744be4f/docs/reports/karttunen-a378444),
  script `docs/reports/karttunen-a378444/check.py`, SHA-256
  `626fa907628a90d4ba42c62229e61480a09d915698e419b6ecaad23a8a601709`.
  The immutable script is materialized at
  `/tmp/op-karttunen378444/continuation/experiment/check.py`.
  Command `python3 /tmp/op-karttunen378444/continuation/experiment/check.py --bfile-dir /tmp/op-karttunen378444/src`,
  exit 0, checks both 65537-row b-files, reduced-numerator parity on
  $1 \le n \le 65537$, and seven larger exponent boxes, with zero mismatches.
  The b-file SHA-256 values are
  `5df9ecbacda6bd7ee7ee6af0c49056b8cea3b99c1667603ad1d42700aa420939`
  (A378444) and
  `1a29482ee696937cf440f64ad9c950ce2ccd3cbf5898a605bffbe05721b4c88a`
  (A174273).
- The typed registration is in
  `Reg/D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.lean`;
  [audit record #23568](https://github.com/the-omega-institute/trureturing/issues/23568)
  records the delivered-head CI binding verdict.
- The ancillary odd-input sigma formula fails at $3$: the defining inverse
  transform gives $2$ while $\sigma(3)=4$. This is outside `claim`.

## Triage

| item | status | evidence |
| --- | --- | --- |
| The exact ceiling identity holds for every positive integer, including $1$, odd $n$, powers of two and arbitrary mixed prime powers. | proved | Kernel-checked `D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity.result`; the parity criterion and finite-box count cover these cases. |
| `r_parity` identifies the selected divisors by the compressed prime-exponent parity, including zero numerator. | proved | Kernel-checked private `r_parity`, consumed by `result`; `Rat.num` at zero is handled by the same parity statement. |
| `box_count` applies to every finite-support natural exponent bound, independent of primality or the sequence definitions. | proved | Kernel-checked private `box_count`, consumed by `result`; its statement quantifies over arbitrary finitely supported natural exponent bounds. |
| The pinned checker matches both 65537-row b-files, verifies reduced-numerator parity through 65537 and seven larger exponent boxes; exit 0, `ALL_CHECKS_OK`. | computed | Experiment commit `bb903f915ef2e272629d6b1de220f6b98744be4f`, path `docs/reports/karttunen-a378444/check.py`, SHA-256 `626fa907628a90d4ba42c62229e61480a09d915698e419b6ecaad23a8a601709`; command `python3 /tmp/op-karttunen378444/continuation/experiment/check.py --bfile-dir /tmp/op-karttunen378444/src`, exit 0. |
| The ancillary A174273 odd-input sigma formula fails at $3$: defining inverse transform gives $2$, while $\sigma(3)=4$; it is outside `claim`. | computed | The pinned checker output records the value at $3$; the discrepancy is a boundary of the ancillary formula, not of `claim`. |
| Analogous identities for other moduli or the weighted sequences A378544/A378546 are not settled by this delivery. | open | No declaration in the delivery states these extensions. |

### What the settlement shows

The decisive mechanism is the reduced-numerator parity identity followed by a
bijection to a finite exponent box and its alternating-sign product. The proof
does not assume primality of the input or restrict the support size. The
analogous modulus and weighted-sequence questions remain open.

## ASSUMED-UNVERIFIED

The literature screen is partial; completeness and originality outside the
screened sources are `ASSUMED-UNVERIFIED`. The finite computation is bounded by
the exact ranges stated above and does not replace the universal proof.
