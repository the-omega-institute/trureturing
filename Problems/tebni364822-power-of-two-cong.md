---
slug: tebni364822-power-of-two-cong
bibkey: tebni2023a364822
doi: null
url: https://oeis.org/A364822
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.result
---

# Tebni's power-of-two congruence for OEIS A364822

## Problem

M. Tebni's OEIS [A364822](https://oeis.org/A364822), revision 25, names the sequence:

> Expansion of e.g.f. cosh(x) / (1 - 2*sinh(x)).

The conjecture resolved here is:

> For n = 2^m (m natural number), a(n) == 1 (mod n).

Preregistration: [#18644](https://github.com/the-omega-institute/trureturing/issues/18644).
The companion conjecture is recorded in [#18643](https://github.com/the-omega-institute/trureturing/issues/18643).

### Statement echo

The natural binder $m$ ranges over all natural numbers including zero. The conclusion is an integer $z=a(2^m)$ with $z\equiv1\pmod{2^m}$.
The rational formal series have coefficients $1/n!$ in even indices for cosh
and in odd indices for sinh, and zero in their other indices. The coefficient
$a(n)$ is $n!$ times the ordinary coefficient of their formal quotient.
The existential integer equals the rational coefficient after casting;
thus integrality and the congruence are both conclusions. No finite index bound
or extra hypothesis is imposed.

## Motivation

This is an explicitly published OEIS conjecture. The settling declaration is
`D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo.result`, with
`admission_basis: open-problem-resolution (#18644; Proved)`.

## Gap

The literature screen in #18644 read the OEIS entry and S. Fried's papers
arXiv:2410.07237, 2606.09913 and 2607.24832; it found no A364822 proof.
It also searched the Epoch OEIS Open benchmark, AlphaProof Nexus results,
formal-conjectures and the repository. These are bounded negative search results;
literature completeness is ASSUMED-UNVERIFIED and no priority claim is made.

## Route

Write $A(x)=\cosh(x)(1-2\sinh(x))^{-1}$. Multiplying by the
denominator gives $A=\cosh+2A\sinh$. The factorial-scaled product formula
`IntegralEGFComposition.eCoeff_mul` gives

$$
a(n)=\mathbf{1}_{2\mid n}+
2\sum_{k=0}^{n-1}\binom nk a(k)\mathbf{1}_{2\nmid(n-k)}.
$$

`IntegralEGFComposition.integral_subst` applies to the geometric series and
$2\sinh(x)$, whose constant coefficient is zero. Multiplication by cosh then
preserves integral factorial-scaled coefficients. The public theorem
`TebniA364822.num_cast` states integrality at every natural index;
`TebniA364822.num_recurrence` states the integer recurrence.
The adjacent binomial identity and coprimality with odd $k$ give $2^m\mid\binom{2^m}{k}$. At positive $m$, the remaining sinh terms have odd $k$ and vanish modulo $2^m$; the cosh term is $1$. For $m=0$, the modulus is one.

## Falsifier

A natural exponent $m$ with nonintegral $a(2^m)$ or $a(2^m)\not\equiv1\pmod{2^m}$ would refute the claim.

## Evidence

The Lean source is [the settling module](../D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.lean),
with its [Blueprint mirror](../Blueprint/D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo.md).
The source note is [tebni2023a364822](../Library/RecurrenceComposition/tebni2023a364822.md).
The public result proves the full proposition, including its integer witness.
The module uses only the standard axiom allowance.

Four-slot escape auditing is unfinished for `TebniA364822.num_cast`,
`TebniA364822.num_recurrence`, `TebniA364822.result` and
`TebniA364822PowerOfTwo.result`; the concrete template gap and missing
realization/source-selection evidence are recorded in
[issue #22441](https://github.com/the-omega-institute/trureturing/issues/22441).
No registration is asserted to be declared_validated.

### Experiment

The independent computation is
[the pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/43e699d21346a1c6156fbac2901ce602af85ccd9/docs/reports/oeis-a364822-cosh-sinh-egf-congruences).
Its script `check.py` has SHA-256
`52f51c8b6cb41d6525e4b991d6c081a96f6bd9ff9783c9ab6888857e2919ce24`.
The command `python3 check.py 256 100001`, using the script from that revision,
exited $0$ with all reported checks true.
Its tested scopes are odd primes at most $256$, powers $2^m\le256$ with
$0\le m\le8$, every even $2\le n\le256$ for the exact valuation,
and odd $5\le r\le100001$ for the parity count. The Taylor expansion is
checked for $0\le n<16$, the second expansion for $0\le n<40$,
and the published coefficient list for $0\le n<12$.
The script's coefficient function, evaluated at $n=2$, gives $a(2)=9$
and $a(2)\bmod2=1$. This evaluation exits $0$ using the same script hash.

## Triage

- **Proved, kernel-checked:** every $a(n)$ is an integer, by
  `TebniA364822.num_cast`; this includes $n=1$ and the modulus-one
  case of `TebniA364822PowerOfTwo.result` at $m=0$.
- **Proved, kernel-checked:** at an odd prime, the interior binomial terms
  vanish and the constant-index term gives residue $2$;
  `TebniA364822.result` uses `Nat.Prime.dvd_choose_self` for this step.
- **Proved, kernel-checked:** if $k$ is odd then
  $2^m\mid\binom{2^m}{k}$, by the private helper
  `TebniA364822PowerOfTwo.pow_two_dvd_choose_odd`.
  `TebniA364822PowerOfTwo.result` applies it to the recurrence for positive
  $m$ and handles $m=0$ modulo one.
- **Computed:** the experiment above validates both congruences through
  $n\le256$, $v_2(a(n)-1)=v_2(n)+2$ for every even $2\le n\le256$,
  and its parity count for odd $5\le r\le100001$. The cited command,
  exit code, immutable revision and SHA-256 specify the evidence.
- **Computed:** $a(2)=9$ has residue $1$ modulo $2$, by the same script's
  coefficient function. Thus the prime $2$ cannot be included in the
  residue-$2$ assertion.
- **Open:** the sharper exact valuation for every even $n\ge2$ is
  unformalized here. The finite experiment does not prove its uniform extension.

### What the settlement shows

The decisive mechanism is the exact integer binomial recurrence. It proves
both published congruences without the sharper valuation assertion.
Integrality extends to all natural indices, not just primes or powers of two.
The strict prime bound is necessary, as the computed $p=2$ value shows.
For powers of two the zero exponent is included and gives modulus one.
The residue-$1$ conclusion modulo $2^m$ is kernel-checked; the stronger
modulus $2^{m+2}$ and the exact valuation at arbitrary even indices remain
open as formalization targets. The source lists these two conjectures;
their Lean proofs share the recurrence, and the dyadic proof does not use
the odd-prime settling result as a premise.

## ASSUMED-UNVERIFIED

Completeness of the literature screen is ASSUMED-UNVERIFIED. The uniform
exact valuation is not a kernel-checked result of these modules. Escape
registration remains unfinished under issue #22441.
