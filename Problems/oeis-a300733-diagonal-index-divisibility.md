---
slug: oeis-a300733-diagonal-index-divisibility
bibkey: hanna2018a300733
doi: null
url: https://oeis.org/A300733
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility
---

# A300733: index divisibility

## Problem

Quoted directly from the seat-local file `oeis-A300733.src`
(`seats/opB-diagidx2/oeis-A300733.src` in the supplied workspace):

> NAME: G.f. A(x) satisfies: [x^n] A( x/A(x)^(3*n) ) = 0 for n>=1.
> COMMENT: Conjecture: n divides a(n) for n>=1.
> AUTHOR: _Paul D. Hanna_, Mar 11 2018

The target is the quoted divisibility conjecture for this entry.
The formal object has `a(0)=a(1)=1` and exponent `e(n)=3*n`.
The printed degree-one boundary requires the correction disclosed under ASSUMED-UNVERIFIED.

## Motivation

This is a first-tier OEIS conjecture attributed to Paul D. Hanna in 2018.
The target is the unbounded assertion `n` divides this entry's `a(n)`
for every `n>=1`. This dossier and its claim account for this entry alone.

## Gap

The supplied source labels the target a conjecture. This offline follow-up
checks the entry-specific source and its connection to the delivered theorem;
it performs no new external literature or revision-history search. Whether
an earlier proof exists outside the supplied material remains unverified.

## Route

The module constructs a normalized integer power series by a triangular
coefficient update. Agreement of inverses preserves agreement of coefficients,
and each update improves agreement by one degree. Stabilization produces the
series; `generating_equation` and `generating_unique` establish its normalized
vanishing equation and uniqueness.

The coefficient engine `power_coefficient_identity` comes from differentiating
integer powers of a unit, including negative powers. In the triangular sum,
put `alpha=v_p(n)`. If `v_p(m)<alpha`, then `v_p(n-m)=v_p(m)`, so the engine
supplies the required prime-power factor in the inverse-power coefficient.
If `v_p(m)>=alpha`, strong induction supplies it in `a(e,m)`. Combining prime
multiplicities, summing and negating proves `index_power_divisibility`.
Its hypothesis `n^k | e(n)` for every natural `n` is sufficient; no claim
is made that it is the weakest sufficient hypothesis.

For this entry specialize `e(n)=3*n` and `k=1`.

This instance uses the general theorem within the same module; it needs no
identification with a coefficient object from the frozen sibling module.

## Falsifier

A natural index `n>=1` at which `n` fails to divide this entry's
normalized coefficient would falsify the claimed conclusion.
The formal coefficient is `a (fun m => 3 * m) n`.
Finite agreement with DATA and finite divisibility checks cannot exclude
an arbitrary later counterexample.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.lean`.
- Entry-specific theorem and Scribe claim: `hanna_conjecture_a300733`.
- Exact conclusion for `n : ℕ`, `hn : 1 ≤ n`: `(n : ℤ) ∣ a (fun m => 3 * m) n`.
- General input: `index_power_divisibility`; coefficient engine:
  `power_coefficient_identity`; construction: `generating_equation` and
  `generating_unique`.

The orchestrator reports from `results/verify-r28.py` / `results/verify-r28.out`
that this entry's published DATA is reproduced exactly (12 terms), with
zero violations of its divisibility conjecture for `1 <= n < 16`.
These are attributed finite supporting readings, not a proof or a fresh run
by this seat.

## Triage

`theorem`. The claim for this slug is attached only to `hanna_conjecture_a300733`
and settles this entry's `n` divisibility conjecture for every `n>=1`
under the corrected, normalized defining condition `n>1`. It does not prove
the literal printed degree-one vanishing condition.

## ASSUMED-UNVERIFIED

The printed NAME says `for n>=1`. The delivered module instead imposes
vanishing only for `n > 1`, as disclosed in its module docstring. This is a
correction to the printed text, not a restatement: this entry's own DATA
starts with `1,1`, and the degree-one substituted coefficient is then one,
not zero. Identifying the corrected normalized object with the intended OEIS
sequence is a source interpretation, not a kernel-verified editorial fact.
The literal printed degree-one condition is not claimed.

The quotations and author date were read directly from this entry's own
local `.src` file; the file's fidelity to the live OEIS page and revision
history was not independently checked because this seat has no network.
External OEIS-to-Lean identification and publication priority are not
kernel-checked facts. No exhaustive literature search is claimed.
The numerical readings above are supplied by the orchestrator and were not
independently recomputed by this follow-up seat; they are support, not proof.
