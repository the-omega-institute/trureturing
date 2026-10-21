---
slug: oeis-a347285-de-vlieger-prime-power-descent
bibkey: devlieger2021a347285
doi: null
url: https://oeis.org/A347285
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.result
---

## Problem

M. De Vlieger's conjecture in [OEIS A347285](https://oeis.org/A347285), COMMENTS (unpaginated), states: "Conjecture: let S be the sum of the absolute values of the first differences of terms in row n. For all n > 0, n - S = 1." The NAME defines the rows as "Irregular triangle T(n,k) starting with n followed by e_k = floor(log_p_k(p_(k-1)^e_(k-1))) such that e_k > 0." The FORMULA is "T(n,1) = n; T(n,k) = floor(log_p_k(p_(k-1)^T(n,k-1)))." The source text is [pinned at e7d0073e](https://raw.githubusercontent.com/oeis/oeisdata/e7d0073e/seq/A347/A347285.seq). Preregistration: [#18689](https://github.com/the-omega-institute/trureturing/issues/18689). Source note: [devlieger2021a347285](../Library/PrimeForms/devlieger2021a347285.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The primes are indexed from one | Existing `D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime`, with value `Nat.nth Nat.Prime (k - 1)` | The literal preregistered enumeration is reused. |
| Initial row entry is $n$ | `e n 0` | Equals $n$. |
| Real logarithm and downward natural floor at the next prime | `e n (j + 1)` | The current exponent is raised on the current prime, and the logarithm base is the next prime. |
| Keep entries greater than zero | `len n`, the first zero index, with zero fallback if none exists | `e_zero_exists` and `len_spec` establish existence and positivity before that index. |
| Sum absolute first differences within the row | `S n` | Natural absolute value of each integer difference, over indices below `len n - 1`. |
| Every $n>0$, with $n-S=1$ | `claim`, proved by `result` | Natural indices, strict positivity, and integer subtraction; no additional hypothesis. |

The source convention "T(0,1) = 0 by convention; 0 is not allowed for n > 0" leaves the separately listed row zero outside the conjecture. The recurrence extends through zero for proof purposes; only the positive prefix enters $S$.

## Motivation

A universal endpoint identity determines the total variation of every row without enumerating its prime powers. The proof separates the existence of a last positive term from its value.

## Gap

The source and literature checks attributed to the Claude Code orchestrator in #18689 read A347285 in the OEIS mirror and on oeis.org. The searched scope includes the Epoch OEIS Open benchmark list and results, `google-deepmind/alphaproof-nexus-results`, `google-deepmind/formal-conjectures`, S. Fried's OEIS-proof papers, the repository's screened-out collections and its development branch. No proof was found within that searched scope. Literature completeness is ASSUMED-UNVERIFIED.

## Route

For consecutive primes $p<q$ and positive exponent $a$, one has $p^a<q^a$, hence $\lfloor\log_q(p^a)\rfloor<a$. Thus positive exponents strictly decrease. A row that never reached zero would give an infinite strictly descending sequence of natural numbers, excluded by well-foundedness.

Let $a$ be the last positive exponent, at prime $p$, and $q$ the next prime. The next exponent is zero, so $p^a<q$. Bertrand's postulate gives $q\le2p\le p^2$. If $a\ge2$, then $p^2\le p^a<q\le p^2$, a contradiction. Therefore $a=1$.

Every absolute first difference equals the preceding entry minus the next. The finite sum telescopes from $n$ to the final entry $1$, so $S=n-1$ and $n-S=1$.

## Falsifier

A positive natural row index for which the literal floor-logarithm recurrence has $n-S\ne1$ would refute the claim. Row zero is outside its quantified domain. Numerical agreement on a finite prefix alone does not establish the universal assertion.

## Evidence

`D5.S3.Arith.Primes.OeisA347285PrimePowerDescent.result` proves `claim` for every positive natural index. Its private proof dependencies include `e_drop`, `len_spec`, `last_eq_one` and `sum_abs_telescope` in the same module. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The Scribe result displays the full quantified claim and carries one Proved resolution of this dossier. The form is deposit-uncovered, with no atom or coverage step.

The experiment is [the published directory at commit 912fe796ac92af38ecfc9d1d7a1e63bfed319639](https://github.com/the-omega-institute/trureturing-experiments/tree/912fe796ac92af38ecfc9d1d7a1e63bfed319639/docs/reports/oeis-a347285-prime-power-descent). Command from that directory: `python3 check.py 400`; exit 0. Script SHA-256: `2bb2265008aac735197e0481f837d1db60fc136175ca2f95e3e24279606d4bc8`. The published data agree, all rows $1\le n\le400$ strictly decrease, end in one and satisfy $n-S=1$, and the longest tested row has 75 entries. This is finite corroboration; it supplies no asymptotic or universal inference.

Escape audit unfinished: [#19840](https://github.com/the-omega-institute/trureturing/issues/19840), covering `D5.S3.Arith.Primes.OeisA347285PrimePowerDescent.result` and the public primality owner `D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime_is_prime`. Declaration identities: `result` is `sha256:459c08f902542886ea820815815a4146c9c7ad725be57ac6250de95ce7c81e2b`; `prime_is_prime` is `sha256:c69cad3dd0e0f731e6d72c5a23e478ab050bc04ff36315a285e62f03cdee35a9`. No Reg registration is supplied for either target and no declared_validated status is claimed. The dependent-family registration attempt lacks elaborated source-selection reconstruction, realization-bridge and E1–E8 evidence, and a DTR-Declared reading.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and scope |
| --- | --- | --- |
| A347285 conjecture $n-S=1$ for $n>0$ | proved; kernel-checked `D5.S3.Arith.Primes.OeisA347285PrimePowerDescent.result` | The literal claim holds for every positive natural row index. |
| Strict decrease of positive row entries and final entry one | proved; kernel-checked private `e_drop`, `len_spec`, `last_eq_one` in the settling module | Strict decrease applies to a positive current entry; the last retained entry is exactly one. |
| Least first difference is one | open | The source's separate comment is not addressed by the settling theorem. |
| Growth of row length in $n$ | open | Neither an asymptotic law nor a quantitative growth estimate is delivered. |
| Explicit numerical bound on `len` in the final module | open | No numerical length bound is delivered; `e_zero_exists` uses the existing general prohibition of infinite natural descent. |
| Finite row check | computed; experiment in Evidence | Only rows $1\le n\le400$ and the published data are checked; the maximum observed length is 75. |
| Decisive mechanism and its extent | proved in prose; Route | Increasing bases give strict descent. The weaker next-base condition $q\le p^2$ already forces endpoint one; the prime-specific input supplies that condition. The argument applies to positive natural rows with natural bases at least two, strictly increasing and satisfying the next-base square bound, with the same floor-logarithm recurrence. This extension is not an additional Lean theorem. |

All eleven theorem proofs are classified bind-only compositions of frozen owners, pinned Mathlib and consumed helpers; no escape witness is claimed. Admission is `open-problem-resolution (#18689; Proved)`, rather than escape-witness admission. The source entry states no additional theorem conditional on this conjecture. Effects on other results have not been verified; the separate least-difference and row-length questions receive no resolution from this delivery.

## ASSUMED-UNVERIFIED

Literature-search completeness and publication priority are ASSUMED-UNVERIFIED. Source and literature readings are attributed to the orchestrator in #18689. The unfinished escape audit is tracked in #19840; the mathematical proof and frozen membership do not establish registration completion. No assertion is made about a prior resolution outside the searched sources.
