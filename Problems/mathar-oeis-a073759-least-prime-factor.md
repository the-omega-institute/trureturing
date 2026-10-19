---
slug: mathar-oeis-a073759-least-prime-factor
bibkey: mathar2026a073759
doi: null
url: https://oeis.org/A073759
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/MatharA073759.result
---

## Problem

R. J. Mathar's conjecture in [OEIS A073759](https://oeis.org/A073759), FORMULA (unpaginated), states: "Conjecture: a(n) = 2*A046667(n) if n>=5. - _R. J. Mathar_, May 15 2026". The NAME is "Largest number < n that is neither a divisor of nor relatively prime to n, or 0 if no such number exists." The companion entries define A046666 by "a(n) = n - (smallest prime dividing n)." and A046667 by "a(n) = A046666(n)/2." The offsets are respectively 1, 2 and 2. Preregistration: [#18937](https://github.com/the-omega-institute/trureturing/issues/18937).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive number below $n$ | `a`: the finite interval from 1 inclusive to $n$ exclusive | Literal preregistered convention |
| Neither divisor nor relatively prime | `a`: the conjunction of nondivisibility and failure of `Nat.Coprime` | Both exclusions retained |
| Largest, or zero if empty | `a`: `Finset.sup id` of the filtered interval | Natural supremum defaults to zero |
| Smallest prime dividing $n$ | `A046666`: natural subtraction of `Nat.minFac n` | Exact for the source domain $n\ge2$ |
| Divide A046666 by two | `A046667`: `Nat.div` by 2 | Integer division; parity supplies exactness |
| Every $n\ge5$ | `claim`, proved by `result` | No extra hypothesis or conjunct |

All names belong to `D5.S3.Arith.Primes.MatharA073759`. The definitions extend to natural indices outside the OEIS offsets; the settlement quantifies only over $n\ge5$.

## Motivation

The maximum excludes both divisors and coprime numbers. A least-prime-factor formula determines it on an unbounded domain, including prime indices where the admissible set is empty.

## Gap

The source and literature screen recorded in #18937 reads A073759, A046666 and A046667 and finds the conjecture line with no cited resolution. Its searches cover the sequence identifiers with Mathar and least-prime-factor terms, the OEIS conjectures metadata of `epoch-research/LeanOpenProblems-results`, snapshot `197f7f8dcc` of `google-deepmind/formal-conjectures`, and the repository's problems and issues. No resolution was found in that searched scope. Literature completeness is ASSUMED-UNVERIFIED.

## Route

Put $p=\operatorname{minFac}(n)$. At a prime index every positive $k<n$ is coprime to $n$, so $a(n)=0=n-p$.

For composite $n\ge5$, $p$ is prime, $p\mid n$ and $p^2\le n$. If $p=2$, $2p<n$ follows from $n\ge5$. If $p\ge3$, $2p<3p\le p^2\le n$. Thus $p<n-p$, and $\gcd(n-p,n)=p>1$. Since $n-p>p$, $n-p$ cannot divide $n$: otherwise its gcd with $n$ would equal $n-p$. Hence $n-p$ is an admissible candidate.

If $k<n$ is not coprime to $n$, a common prime divisor $r$ divides the positive difference $n-k$. Minimality of $p$ gives $p\le r\le n-k$, so $k\le n-p$. This proves maximality and $a(n)=n-p$.

Finally $n-p$ is even. For even $n$, $p=2$; for odd $n$, both $n$ and its prime divisor $p$ are odd. Therefore $n-p=2\lfloor(n-p)/2\rfloor=2A046667(n)$.

## Falsifier

A natural index $n\ge5$ at which the literal filtered supremum differs from $2A046667(n)$ would refute the claim. The index 4 does not satisfy the quantified lower bound.

## Evidence

`D5.S3.Arith.Primes.MatharA073759.result` proves `claim` for every natural $n\ge5$. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The Scribe result displays the expanded quantified proposition and carries one Proved resolution of this dossier. No atom or coverage step is involved.

The finite check is [the published experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/04bafcea983207a1fa6056376aa68d57319d2fa1/docs/reports/oeis-a073759-mathar-largest-unrelated). Command: `python3 check.py` from that directory; exit 0. Script SHA-256: `f36bac2eba413b9af6d1f92f1a3f6ad6ff06bdd62fd4fd3613797bf5fc7633f0`. It reports agreement with the first 50 listed terms, zero mismatches for $5\le n\le20000$, and $a(4)=0$ while $4-\operatorname{minFac}(4)=2$. This corroboration is finite and supplies no universal inference.

Escape audit unfinished: [#19044](https://github.com/the-omega-institute/trureturing/issues/19044), covering the sole public theorem `D5.S3.Arith.Primes.MatharA073759.result`. No Reg registration or declared_validated status is claimed. An infinite dependent-family reconstruction, equivalence bridge, positive law, variation and sensitivity evidence have not been supplied.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and scope |
| --- | --- | --- |
| Settlement | proved; kernel-checked `D5.S3.Arith.Primes.MatharA073759.result` | The literal conjecture holds for every natural $n\ge5$, with only the three standard axioms in its closure. |
| Mechanism | proved in prose; Route | The witness is $n-p$, with gcd $p$, and for composite $n\ge5$ it is not a divisor. Every $k$ strictly between $n-p$ and $n$ is coprime to $n$. The four private helpers support the kernel proof; the stronger identity is explained in Route, not asserted as an additional public theorem. |
| Neighbouring consequence | proved in prose | For even $n\ge5$, the identity in Route and $p=2$ give $a(n)=n-2$, exactly Mathar's even-index comment. This is not a separate Lean theorem. |
| Sharp boundary | computed; published experiment in Evidence | $a(4)=0$ but $4-p(4)=2$; the lower bound cannot be extended to all $n\ge4$ for that identity. No proof step in #18937 is overturned. |
| Escape witness | proved in prose; judgement-form classification | No escape witness is claimed. All five authored theorem proofs are bind-only compositions of pinned Mathlib facts and consumed helpers. Admission is `open-problem-resolution (#18937; Proved)`. |

The proof gives the conjectured formula directly rather than conditionally assuming it. The source screen identifies no other result that depends on this conjecture; effects beyond the three cited entries have not been verified. The even-index comment follows on the stated range, while the computed index 4 fixes the boundary of the stronger least-prime-factor identity.

## ASSUMED-UNVERIFIED

Completeness of the literature search and first-publication priority are ASSUMED-UNVERIFIED. The source readings are attributed to the orchestrator in #18937. The unfinished four-slot escape audit is tracked in #19044; mathematical verification does not establish registration completion. No claim is made about a proof outside the screened sources or about neighbouring OEIS assertions outside the stated range.
