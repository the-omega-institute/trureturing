---
slug: oeis-a344695-gcd-sigma-psi-odd-primes
bibkey: karttunenmunn2021a344695
doi: null
url: https://oeis.org/A344695
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes
---

# The Karttunen–Munn prime-values conjecture for OEIS A344695

## Problem

OEIS A344695, revision 39, defines “a(n) = gcd(sigma(n), psi(n)), where sigma is the sum of divisors function, A000203, and psi is the Dedekind psi function, A001615.” Its comment states: “Conjecture: the set of primes that appear in the sequence is A065091 (the odd primes).” The assertion is preregistered in [#18688](https://github.com/the-omega-institute/trureturing/issues/18688).

For each natural prime $q$, the formal claim says that some natural $n\ge1$ has $a(n)=q$ if and only if $q$ is odd.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A001615: “Dedekind psi function: n * Product_{p\|n, p prime} (1 + 1/p).” | `psi`, using natural exact division by the product of distinct prime factors | The binding integer expression of #18688; positive indices make the division exact |
| A344695 defines the gcd of sigma and psi | `a` | `ArithmeticFunction.sigma 1` and `Nat.gcd` retain the source operations |
| “the set of primes that appear” | `claim` quantifies over every natural prime and an existential positive index | The guard excludes composite candidate values, and positivity matches the sequence's domain |
| “is A065091 (the odd primes)” | The existential occurrence is equivalent to `Odd q` | Both directions, with no upper bound |

The public definitions are the binding expressions of #18688. The value at zero is outside the source sequence. The settling declaration `result` proves the complete `claim`.

## Motivation

The classification explains why 2 is absent and why every odd prime occurs, including primes absent from a finite prefix. It concerns existence of an index, not the least index or a practical bound on its size.

## Gap

The source presents the prime-values assertion as a conjecture. The literature screen recorded in #18688 read A344695 and A001615 and searched the Epoch OEIS Open benchmark, AlphaProof Nexus results, formal-conjectures, Fried's OEIS-proof papers, and repository records without finding a proof. Completeness and freshness of that screen are `ASSUMED-UNVERIFIED`.

## Route

For a square index, the frozen divisor-sum parity theorem supplies oddness of $\sigma(n)$, so the gcd cannot be 2. For a nonsquare index, some prime $p$ has odd exponent. The factor $p+1\ge3$ divides both $\sigma(n)$ and $\psi(n)$, again excluding 2.

For an odd prime $q$, choose a prime $r>q^2+q+1$ with $r\equiv1\pmod{q(q+1)(q^2+q+1)}$, using `Nat.exists_prime_gt_modEq_one`. At $n=q^2r^{q-1}$, write $S=q^2+q+1$ and $T=\sum_{i=0}^{q-1}r^i$. Then $\sigma(n)=ST$ and $\psi(n)=q(q+1)r^{q-2}(r+1)$. The congruences give $q\mid T$ and coprimality of $(q+1)r^{q-2}(r+1)$ with $ST$. Applying `Nat.gcd_mul_of_coprime_of_dvd` gives $a(n)=q$. No lifting-the-exponent theorem is needed.

## Falsifier

A positive index with $a(n)=2$, an odd prime outside the range, or a failure of the exact-division and prime-power identities would falsify the settlement. The finite experiment tests the arithmetic encoding over its stated range; it does not replace the universal proof.

## Evidence

The kernel-checked public theorem is `D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes.result`. Its seven private consumed helpers are listed in the classification table below. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The frozen parity dependency used in the proof is `D5.S3.Arith.KrizekTriangularSquareSigmaParity.sigma_odd_iff_square_or_twice_square` from `D5/S3/Arith/KrizekTriangularSquareSigmaParity`.

The experiment is [`docs/reports/oeis-a344695-gcd-sigma-psi`](https://github.com/the-omega-institute/trureturing-experiments/tree/579c9e22945b4ac6f0fbe32e55ce7fd7c28d4407/docs/reports/oeis-a344695-gcd-sigma-psi) at commit `579c9e22945b4ac6f0fbe32e55ce7fd7c28d4407`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/oeis-a344695-gcd-sigma-psi/check.py 2000000 200`, exit 0. The SHA-256 of `check.py` is `bbb350936c12eca673642129e7b622b8234644aeb743a8787e136a56c19d521c`. The published data agree; exclusion of 2 and the square/nonsquare dichotomy hold for $1\le n\le2{,}000{,}000$; the construction succeeds for all 45 odd primes $q\le200$.

The escape audit of `result` is unfinished in [#19807](https://github.com/the-omega-institute/trureturing/issues/19807). No compiled Reg mirror or `declared_validated` registration is claimed.

## Triage

| Target item | Status | Evidence kind and scope |
| --- | --- | --- |
| Prime values are exactly the odd primes | proved | Kernel-checked `result`, for every natural prime |
| The arithmetic-progression construction works for every odd prime, with coprimality controlling the gcd without LTE | proved | Kernel-checked private `witness_value`, consumed by `result`, and the prime-existence application in `result` |
| The value 2 is excluded for every positive index | proved | Kernel-checked private `not_two`, consumed by `result` |
| Published data, exclusion/dichotomy through 2,000,000, and all 45 odd-prime constructions through 200 | computed | The pinned experiment, command, exit code and hash in Evidence |
| Least positive index producing each odd prime | open | No minimum or optimality statement is supplied by `result` |
| Composite range, including whether 10 occurs | open | `claim` classifies prime values only |
| The source implication $a(n)=1\Rightarrow n$ is square | open as a separately exported theorem | The nonsquare obstruction explains the implication, but no separate theorem with that conclusion is exported |
| Effect on other source formulas and the full sequence range | open | Those assertions are outside `claim`; only the prime-values conjecture is settled |
| Literature completeness | ASSUMED-UNVERIFIED | Bounded literature reading in #18688 |

### What the settlement shows

**Proved in this module.** `result` classifies all prime values. The private `not_two` excludes 2 for every positive index. The private `witness_value` gives a construction for every odd prime once the stated congruent prime $r$ is supplied; `result` obtains such an $r$ from the upstream existence theorem.

**Decisive mechanism and extent.** The square/nonsquare split excludes 2. Geometric-sum congruences and a coprimality calculation make the construction uniform over all odd primes, without LTE. The construction need not give a least index and supplies no composite-range classification.

**Computed.** The experiment verifies the finite scope stated in Evidence, including first occurrences $3$ at $n=2$, $5$ at $366025$, $7$ at $6724$, $11$ at $9801$, and $13$ at $257049$; $17$ does not occur through $2{,}000{,}000$.

**Effect on the source.** The prime-values conjecture is proved in the binding formal conventions. Other source formulas and the full sequence range receive no settlement.

| Declaration | proof_shape | escape_witness | Live consumers |
| --- | --- | --- | --- |
| `psi`, `a`, `claim` | bind-only source definitions | none | `result` and its helpers |
| `psi_prod` | bind-only | none | `not_two` |
| `geom_mod_one` | bind-only | none | `witness_value` |
| `geom_mod_self` | bind-only | none | `witness_value` |
| `geom_mod_succ` | bind-only | none | `odd_exp_dvd_sigma`, `witness_value` |
| `odd_exp_dvd_sigma` | bind-only | none | `not_two` |
| `not_two` | bind-only | none | `result` |
| `witness_value` | bind-only | none | `result` |
| `result` | bind-only after expanding the same-delivery helpers | none | External named open-problem settlement |

Module admission basis: `open-problem-resolution (#18688; Proved)`. Utility: `none`; the statements concern arbitrary indices and primes rather than a finite numerical certificate.

## ASSUMED-UNVERIFIED

Literature completeness, worldwide priority and the freshness of the external screen remain `ASSUMED-UNVERIFIED`. The least-index problem, composite range and separately exported square-necessity assertion remain open in this delivery. The escape audit is unfinished under #19807.
