# Exact k-bonacci observation experiments

`audit.py` uses Python 3.8+ and only the standard library. All arithmetic uses
integers; coefficient vectors are constant first and modular residues lie in
`[0,n)`. The definitions are

$$
\Phi_k(X)=X^k-\sum_{j=0}^{k-1}X^j,\qquad
O(n,k,a)=((X+a)^n-X^n-a)\bmod(n,\Phi_k),\quad k\ge2.
$$

These files contain experimental evidence, not Lean-verified declarations.
The polynomial and matrix implementations were written by one delegated
implementation worker using `formal-thinking-and-answer`. The parent added
the boundary checks after a separate mathematical review. Agreement of the
two arithmetic implementations does not represent independent authorship.

## Reproduction

From the repository root:

```sh
python3 -B docs/reports/kbonacci-observation-depth/audit.py --check
python3 -B docs/reports/kbonacci-observation-depth/audit.py --n 4181 --k 2 --a 2
python3 -B docs/reports/kbonacci-observation-depth/audit.py --n 727993807201 --k 4
python3 -B docs/reports/kbonacci-observation-depth/audit.py --scan-max 20000 --output docs/reports/kbonacci-observation-depth/results.json
```

`--n/--k/--a` computes a single observation and checks it using companion
matrices. Shifts may be negative or zero; `--a` defaults to 1. Report mode runs
the certificates, bounded identity checks, reduced-defect checks, and scan.
Without `--output`, report mode prints JSON. `--check [PATH]` reads saved JSON,
recomputes its scan window and all other checks, and exits nonzero on any
disagreement. Its default path is relative to the script, independent of the
current working directory. `--scan-max` can explicitly override the endpoint;
a different endpoint cannot match an unchanged saved report.

Validation used Python 3.9.6 on macOS arm64. Relocated execution from a path
containing spaces, with a different working directory and an empty environment,
passed both single-case and saved-result checks. Other platforms were not run.
Malformed CLI inputs returned the expected exit 2, and changing a saved
coefficient caused `--check` to return the expected exit 1.

Saved data contain counts, exact values, and a SHA-256 digest of the scan's
ordered remainder stream, with no timestamps or timing measurements. The stream
encodes each queried `[n,k,remainder]` as compact JSON plus one newline in ASCII.
Within each `n`, scanning stops at the first nonzero remainder. The saved JSON
has one top-level field per line to keep related numerical records together.

## Verified numerical certificates

The polynomial implementation and companion-matrix implementation agree on
every row:

| n | k | a | Remainder |
|---|---|---|---|
| 4181 | 2 | 1 | `[0,0]` |
| 4181 | 2 | 2 | `[2453,3317]` |
| 4181 | 3 | 1 | `[2910,2999,1387]` |
| 727993807201 | 2 | 1 | `[0,0]` |
| 727993807201 | 3 | 1 | `[0,0,0]` |
| 727993807201 | 4 | 1 | `[119234756168,337074161891,408394870732,141106388989]` |

Trial division verifies that 37, 113, 4951, 9901 and 14851 are prime. Exact
multiplication verifies `4181=37*113` and `N=727993807201=4951*9901*14851`.
The latter factors are distinct, and `gcd(N,5040)=1`. For each row below the
program checks every root, distinctness, and the entire coefficient vector of
the product of the linear factors, not just its evaluations:

| q | Roots of Phi_2 modulo q | Roots of Phi_3 modulo q | (N-1)/(q-1) |
|---|---|---|---|
| 4951 | 2089, 2863 | 132, 820, 4000 | 147069456 |
| 9901 | 223, 9679 | 5236, 6716, 7851 | 73534728 |
| 14851 | 273, 14579 | 6774, 9046, 13883 | 49023152 |

The trial-division upper limits for these three `q` are 70, 99 and 121.
`results.json` records the product coefficient vectors, which equal the
corresponding monic `Phi_k` reduced modulo `q`.

The preceding calculations are **finite certificate checks**. The consequence
for **every integer shift** uses the following field and CRT argument, rather
than extrapolation from sampled shifts. Since `q` is prime and `q-1` divides
`N-1`, Fermat's theorem gives `t^N=t` for every nonzero `t` in `F_q`; it also
holds for `t=0`. Thus, for any integer `a` and any certified root `r`,
`(r+a)^N-r^N-a=0` in `F_q`. For `k=2,3`, the complete factorization has `k`
distinct roots. The remainder of degree less than `k` therefore vanishes at
`k` distinct field elements and is zero. Monic division commutes with reduction
modulo `q`, so each coefficient of the remainder modulo `N` is zero modulo
each of its three prime factors. Integer CRT makes every coefficient zero
modulo their product `N`. Consequently these certificates support
`O(N,2,a)=O(N,3,a)=0` for every integer `a`. This argument uses the standard
field root bound and CRT; the program does not formalize those theorems.
The analogous every-shift claim for `4181,k=2` is refuted by the `a=2` row.

## Arithmetic verification

General monic long division works over the integers or modulo any integer at
least 2; it never inverts a coefficient. Binary exponentiation reads exponent
bits from left to right and stores `U=X^e`, `V=(X+a)^e`. On bit `b`, the update
is `e'=2e+b`, `U'=U^2 X^b`, `V'=V^2 (X+a)^b`, reduced modulo the same monic
polynomial and integer modulus.

The independent arithmetic path constructs the companion matrix `C` directly
from the divisor coefficients. Right-to-left binary matrix powering applies
`C^e` and `(C+aI)^e` to the first basis vector. This path does not call polynomial
multiplication or long division. Direct binomial expansions provide a third
check on small cases.

The saved checks cover the following fixed finite sets:

| Check | Scope | Count |
|---|---|---|
| Prefix `U,V` against matrices | 11 monic divisors; moduli 2,4,6,9,11,35; shifts -3,0,1,2; exponents 0,1,2,3,5,10,21 | 4752 prefix states |
| Observation against direct binomial expansion and matrices | n=2..35; the same 11 divisors; a=-2..3 | 2244 cases |
| Full mirror remainder vectors | odd n=3..35; the same 11 divisors; a=1 | 187 cases |
| Adjacent CRT reconstruction | k=2..8; the six moduli above; three source polynomials per pair | 126 cases |
| Integer monic division reconstruction | the CRT source polynomials and Phi_k | 126 cases |

The divisor list consists of `X`, `X^2-2X+3`, `X^2`, `X^3-3X^2+4`, and
`Phi_2,...,Phi_8`. Prefix checks include both possible bits and exponent zero.
Mirror checks build every coefficient of
`P^sigma(X)=(-1)^deg(P) P(-1-X)` and compare
`Delta_n mod P^sigma` with `(Delta_n mod P)(-1-X) mod P^sigma` for odd `n`,
where `Delta_n=(X+1)^n-X^n-1`. The transformed remainder is checked by direct
binomial expansion too, and the substitution is checked to be involutive.

For adjacent CRT the exact coefficient identity is
`X Phi_k-Phi_(k+1)=1`. Given residues `A` modulo `Phi_k` and `B` modulo
`Phi_(k+1)`, reconstruction uses
`B X Phi_k-A Phi_(k+1)` modulo the product. The program compares the full
reconstructed vector with direct division of the source by the product, then
checks both residue projections. Source polynomials are zero, `3-7X+2X^2`,
and a signed dense polynomial of degree `3k+4`; the latter exceeds the product
degree. Exact examples are retained for every tested integer modulus,
including the even and composite moduli.

## Bounded scan

For composites, define the searched depth as the first `k>=2` for which
`O(n,k,1)` is nonzero. A composite surviving all `k=2,...,8` is explicitly
unresolved above 8; no larger depth is assigned. A separate Eratosthenes sieve
classifies primes and is checked against trial division for every integer
`2,...,20000`.

The inclusive scan `n=4,...,20000` covers 19997 integers: 17737 composites and
2260 primes. All primes have zero observations through `k=8`. Every queried
remainder, including the prime rows, was compared with the companion-matrix
verifier: 33567 comparisons.

| Composite depth | Count |
|---|---|
| 2 | 17727 |
| 3 | 10 |
| 4,5,6,7,8 | 0 each |
| Unresolved above 8 | 0 |

The complete list at depth 3, with the first nonzero vector, is:

| n | O(n,3,1) |
|---|---|
| 705 | `[456,477,351]` |
| 2465 | `[612,2078,551]` |
| 2737 | `[2534,2037,1442]` |
| 3745 | `[245,2030,1365]` |
| 4181 | `[2910,2999,1387]` |
| 5777 | `[3301,5643,719]` |
| 6721 | `[4433,5148,2145]` |
| 10877 | `[4619,2692,10754]` |
| 13201 | `[4361,9081,5392]` |
| 15251 | `[9392,2967,2755]` |

These counts concern only this finite window. No global bound on composite
depth, and no exclusion of composites with depth above 8 outside the window,
is inferred. The separately certified `N` already has depth 4 for shift 1.

The scan also checks the proposed bound `d(n) <= max(2,floor(n/3)-1)` wherever
the queried depths can decide it, and verifies that all 9999 even composites
in the window have depth 2. General proofs, distinct from these bounded
checks, are in [observer theory §§306.5–306.6](../../develop/theory/FORMAL_PRIME_OBSERVER_DYNAMICS.md).

## Structural boundary examples

For `k=2,...,10`, the program verifies every coefficient of
`X^2 Phi_k-Phi_(k+2)=X+1`. Over an odd modulus, `Phi_k(-1)` is a unit;
together with adjacent comaximality, this supports the three-consecutive-order
argument in §306.6. Nonadjacent orders need not remain comaximal:
`Phi_2(3)=5` and `Phi_6(3)=365`, so both vanish in the quotient field `F_5`
of `Z/15Z`.

All 561 residue classes of shifts are checked for `n=561`, `P=X^2` using
both arithmetic paths. Every observation is zero, while `X^561=0` and `X`
has vector `[0,1]`. Since the shift response depends only on the shift
modulo 561, this exhaustive finite check covers every integer shift for this
example. It shows that all-shift agreement does not imply `z^n=z` for every
element of the quotient. It is a counterexample for a general monic
polynomial, not a k-bonacci polynomial.

## Bounded reduced-defect checks

The parent-supplied reduced-defect claims were tested in `(Z/nZ)[X]`, with
`a=1` and `p` the least prime factor of `n`. Among all 238 composites in
`4,...,301`, the reduced coefficient polynomial `Delta_n` has degree `n-p`,
its coefficients below degree `p` are zero, and monic division by `X^p`
has zero remainder. For all 89 odd composites in that window, monic division
by `X^p(X+1)^p` has zero remainder and quotient degree `n-3p`. Re-multiplication
recovers the entire defect vector modulo `n` in every case. The JSON retains
13 degree examples, including the constant reduced polynomial at `n=9`.

For each of these 89 odd composites and each `k=2,...,8`, evaluation verifies
`Phi_k(0)=-1`, `Phi_k(-1)` in `{1,-2}`, and that both values are units modulo
`n`: 623 pairs of unit checks. These are bounded checks, not a proof of the
general reduced-defect statements and not a derivation of a depth bound.
