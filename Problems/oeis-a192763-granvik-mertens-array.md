---
slug: oeis-a192763-granvik-mertens-array
bibkey: granvik2011a192763
doi: null
url: https://oeis.org/A192763
triage: theorem
motivation_gids:
  - D5/S3/Arith/GranvikMertensArray.result
---

# Granvik's Möbius diagonal and Mertens row

## Problem

Preregistration: [#20559](https://github.com/the-omega-institute/trureturing/issues/20559).
Mats Granvik's OEIS A192763 COMMENTS field states:

> The main diagonal is the Mobius function times the natural numbers A055615 (conjecture). For k>1 the first row is the Mertens function + 2 = A002321 + 2 (conjecture).

The positive-index array is defined by Michael Somos's Mathematica and PARI programs in the entry.
It is symmetric, $T(1,1)=1$, $T(2,1)=2$, and
\[
T(n,1)=\frac{-T(n-1,1)-\sum_{i=2}^{n-1}T(n,i)}{n+1}+T(n-1,1)
\quad(n\ge3).
\]
For $n>k\ge2$ it satisfies
$T(n,k)=T(k,((n-1)\bmod k)+1)$; for $n\ge2$ its diagonal is
$T(n,n)=-\sum_{i=1}^{n-1}T(n,i)$.
The formal definition takes values in $\mathbb Q$ and extends zero-index cells
by zero. It uses well-founded recursion with measure
$4\max(n,k)$ plus phases three for the upper triangle, two for the diagonal,
one for the lower border, and zero for the strict lower interior.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Somos's positive rational recurrence | `GranvikMertensArray.T` | The displayed branch order and inclusive sums; no integer rounding. |
| Corner and first border cell | `T 1 1 = 1`, `T 2 1 = 2` by definition | OEIS program normalization. |
| Main diagonal for every positive index | First conjunct of `result` | `∀ n : ℕ, 1 ≤ n → T n n = (n : ℚ) * (ArithmeticFunction.moebius n : ℚ)`. |
| First row for every index greater than one | Second conjunct of `result` | `∀ k : ℕ, 2 ≤ k → T 1 k = 2 + ∑ j ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius j : ℚ)`. |
| Mats Granvik and Olivier Gérard's first Mathematica program | Private `granvik`, `T_eq_granvik` and `T_published_unique` | Its literal border and reverse-window equations define exactly `T`. This equality is consumed by `result`. |
| Math.SE 50719 | Source note | Its printed corner is three; this settlement uses the OEIS program's corner one. Its index slips are resolved by the executable Mathematica and PARI programs in OEIS. |

## Motivation

The single result settles both all-index conjectures in the entry. The first
row is an exact recurrence characterization of the Möbius summatory function.
No estimate for its growth is part of the assertion.

## Gap

The two claims remain labelled conjectural in the official export at commit
`0b811e71e00a3e9b1374c94971f83d8e4c8af516`. The Math.SE API reading on
2026-10-23 gives zero answers and `is_answered: false`. The bounded
literature and duplicate screen in #20559 found no settlement. Completeness
of that screen and publication priority are `ASSUMED-UNVERIFIED`.

The mathematical gap is to evaluate the sums of the Euclidean-descended
cells and derive the border identity for every index. Finite agreement with
the entry is not used as evidence for these universal claims.

## Route

Write $B(n)=2+\sum_{d=1}^n\mu(d)$. Define a symmetric arithmetic model
with border $B$, corner one, and the following interior values. A cell with
$g=\gcd(n,k)>1$ has value $g\mu(g)$. When $n>k>1$ and $g=1$, its value
is $B(q)$, where $q$ is the last quotient in the ordinary Euclidean descent.

Signed Bézout descent proves
\[
q=\left\lfloor\frac{n-1}{\min(u,n-u)}\right\rfloor,
\qquad u=(k^{-1}\bmod n)\in\{1,\ldots,n-1\}.
\]
This follows by transporting the determinant $ka-nb=\pm1$ through each
Euclidean step while preserving the positive quotient. The smaller signed
inverse has $0<\min(u,n-u)\le n/2$.

For $n>1$, the Möbius convolution identity gives
\[
\sum_{\substack{1\le j<n\\(j,n)=1}}
 M\!\left(\left\lfloor\frac{n-1}{j}\right\rfloor\right)=-\mu(n).
\]
Inversion permutes the reduced residues. Reflection $u\mapsto n-u$,
together with the quotient-one border value, evaluates the corresponding
sum with denominator $\min(u,n-u)$ as $\varphi(n)-2\mu(n)$.
The $k=1$ border correction changes this to $\varphi(n)-\mu(n)$.

Grouping the remaining cells by gcd uses the existing
`RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity` and
\[
\sum_{d\mid n}\varphi(n/d)d\mu(d)=\mu(n).
\]
The complete off-diagonal model row sum is therefore $-n\mu(n)$.
The difference $B(n)-B(n-1)=\mu(n)$ then supplies the border update.

For fidelity, a symmetric array with Somos's positive reduction and zero
row-sum diagonal has periodic positive columns of index at least two; each full period sums to
zero. This gives precisely the reverse-window sums in Granvik/Gérard's
first Mathematica program. That literal program is itself well-founded.
Both `T` and the model satisfy it, so its uniqueness identifies them.
The single public result reads off the model's diagonal and border.

## Falsifier

A positive diagonal index $n$ with $T(n,n)\ne n\mu(n)$, or a first-row
index $k\ge2$ with $T(1,k)\ne2+\sum_{j=1}^k\mu(j)$, contradicts the
respective conjunct. A disagreement between Somos's and the literal first
Mathematica program contradicts the consumed equivalence proof. Rational
values and exact inclusive index ranges exclude rounding or off-by-one
interpretations.

## Evidence

- Lean owner: `D5/S3/Arith/GranvikMertensArray.lean`.
- Public mathematical interface: `T` and the single theorem `result`.
- Source note: `Library/RecurrenceComposition/granvik2011a192763.md`.
- Blueprint source: `Blueprint/D5/S3/Arith/GranvikMertensArray.scribe.cs`.
- Verification: the scoped Lean report successfully checks the owner module
  and its import closure.
- The proof reuses
  `RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity` to group cells by gcd.

### Proof components

| Statements | Mathematical role |
| --- | --- |
| `lastQuotient_of_signed_bezout`, `lastQuotient_eq_inverse` | Signed Bézout descent expresses the terminal Euclidean quotient through the smaller inverse residue. |
| `coprime_mertens_cancel`, `reduced_border_sum`, `sum_inverse` | Möbius convolution, inversion and reflection evaluate sums over reduced residues. |
| `model_coprime_sum`, `model_row_sum` | The coprime and gcd-grouped contributions give the off-diagonal sum $-n\mu(n)$. |
| `border_step`, `model_granvikRule` | The border difference and row sum establish the published recurrence for the model. |
| `T_granvikRule`, `granvik_unique`, `T_eq_granvik`, `T_published_unique` | Periodicity and well-founded uniqueness identify Somos's array, the first Mathematica recurrence and the model. |
| `result` | The model's diagonal and border give both conjectured identities at every stated index. |

## Triage

**Proved:** the decisive invariant is the terminal Euclidean quotient of a
coprime cell, encoded by the smaller inverse residue. Noncoprime cells are
controlled by their gcd. This explains why the two-dimensional rational
recurrence has a one-dimensional arithmetic border rather than merely
matching a list of initial values.

**Proved:** reduced-residue inversion and reflection turn the interior sum
into Möbius convolution. Together with gcd multiplicity, they force the
row sum and the border difference. The published reverse-window recurrence
and Somos's accelerated recurrence describe the same positive array;
neither interpretation is left as a numerical hypothesis.

**Proved:** the two source conjectures require no remaining conditional
arithmetic assumption. The corner at one is handled explicitly. The
Math.SE corner-three variant is not the array defined here, and equality
with that variant is not claimed.

**Open:** replacing the border weights by a general arithmetic function
would require a compatible convolution identity and diagonal law. This
proof does not state a generalization for arbitrary weights or prove that
the Möbius function is the only possible family under altered seeds.
Such questions are outside the two named claims.

**Open:** the recurrence supplies an exact characterization, with no
cancellation estimate beyond its finite identities. The Riemann-hypothesis
bound for the growth of the Mertens function remains unresolved. No
improved asymptotic or complexity estimate is a consequence claimed by
this settlement, and no other source theorem is claimed as newly settled.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not kernel
conclusions. The bounded source readings do not rule out unindexed
settlements. The Math.SE corner-three normalization and any proposed
arithmetic-weight generalization are outside the formal statement.
