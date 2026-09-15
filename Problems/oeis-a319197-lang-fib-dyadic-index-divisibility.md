---
slug: oeis-a319197-lang-fib-dyadic-index-divisibility
bibkey: lang2018a319197
doi: null
url: https://oeis.org/A319197
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LangFibDyadicIndexDivisibility
---

# Dyadic divisibility at Lang's Fibonacci indices

## Problem

OEIS A319197, NAME (`%N`, verbatim):

> All entries from a(3) to a(n) appear in addition to 2^n as factors in the conjectured factorization of Fibonacci(2^(n-2)*3*m) for n >= 3 and all m >= 0.

The first COMMENT sentence (`%C`, verbatim), which is the settled clause:

> It appears that Fibonacci(2^(n-2)*3*m)/(2^n) is a nonnegative integer for n >= 3 and all m >= 0.

AUTHOR (`%A`, verbatim):

> _Wolfdieter Lang_, Oct 09 2018

The exact Lean statement is
`theorem result (n m : ℕ) (hn : 3 ≤ n) : 2 ^ n ∣ Nat.fib (2 ^ (n - 2) * 3 * m)`.
The natural-number domain includes `m=0`; `n-2` is truncated subtraction,
which agrees with ordinary subtraction under `3 <= n`. The positive divisor
`2^n` makes natural divisibility equivalent to the quoted
nonnegative-integral quotient assertion, not a claim about truncated division.

Only that first COMMENT sentence is settled. The product
`A(n) = Product_{j=3..n} a(j)`, the `I(n; m)` factorization conjecture, the
specific factors from A049660 and A253368, and the rest of the entry are not
claimed. The theorem does not assert an exact 2-adic valuation.

## Motivation

The stated power of two is a uniform divisor for every natural multiplier
and every dyadic level starting at `n=3`. A direct induction establishes this
unbounded divisibility assertion independently of the remaining proposed
factors in A319197.

## Gap

Readings of 2026-09-15. OEIS
still opens the comment with "It appears" and carries no proof line and no
Lengyel reference. OpenAlex returned zero results for `A319197`,
MathOverflow returned zero, and formal-conjectures returned zero. GitHub
code search returned only unrelated non-mathematical hits. The arXiv API
returned HTTP 503 at query time: arXiv was not searched.

The repository prior-art search at
`origin/dev = d1c9a61ae9` found zero `A319197` hits. Hits for
`2-adic valuation` concerned only `IsraelLaguerreFourParity`, whose object is
Laguerre numbers. No 2-adic Fibonacci divisibility theorem was found in D5
or pinned Mathlib: `padicValNat` and `fib` never co-occurred in that search.
The A074724 lane #7976 concerns the 3-adic analogue in an independent module.

No direct theorem for the full dyadic divisibility statement was found in
the frozen-project and pinned-Mathlib search scope; a direct `exact?`
binding attempt failed on the unbounded power-divisibility
obligation. This is `not-found-in-searched-scope`, not an exhaustive absence
claim. Pre-registration issue #7988 was created on 2026-09-15 before the
probe started.

Lengyel (1995), "The order of the Fibonacci and Lucas numbers", Fibonacci
Quarterly 33, gives the general exact 2-adic valuation of Fibonacci numbers.
That prior literature is acknowledged in `lang2018a319197`; no mathematical
priority or claim of a previously unknown consequence of that valuation is
made here.

## Route

1. Apply `Nat.le_induction` to the level `n`, starting at `n=3` with arbitrary
   natural `m`. Compute `Nat.fib 6 = 8` and use `Nat.fib_dvd` to transport
   divisibility from index `6` to `6*m`.
2. At the successor step, write `k = 2^(n-2)*3*m`. The index for `n+1` is
   `2*k`, and `Nat.fib_two_mul` gives
   `Nat.fib (2*k) = Nat.fib k * (2*Nat.fib (k+1) - Nat.fib k)`.
3. The induction hypothesis gives `2^n` dividing `Nat.fib k`, and hence `2`
   dividing it. Both terms of the cofactor are even, so `Nat.dvd_sub` gives
   an even cofactor. Apply `mul_dvd_mul` and normalize `2^(n+1)` to finish.

The sole public theorem has `proof_shape: content` and
`admission_basis: escape-witness`, using the public-conclusion form of the
witness: the induction constructs the unbounded dyadic divisibility
invariant on the live proof path. There are no separately authored public
or private helpers and no direct frozen-project dependencies.
`utility: none` describes an unbounded arithmetic theorem; the internal
base computation is not a separate finite-instance result.

## Falsifier

A natural pair `n >= 3`, `m >= 0` with
`Nat.fib (2^(n-2)*3*m) % (2^n) != 0` would refute the stated divisibility.
The case `m=0` is included: its Fibonacci value is zero and is divisible by
`2^n`.

## Evidence

- Lean module: `D5/S1/Recurrence/LangFibDyadicIndexDivisibility.lean`.
- `lake env lean` on that module: exit 0. The exact theorem statement and
  proof were copied from the verified probe.
- `tools/scripts/agent/header-check.sh` on that module: exit 0; 35 lines,
  31 Lean files in the immediate directory, `generality: G` compliant.
- The scratch `#print axioms` audit: exit 0, with exactly
  `[propext, Classical.choice, Quot.sound]` for
  `D5.S1.Recurrence.LangFibDyadicIndexDivisibility.result`.
- The sole direct import is `Mathlib.Data.Nat.Fib.Basic`. Deleting it alone
  through process substitution and recompiling exits 1, reporting unknown
  Fibonacci notation/constants and an unknown tactic. No separate tactic
  import is needed because the Fibonacci module supplies the required
  tactics transitively.
- `lake env lean -Dprofiler=true -Dtrace.profiler.threshold=1000` on the
  module: exit 0; `/usr/bin/time -p` wall time 1.98 seconds, Lean type
  checking 13.9 milliseconds. This is a warm-cache single-file measurement
  in the assigned macOS worktree.
- Numerical checks: zero exceptions for `3 <= n <= 9`, `m < 60` and for
  `3 <= n <= 12`, `m <= 100` (1010 pairs). These finite scans support fault
  detection only; the Lean induction carries the unbounded statement.
- Whole-tree `make lean-report` exit 0 (`LEAN_REPORT_DELTA mode=delta
  changed=0 added=2 removed=1 recheck=2`) and whole-tree `make lean` exit 0
  (`Build completed successfully (13371 jobs)`) on the landed lane tree
  (parent `198f814cd0`); header check exit 0; Scribe
  `FormulaCorpusInventoryTests` exit 0.

## Triage

`theorem`; resolution `proved` for the first quoted COMMENT sentence, with
the explicit scope wall above.

## ASSUMED-UNVERIFIED

The arXiv search was not performed (HTTP 503 at query time). Historical
openness outside the stated search surfaces (OEIS text, OpenAlex,
MathOverflow, GitHub code search, formal-conjectures, repository prior art)
is unverified, and no exhaustive literature or priority claim is made. The
bounded numerical scans do not establish the universal statement.

### LS.1. The separately stated sharpness clause

**Definition.** Let F_n and L_n be the original Fibonacci and Lucas
sequences, with F_0=0, F_1=1, L_0=2 and L_1=1. Let a(n) denote the
published entries of OEIS A319197 with offset three, and, wherever the
prefix has been supplied, set

$$D_n=2^n\prod_{j=3}^n a(j).$$

The COMMENT and FORMULA of A319197 additionally assert that this
uniform divisor is best possible, with F_(3*2^(n-2))/D_n=1. The following
claim is the consequence of that assertion at n=7:

$$\mathsf{Sharp}_7:\quad
\nexists c\in\mathbb N:\ c>1\ \land\
\forall m\in\mathbb N,\quad cD_7\mid F_{96m},$$

where the five supplied entries fix

$$D_7=2^7\cdot1\cdot9\cdot161\cdot51841\cdot6989569.$$

This clause is distinct from the power-of-two divisibility statement.
No choice of the unspecified tail of a(n) changes this finite-prefix
consequence. Source: Wolfdieter Lang, OEIS A319197 (2018), COMMENT and
FORMULA, https://oeis.org/A319197 .

### LS.2. The exact corrected product at every level

**Definition.** Independently of the published a(n), define integers

$$b_0=9,\qquad b_{j+1}=2b_j^2-1,\qquad
s_k=6\cdot2^k,\qquad C_k=2^{k+3}\prod_{0\le j<k}b_j.$$

The sequence b_j is A081459(j+2), the known Newton-Pell numerator
sequence. Its recurrence and formula b_j=L_(6*2^j)/2 are recorded in
OEIS A081459, https://oeis.org/A081459 . The definition here fixes an
infinite sequence without extrapolating A319197's incorrect prefix.

**Theorem LS1.** For every k>=0,

$$\boxed{L_{s_k}=2b_k,\qquad F_{s_k}=C_k>0.}$$

For every integer d, including zero and negative integers,

$$\boxed{\bigl(\forall m\ge0,\ d\mid F_{s_km}\bigr)
\quad\Longleftrightarrow\quad d\mid C_k.}$$

Thus C_k is the greatest positive common divisor of all those Fibonacci
values. In external indexing, the corrected layer is a*(3)=1 and
 a*(n)=b_(n-4) for n>=4.

**Proof.** At k=0, L_6=18 and F_6=8. Since every s_k is even, the
classical identities L_(2n)=L_n^2-2 and F_(2n)=F_n L_n imply

$$L_{s_{k+1}}=4b_k^2-2=2b_{k+1},\qquad
F_{s_{k+1}}=C_k(2b_k)=C_{k+1}.$$

Simultaneous induction proves both equalities. Positivity follows from
s_k>0. Fibonacci divisibility gives F_(s_k)|F_(s_km), proving the reverse
implication in the common-divisor assertion. Its forward implication
uses the permitted multiplier m=1. This argument also shows that zero
cannot be a common divisor. These are applications of classical Lucas
doubling and Fibonacci divisibility, within the correction of the
specified sharpness assertion.

### LS.3. An all-multiplier counterexample to sharpness

**Theorem LS2.** The claim Sharp_7 is false. More precisely,

$$D_7=67205083036226688,\qquad
F_{96}=51680708854858323072=769D_7,$$

and therefore

$$\boxed{\forall m\ge0,\quad769D_7\mid F_{96m}.}$$

**Proof.** LS1 at k=4 and the defining recurrence give

$$b_0=9,\quad b_1=161,\quad b_2=51841,\quad
b_3=5374978561=769\cdot6989569.$$

Insert these values in C_4=2^7 b_0b_1b_2b_3. The multiplier assertion
then follows from F_96|F_(96m). Since 769>1, it contradicts Sharp_7.
In particular the published quotient at m=1 is 769, rather than one.
This does not refute the published integrality assertion at that level.

**Proposition LS3.** Using exactly the eight supplied entries of A319197,

$$\left(\frac{F_{3\cdot2^{n-2}}}{D_n}\right)_{n=3}^{10}
=(1,1,1,1,769,835903,1,1),\qquad835903=769\cdot1087.$$

**Proof.** The next correct layer is

$$b_4=57780789062419261441
=1087\cdot53156199689438143.$$

The supplied a(9) equals 835903*b_5, so the two displaced factors are
included there. The supplied a(10) equals b_6. Together with LS1 and
LS2 these integer identities give every displayed ratio. No assertion
about the unprovided infinite tail is needed. Failure at n=7 alone
already refutes the universal sharpness clause.

### LS.4. Coprime layers and normalized multiplier dynamics

**Theorem LS4.** All b_j are positive odd integers and, whenever i<j,

$$\gcd(b_i,b_j)=1.$$

Consequently the exact exponent of two in F_(6*2^k) is k+3.

**Proof.** The recurrence preserves oddness and b_j>=9. It gives
b_(i+1)=-1 modulo b_i and b_(i+2)=1 modulo b_i; every later term remains
one modulo b_i. Thus every common divisor of b_i and b_j divides one.
The exact exponent statement follows from the positive odd product
in LS1.

**Theorem LS5.** For fixed k, the integer quotient

$$U_k(m)=F_{s_km}/C_k\quad(m\ge0)$$

satisfies

$$U_k(0)=0,\qquad U_k(1)=1,\qquad
U_k(m+2)=2b_kU_k(m+1)-U_k(m).$$

**Proof.** LS1 and Fibonacci divisibility make the quotient integral.
The two roots phi^(s_k),psi^(s_k) have sum L_(s_k)=2b_k and product
one because s_k is even. The Binet difference therefore satisfies the
displayed second-order recurrence. Division by the fixed nonzero C_k
preserves that recurrence and gives the two initial values. This is
an exact corrected normalization for every multiplier, not merely a
finite list of factors.

### LS.5. Two exact-rank channels inside each later layer

**Theorem LS6.** Let j>=1, t=2^(j+1), and define

$$A_j=L_t,\qquad B_j=(L_t^2-3)/2.$$

These are coprime positive odd integers and

$$\boxed{b_j=A_jB_j.}$$

Every prime p dividing A_j has exact Fibonacci rank 2t, and every
prime p dividing B_j has exact Fibonacci rank 6t. In either case its
exponent in b_j equals its initial depth

$$h_p=v_p(F_{p-(5/p)}).$$

**Proof.** For even t, the Lucas tripling identity is
L_(3t)=L_t(L_t^2-3), while 3t=6*2^j. For t a power of two at least four,
L_t is odd, and repeated doubling from L_4=7 gives L_t=7 modulo eight
and L_t=1 or2 modulo three. Thus B_j is a positive odd integer and
neither factor is divisible by three. A common odd prime divisor would
divide three; hence the two factors are coprime. The Lucas doubling law
modulo five gives L_t=2 or3 modulo five, excluding five as well.

If p|A_j, then p|F_(2t)=F_t L_t and p does not divide F_t, since their
greatest common divisor divides two. The rank therefore divides 2t but
not t. These indices are consecutive powers of two, so the rank is 2t.
If p|B_j, then p|L_(3t), hence p|F_(6t), but p does not divide F_(3t).
As 6t has only the primes two and three in its index, its rank must be
either 2t or6t. Rank 2t would imply p|L_t, contradicting coprimality of
A_j and B_j. Thus it is 6t.

Finally p is different from two, three and five. The multiplier between
its exact rank and 6t is either three or one, so it does not change the
initial valuation. The coprimality of F_(3t) and L_(3t) away from two
identifies that valuation with the exponent in b_j. The standard rank
bound and the Fibonacci valuation theorem identify it with h_p. The
valuation input is Lengyel's classical formula, as recorded in Medina
and Rowland, Fibonacci Quarterly 53 (2015), Theorem 1.4,
https://arxiv.org/abs/0910.2907 .

**Proposition LS7.** The first four later layers split as

$$
\begin{array}{c|r|r|c}
j&A_j&B_j&\text{ranks of the two channels}\\\hline
1&7&23&8,24\\
2&47&1103&16,48\\
3&2207&769\cdot3167&32,96\\
4&1087\cdot4481&11862575248703&64,192.
\end{array}
$$

**Proof.** Evaluate the Lucas doubling recurrence at t=4,8,16,32 and
insert the resulting values into LS6. Trial division verifies the
primes displayed in the products. In particular the missing 769 belongs
to rank96, while the missing 1087 belongs to rank64. Their relocation
in the supplied a(9) does not respect these exact-rank channels.

LS6 identifies where an initial repeated factor would occur; it does
not force one. The exceptional first layer b_0=9 is excluded from LS6:
its factor three has rank four and its repeated exponent comes from
an index multiple, not from a WSS exception. No WSS prime is furnished
by the sharpness counterexample or the corrected normalization.
