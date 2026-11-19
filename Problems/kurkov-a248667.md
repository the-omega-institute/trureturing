---
slug: kurkov-a248667
bibkey: kimberling2014a248667
doi: null
url: https://oeis.org/A248667
triage: theorem
motivation_gids:
  - D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.result
---

## Problem

Mikhail Kurkov's conjecture in COMMENTS paragraph 3 of [OEIS A248667](https://oeis.org/A248667), revision 53, is preregistered in [#23541](https://github.com/the-omega-institute/trureturing/issues/23541):

> Conjecture: any composite term can be represented as a product a(i)*a(j) (i > 1, j > 1) in at least one way.

The source is an electronic OEIS entry, with no DOI or source arXiv identifier. Its [Library note](../Library/Certificates/kimberling2014a248667.md) gives the complete source quotations and locator.

For positive $n$, let

$$P_n(X)=\sum_{j=0}^{n-1}\prod_{i=j+1}^{n-1}(nX+i).$$

This is the unreduced numerator over the source's full denominator. Empty products are one. Let $A$ consist of the positive $n$ such that $P_n$ is primitive over $\mathbb Z$. The assertion includes existence of a strictly increasing enumeration $a$ of exactly $A$, with the dummy value $a(0)=0$. Every composite $a(k)$ at a positive index is a product $a(i)a(j)$ with $i,j>1$; equal indices are allowed.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Numerator over the specified full denominator | `sourcePolynomial` | Sum of the remaining tails, with both integer casts and every interval endpoint preserved. |
| Relatively prime coefficients | `Polynomial.IsPrimitive` in `IsSourceSequence` | Existing Mathlib predicate over integer polynomials. |
| Increasing one-based sequence of all such positive integers | `IsSourceSequence` | Strict increase and exact positive range; zero is an auxiliary value outside the source domain. |
| Any composite term | `claim`, quantified over every source enumeration and positive index | Greater than one and not `Nat.Prime`; no finite cutoff. |
| A product at indices greater than one | Existential conclusion of `claim` | Both inequalities are retained, with no distinctness assumption. |
| The source sequence exists | First conjunct of `claim` | Proved rather than assumed; this strengthens the explicit assertion and prevents vacuity. |

## Motivation

The settling declaration is `D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.result`, with `generality: I`, `utility: none` and `admission_basis: open-problem-resolution (#23541; Proved)`. The chain is deposit-uncovered, with no atom or cover. The public definitions retain the preregistered literal expressions.

## Gap

A prime factor of a sequence member need not belong to an arbitrary sequence. Here the required bridge is that membership in the actual primitive-numerator family depends only on the prime divisors of the same positive integer. Nonvacuity additionally requires infinitely many members and their exact increasing enumeration.

## Route

Define the explanatory recurrence $Q_a(0)=1$ and $Q_a(m+1)=(aX+m+1)Q_a(m)+1$. The private consumed lemmas identify $P_n=Q_n(n-1)$, show its top coefficient is $n^{n-1}$, and commute the recurrence with coefficient maps. A prime dividing every coefficient must divide that top coefficient and hence $n$. Modulo a prime divisor $p$ of $n$, the recurrence resets at each multiple of $p$, giving $Q_0(n-1)=Q_0(p-1)$ in $(\mathbb Z/p\mathbb Z)[X]$. Thus

$$P_n\text{ primitive}\quad\Longleftrightarrow\quad
\forall p\text{ prime},\ p\mid n\ \Longrightarrow\ Q_0(p-1)\ne0.$$

Positive divisors therefore remain in $A$. The prime $3$ passes the residue test, so every power of $3$ belongs. The existing `Nat.nth` enumeration of this infinite set, with zero adjoined, gives a strictly increasing exact enumeration. Since $P_1=1$, every such enumeration has $a(1)=1$. A composite member splits as $pq$ with $p$ prime and $p,q>1$; divisor closure puts both factors in $A$, and their indices exceed one.

## Falsifier

A positive composite member with no such pair of indices would refute the stated conjecture. A discrepancy in the finite checker would require checking its exact polynomial and membership calculations; it would not by itself establish a counterexample to the kernel-checked statement. The dummy index zero is never a source term.

## Evidence

The [Lean module](../D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.lean) proves `result : claim`. The corresponding Scribe displays all three public definitions and the expanded complete theorem. There are no D5 imports. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The escape audit of the sole public theorem `D5.S3.Arith.PolynomialValues.KurkovA248667CompositeFactorization.result` is unfinished under [#30662](https://github.com/the-omega-institute/trureturing/issues/30662). The full conjunction needs an existential enumeration realization together with the universal factorization law. No faithful compiled four-slot registration and whole-family bridge/sensitivity evidence is supplied; no `declared_validated` claim is made.

### Exact finite experiment

The program and data are in the [immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/1ee9383937689b0a4434e5fb1159ef0d933f2f5e/docs/reports/kurkov-a248667). The script `check.py` has SHA-256 `882bedc7e63061ff596581cc8a1a26bbcccbc320201b138f68b5d7d8137168f0`, verified against that commit. Running the exact extracted script with `python3 /Users/auric/.op-scratch/kurkov-stageb/check.py` exits 0 and reports `ALL_CHECKS_OK`. It independently checks polynomial content for $1\le n\le100$, and uses Taylor's criterion for $101\le n\le3000$. Within $1\le n\le3000$ it finds 1075 members, checks 2130 divisor pairs and all 649 composite members' internal factorizations, and checks 6846 prime-divisor reset pairs. These are finite computations, separate from the universal proof.

## Triage

### What the settlement shows

All theorem names below belong to `D5.S3.Arith.PolynomialValues.KurkovA248667CompositeFactorization`; the supporting theorems are private and consumed.

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Membership in the actual source-polynomial family is characterized solely by the primes dividing the same positive $n$. | proved | Kernel-checked `source_prime_support`, for every $n>0$. |
| Every positive divisor of a source member is a source member. | proved | Kernel-checked `source_divisor_closed`. |
| All powers of $3$ belong; the exact increasing source enumeration exists and every such enumeration has $a(1)=1$. | proved | Kernel-checked `source_three_pow`, `source_sequence_exists`, `source_sequence_one`. |
| Every composite term splits into two source terms at indices greater than one; equal indices are permitted. | proved | Kernel-checked `result`, including sequence existence and every admissible enumeration. |
| All 649 composite members through 3000 have internal factorizations; independent polynomial-content checks extend through 100. | computed | The exact finite experiment above, command exit 0 and the stated script SHA-256; values above 100 use Taylor's criterion. |
| Finitude or infinitude of the excluded-prime set, and density or counting asymptotics of source members. | open | No such conclusion is proved or inferred from the finite computation. |

The decisive mechanism is prime support and positive-divisor closure, rather than a bounded search for factor pairs. The recurrence identities are proved over arbitrary commutative rings; the source-family support theorem concerns every positive integer. The conjecture's equality permits repeated factors and the proof preserves that scope. The source's composite-term assertion is available as a theorem; no other OEIS assertion is claimed as a new settlement. Taylor's printed leading coefficient $n^n$ is not used: `Q_coeff` and `source_Q` yield $n^{n-1}$.

### Literature status

The bounded screen in #23541 found no settlement of the exact Kurkov conjecture. It checked OEIS A248667 and related entries, arXiv identifier/full-text/author searches, Crossref, Semantic Scholar citations, named Zenodo corpora and MathDB. Sondow and Schalm, arXiv:0709.0671v3, Proposition A.5, is background on the scalar factorial recurrence and modular periodicity; it is neither the target's source nor a claim of new content. The AMS book-chapter version and an access-restricted Springer full text were not read. Repository scalar recurrence and prime-factorization owners do not supply the polynomial-family support bridge. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The literature screen establishes only the searched scope, not exhaustive completeness or global priority. The excluded-prime and asymptotic questions remain open. The finite experiment has exactly the tested ranges stated above. The unfinished escape audit in #30662 is distinct from the mathematical proof.
