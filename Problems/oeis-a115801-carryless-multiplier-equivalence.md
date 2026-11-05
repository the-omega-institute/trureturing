---
slug: oeis-a115801-carryless-multiplier-equivalence
bibkey: oeis2026a115801
doi: null
url: https://oeis.org/A115801
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence
---

# Equivalent ordinary and binary carryless multiplier conditions

## Problem

[OEIS A115801](https://oeis.org/A115801) defines the nonnegative integers
$k$ satisfying $9k = \operatorname{A048720}(25,k)$ and conjectures that the
same integers satisfy $15k = \operatorname{A048720}(19,k)$.
The exact assertion is

$$
\forall k\in\mathbb{N},\qquad
9k=C(25,k)\ \Longleftrightarrow\ 15k=C(19,k).
$$

Here $\mathbb{N}$ includes zero, and the multiplications $9k$ and $15k$ are
ordinary natural-number multiplication. The binary digits are indexed from
the least significant bit. The operation $C$ is genuine coefficient
convolution over $\mathrm{GF}(2)$:

$$
\operatorname{bit}(C(u,k),t)
=
\left(\sum_{i=0}^{t}
\operatorname{bit}(u,i)\operatorname{bit}(k,t-i)\right)\bmod 2.
$$

This is the binary polynomial multiplication table
[OEIS A048720](https://oeis.org/A048720), rather than ordinary multiplication.

## Motivation

The source proposes equality of two sets specified by different ordinary
and carryless multiplier pairs. A proof must compare the full sets of
nonnegative integers, beyond the finite check reported in A115801.

## Gap

The source locators retained in
[the Library note](../Library/Digit/oeis2026a115801.md) identify A115801
revision 20, whose NAME gives the first condition and whose COMMENTS gives
the conjectured second condition and a finite check. The operation is
identified by A048720 revision 62, including its binary exclusive-OR
recursion. These are the bounded original-source readings for the claim;
the source's finite check is not a universal proof.

The target and its source qualification are recorded in
[issue 23220](https://github.com/the-omega-institute/trureturing/issues/23220).
The literature scope stated here is limited to those source locators and
the retained Library attribution. It does not establish exhaustive
literature coverage or worldwide priority. Binary polynomial multiplication
and its exclusive-OR recursion are known operations; the asserted resolution
is the exact equivalence above.

## Route

Let $P(u,k)$ be the recursive binary product, with
$P(u,0)=0$, $P(u,2n)=2P(u,n)$, and
$P(u,2n+1)=(2P(u,n))\mathbin{\mathrm{xor}}u$.
Binary induction on $k$ proves that each bit of $P$ is the coefficient
convolution displayed above. Equality of binary digits then identifies
$P(u,k)$ with $C(u,k)$.

A state is either rejection or a pair $(c,d)$ expressing
$m k+c=P(u,k)\mathbin{\mathrm{xor}}d$.
For a low input digit $b\in\{0,1\}$, set
$v=mb+c$ and $e=(bu)\mathbin{\mathrm{xor}}d$.
When $v$ and $e$ have different parity the next state rejects; otherwise
the next state is $(\lfloor v/2\rfloor,\lfloor e/2\rfloor)$.
Splitting an equality into its low bit and remaining bits proves this
transition rule.

The explicit relation `related` contains 29 pairs of states, one from the
$(u,m)=(25,9)$ system and one from the $(19,15)$ system. Its terminal
conditions agree at every pair. Both input digits preserve the relation,
giving 58 checked transitions. Binary induction propagates terminal
agreement through every finite binary expansion. The initial pair
$((0,0),(0,0))$ therefore gives both implications for every natural number.

## Falsifier

A natural number $k$ for which exactly one of the two multiplier equations
holds would refute the source assertion. A failure of the convolution
identification, a terminal-condition mismatch, or a digit transition leaving
the relation would invalidate this proof mechanism. The finite transition
checks support the induction; no finite bound on $k$ replaces its universal
conclusion.

## Evidence

- Mathematical source:
  `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.lean`.
- Public operation: `carryless`, defined by binary coefficient convolution.
- Exact theorem: `result (k : Nat) : 9*k = carryless 25 k ↔ 15*k = carryless 19 k`.
- The recursive product's coefficient specification, state transition rule,
  29-pair relation, terminal agreement, and transition closure are retained
  in the mathematical source and consumed by the theorem.
- The theorem's axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.
- The source operation has literature attribution; the new proof has
  repository-derived attribution linked to the same Library source.
- The retained Reg mirror compiles but its machine audit is
  `declared_unresolved`: `IE-C050 ClosedTruthReadout`,
  `reason=unclassified_form`, rule `source.residual_requires_open`.
  The linked exception is
  [issue 23220, audit gap](https://github.com/the-omega-institute/trureturing/issues/23220#issuecomment-6475140509).
  It supplies neither a validated registration nor a substitute for kernel
  and frozen-state checks.

## Triage

`theorem`. The exact all-natural-number equivalence follows from a
coefficient-convolution identification and a finite state relation with
29 pairs and 58 digit transitions. Binary induction extends that finite
certificate to inputs of every binary length; at $k=0$, both equations
are $0=0$.

The state-transition argument suggests a method for comparing other
ordinary/carryless multiplier pairs, but each such comparison needs its own
relation, transition closure, and terminal agreement. No general theorem
about all multiplier pairs is asserted here. A proposed binary-run
characterization and the older neighboring `17 -> 9` question remain open
in this dossier; neither is a consequence claimed by this resolution.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and worldwide publication priority are
unverified. The bounded source record does not exclude every independently
published solution. The Reg readout classification remains unresolved under
the linked issue. No unproved run characterization or neighboring
multiplier equivalence is included in the resolution claim.
