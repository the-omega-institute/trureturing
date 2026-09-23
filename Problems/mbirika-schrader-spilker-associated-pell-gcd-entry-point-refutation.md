---
slug: mbirika-schrader-spilker-associated-pell-gcd-entry-point-refutation
bibkey: mbirika2023pellbraid
doi: 10.48550/arXiv.2301.05758
url: https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.result
---

# Mbirika-Schrader-Spilker Associated Pell GCD Entry-Point Refutation

## Problem

Mbirika, Schrader, and Spilker define the Pell and associated Pell sequences
in Definition 3 on printed page 4:

> **Definition 3.** The Pell sequence (P_n)_{n≥0} and the associated Pell sequence (Q_n)_{n≥0} are defined by the recurrence relations P_n = 2P_{n−1} + P_{n−2} and Q_n = 2Q_{n−1} + Q_{n−2}, respectively, with initial conditions P_0 = 0, P_1 = 1, Q_0 = 1, and Q_1 = 1.

Section 6.2 on printed page 22 gives the entry-point convention:

> When (S_n)_{n≥0} is the Pell or associated Pell sequence, we have partial results towards closed forms for gcd(S_k, k) that involve the entry point (or rank of apparition), e_S(p), which is the smallest index r > 0 such that p divides S_r where p is a prime.

The same printed page states:

> **Conjecture 32.** We claim that gcd(Q_k, k) > 1 if and only if there exists a prime p such that p divides k and the rank of apparition (or entry point), e_Q(p) divides k. For example, gcd(Q_21, 21) = 7 and for the prime p = 7, we have p divides 21 and e_Q(p) = 3 divides 21.

The formal `claim` follows the printed universal biconditional and makes the
entry point explicit as the least positive index at which the prime divides
the associated Pell sequence.

## Motivation

Issue 9058 preregistered this first-tier external named conjecture and its
literal source statement before the Lean probe. The frozen theorem
`D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.result`
settles the statement as printed. It does not propose a corrected criterion.

## Gap

The bounded literature check covered arXiv:2301.05758 and its versions, the
published Journal of Integer Sequences article, the cited records, and the
2025 Fiebig-Mbirika-Spilker Lucas-sequence paper. MathDB entry `/p/357242`
repeats the same statement and reports `Solutions 0`. Repository searches
found no prior declaration resolving this associated Pell gcd criterion.
No proof or refutation was found in that searched scope.

The searched surfaces do not establish exhaustive publication absence, and
no publication-priority claim is made.

## Route

Use `k = 12`. The frozen recurrence gives `Q_12 = 19601`, hence
`gcd(Q_12, 12) = 1`, so the left side of the biconditional is false. On the
right side, `p = 3` is prime and divides 12. Its entry point is 2 because
`Q_1 = 1`, `Q_2 = 3`, and no term `Q_s` with `0 < s < 2` is divisible by 3.
Finally, 2 divides 12, so the right side is true.

The source's own `k = 21` example is retained as a fidelity anchor:
`Q_21 = 54608393`, `gcd(Q_21, 21) = 7`, and `p = 7` has entry point 3,
which divides 21. Thus the formal sequence and entry-point convention agree
with the paper on its displayed example before the `k = 12` falsifier is used.

## Falsifier

An incorrect associated Pell recurrence, any failure among
`Q_12 = 19601`, `gcd(Q_12, 12) = 1`, `Q_1 = 1`, or `Q_2 = 3`, or a term
`Q_s` with `0 < s < 2` divisible by 3 would invalidate the counterexample. A proof of
the printed universal claim would contradict the kernel-checked theorem
`result : Not claim`.

## Evidence

The canonical module defines `claim : Prop` and the sole public theorem
`result : Not claim`. Its frozen module statement identity is
`sha256:3bb5cc24f868f61c2bbd3d043e753e05f5430cadfc09f02ead549b25e1a80338`;
the result statement identity is
`sha256:ae715155cab6ec1f27f34a88f1b88a38710e840df1b323908451388f1870801b`.
The Freeze event is
`sha256:2f8f766bd26dbe9d7c8a63fd77e816b7376cba21d326b33bef64aaf5074c50ce`.
Its prerequisite node
`sha256:e758dbf8a9e3adab4f031a1eac93fba719aaaaaa986a0b152d5ff12a29aca6fc`
is `D5/S1/Recurrence/PellCompanionGcd`, whose frozen definition `Q` is
imported and used.

The Scribe theorem node binds the frozen `result` to this dossier with
`OpenProblemResolutionClaim(Refuted)`. The result is a closed typed
refutation, and the proof uses no `sorry`, `native_decide`, or new axiom.

## Triage

`theorem`; Tier 1 external named conjecture, preregistered in issue 9058.
The public theorem has `proof_shape: bind-only`: it instantiates the printed
claim at `k = 12`, evaluates the frozen recurrence and natural-number gcd,
and closes the finite divisibility and minimality facts with `decide` and
`omega`. Its `escape_witness` is `none`, and its `admission_basis` is
`open-problem-resolution`. The computational use is a `certified-instance`
with a typed `refutes` edge from `result` to `claim`. There is no atom and no
digestion coverage edge.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded search cannot
exclude every prior resolution or establish publication priority.
Source-to-Lean fidelity and proof-shape classification remain semantic review
judgments; the Lean kernel checks the formal statement and proof, not their
equivalence to the cited prose. The resolution binding records the current
frozen theorem and does not itself establish repository merge or external
publication.
