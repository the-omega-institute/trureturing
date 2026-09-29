---
slug: mahmoud-2026-stabilizer-pair-local-unitary-inequivalence
bibkey: mahmoud2026macwilliams
doi: 10.48550/arXiv.2607.26214
url: https://arxiv.org/abs/2607.26214v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result
---

# Local-unitary inequivalence of the Question 5.4 stabilizer pairs

## Problem

A. A. Mahmoud (arXiv:2607.26214v1, 2026) constructs weight-isometric pairs of
stabilizer codes that are not monomially equivalent. Theorem 5.3 gives the
full-support pairs

- (ii) `S_A = ⟨ZZZZI, XXIIX, IIXXX⟩` and `S_B = ⟨ZZIZX, XIZXI, IXXYI⟩`, two
  `[[5,2]]` codes;
- (iii) `S+ = ⟨XXIIXX, IIXXXX, ZZZZIX⟩` and `S− = ⟨XXZXII, ZZXYII, IZZZXX⟩`,
  two `[[6,3]]` codes.

The paper then asks:

> Question 5.4 (Extension analogue of LU–LC). Are the codespaces of SA and SB
> of Theorem 5.3(ii)—or those of S+ and S− of Theorem 5.3(iii)—mapped to one
> another by some product unitary U1⊗···⊗Un composed with a qubit
> permutation?

and §6.2 lists it as open problem 1, with the `[[5,2]]` pair as "the minimal
open instance". Issue #11210 fixes the reading: qubits are numbered from the
left; the Pauli matrices are the frozen `qubitX`, `qubitZ` with `Y = i X Z`; a
word and a product unitary act by the tensor product; the codespace is the
joint `+1` eigenspace of the three generators; the permutation acts by
`(P_σ ψ)(x) = ψ(x ∘ σ)`; and "mapped to one another" means that the image of
the first codespace under `U·P_σ` is the second. The formal `claim` is the
positive answer for either pair, and the formal `result` refutes it. The
"More generally" part of the question is not addressed.

## Motivation

For the basic family of the paper, the codespaces are separated by the number
of qubits on which the code projector acts as the identity (Lemma 3.2 and
Theorem 3.3 (iii)). This number vanishes for both pairs of Theorem 5.3, and the
paper says it knows of no invariant that separates them. The frozen declaration
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.result`
settles the first part of the question: neither pair is equivalent, so
Theorem 5.3 (ii) and (iii) hold at the codespace level.

## Gap

Issue #11210 preregisters the question, the route and the literature check.
arXiv lists only version 1, and OpenAlex reports no citing work (2026-09-29).
Searches for the paper's identifier and for the MacWilliams extension problem
together with local-unitary equivalence of stabilizer codes found only the
paper and the earlier work it cites; code search in
`google-deepmind/formal-conjectures`, `epoch-research/LeanOpenProblems` and
`Horace-Maxwell/ai4math-results` found nothing. The separating quantity, the
rank of the reduced state on a set of qubits, is an elementary local-unitary
invariant; no source evaluates it on these pairs.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

For a set `T` of qubits and a subspace `C`, let `V_T(C)` be the span of
`M ψ` with `ψ ∈ C` and `M` a product operator that is the identity on `T`; it
is the whole space exactly when the reduced state of `C` on `T` has full rank.

1. If `W` is a product of invertible matrices composed with a permutation `σ`,
   then `W` maps `V_T(C)` into `V_{σT}(WC)`; applying this to `W` and `W⁻¹`
   shows that `T` is full for `C` exactly when `σT` is full for `WC`.
2. A word that fixes `C`, is supported in `T` and has an `X` or a `Y` fixes
   `V_T(C)`, which then misses the basis vector `0…0`. So `{0,2,3}` and
   `{1,2,3}` are not full for `S_B`, and `{0,1,2,3}`, `{0,1,4,5}`, `{2,3,4,5}`
   are not full for `S+`.
3. A word commuting with the generators maps `C` into `C`, so `V_T(C)` is
   invariant under its part on `T`. When these parts include `X_j` and `Z_j`
   for all `j ∈ T`, `V_T(C)` is invariant under all product operators and, if
   nonzero, is the whole space. Tables of normalizer words make every triple
   other than `{0,1,4}`, `{2,3,4}` full for `S_A` and every 4-set other than
   `{0,1,2,3}` full for `S−`.
4. For (ii), the σ-preimages of `{0,2,3}` and `{1,2,3}` would be `{0,1,4}` and
   `{2,3,4}`, but the former share two qubits and the latter one. For (iii),
   the images of the three sets of step 2 would be three distinct 4-sets that
   are not full for `S−`, which has only one.

## Falsifier

The answer would change if "mapped to one another" allowed maps other than a
product of single-qubit unitaries composed with a qubit permutation, or if the
codespaces were not the joint `+1` eigenspaces of the displayed generators.

## Evidence

Numerical reduced-state ranks (issue #11210): among triples, `S_A` has rank 4
exactly on `{0,1,4}`, `{2,3,4}` and `S_B` exactly on `{0,2,3}`, `{1,2,3}`;
among 4-sets, `S+` has rank 8 exactly on `{0,1,2,3}`, `{0,1,4,5}`,
`{2,3,4,5}` and `S−` rank 4 exactly on `{0,1,2,3}`. A random product unitary
composed with a permutation reproduces the pattern of each code up to
relabelling, as the invariance requires.

The canonical source is
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.lean`. Its
public declarations are `Pauli`, `pauliMatrix`, `tensorOp`, `wordOp`,
`qubitPermutation`, `codespace`, `SA`, `SB`, `Splus`, `Sminus`, `claim`, and
`result`; the invariant span, the sign tables, the word lists and the check
functions are private non-proposition definitions. The frozen module state has
statement identity
`sha256:3d5bbaf9c10ebfd0e926df3da017b2060f9eee45370a9d50ccd2a2ee92b57ecc`.
The result declaration has statement identity
`sha256:f99e62fb5f547191da43251f22f5e051189451d572f258bccd3f67b58f51e507`.
The Freeze event is
`sha256:7d80fa860d71aa317b50182a5f0c68dfb59cf6fb386e1a33f2580091f3c59ba1`.
Its frozen prerequisite is `D5/S3/Quantum/FiniteDimensional` (the Pauli
matrices `qubitX`, `qubitZ` and their squares). The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named question, preregistered in issue #11210 before any Lean.
`theorem`; resolution `refuted` for the positive answer, that is, Question 5.4
(first part) is answered no for both pairs. The public theorem has
`proof_shape: content`: the transport of the spans under product operators and
permutations, the deficiency criterion and the fullness criterion are proved
in the module, and the finite tables are checked by the kernel. Its escape
witness is form (2), the public conclusion itself, and its admission basis is
`open-problem-resolution`. Its computational use is a `certified-instance`
with `basis=refutes`: the result negates the closed claim.

## ASSUMED-UNVERIFIED

The argument needs only that each single-qubit matrix is invertible; the
formal statement is for unitary matrices, as in the question, and the
invertible case is not stated as a separate declaration. The bounded literature check does not
establish exhaustive worldwide novelty, priority, or the absence of an
independent answer. The Lean kernel does not authenticate the external source
or its version history.
