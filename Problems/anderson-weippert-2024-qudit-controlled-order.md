---
slug: anderson-weippert-2024-qudit-controlled-order
bibkey: andersonweippert2024controlled
doi: 10.48550/arXiv.2410.04711
url: https://arxiv.org/abs/2410.04711v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.result
---

# Controlled qudit gates have prime-power target order

## Problem

J. T. Anderson and M. Weippert, *Controlled Gates in the Clifford Hierarchy*, arXiv:2410.04711v3, Section 4, printed page 7:

> It is tempting to conjecture for the qudit case that C(U) is in the Clifford Hierarchy only if U is order d^m where d is the local qudit dimension and m is a non-negative integer. We leave this as an open problem.

For every prime $p$, every $n\geq0$ and every unitary $U$ on $n$ qudits of local dimension $p$, membership of $C(U)$ in a finite Clifford-hierarchy level implies $\operatorname{orderOf}(U)=p^m$ for some $m\geq0$. The control is coordinate zero. Block one is $U$; all other control blocks are the identity. Order includes the global phase.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Prime local dimension | `claim` quantifies over $p$ with `Nat.Prime p` | Exact; primality supplies `NeZero p`. |
| Controlled gate in block one | `controlled` uses the two literal conditional matrix entries and `Fin.tail` | Exact preregistered convention. |
| Tensor-product Pauli words with a unit-circle phase | `WeylCliffordDescent.pauli` uses the existing `productMap` and `WeylDisplacement.displacement` | The complete tensor expression is retained; the source allows arbitrary $U(1)$ phase. |
| Recursive hierarchy, starting at the Pauli group | `WeylCliffordDescent.cliffordHierarchy` | Level zero is empty; level one is the Pauli set; higher levels require unitarity and conjugation of every Pauli into the preceding level. |
| Some finite hierarchy level | The existential natural index in `claim` | No uniform level bound is assumed. |
| Target has order $p^m$ with $m\geq0$ | The conclusion of `claim` and `result` | Exact multiplicative matrix order, including phase. |
| The source describes $p$ blocks of size $p$ | The parameter $n=1$ | The theorem additionally proves the same convention for every natural target count, including zero; no source hypothesis is dropped. |

The public definitions are the literal preregistered expressions, with basis type aliases expanded. The Pauli tensor construction is the existing owner `productMap`; its use does not introduce a forwarding Weyl definition.

## Motivation

Preregistration: https://github.com/the-omega-institute/trureturing/issues/19835. The settling declaration is `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.result`. Its module has generality I, utility none, and admission basis `open-problem-resolution (#19835; Proved)`. The arithmetic and hierarchy modules have generality G, utility none, and escape-witness admission.

## Gap

The bounded source and literature screen in the preregistration found no settlement in its inspected papers. That screen covers the source versions, the named qubit and diagonal-gate follow-ups, and the cited abstracts. Exhaustive coverage and originality are `ASSUMED-UNVERIFIED`; the named UC Davis dissertation was not read.

## Route

Let $S$ be the shift on the control and $D_0=C(U)$. Iterate $D_{r+1}=D_r S D_r^\dagger S^\dagger$. `WeylCliffordDescent.hierarchy_terminates` proves termination at the identity for finite hierarchy membership. The private block lemmas identify each iterate with powers of $U$ whose integer exponents satisfy $a_{0,j}=\mathbf1_{j=1}$ and $a_{r+1,j}=a_{r,j}-a_{r,j-1}$.

The arithmetic proof shows that the positive gcd of these exponents has no prime divisor other than $p$. For a field of characteristic different from $p$, a cyclic difference with zero sum has trivial kernel: its kernel consists of constant vectors, and $p$ is nonzero. This proves that a positive iterated difference remains nonzero. Reduction modulo any prime $q\ne p$ excludes $q$ from the gcd. `CyclicDifferencePrimeContent.order_prime_power_of_coeff` then proves that a group element annihilated by every exponent has $p$-power order. `result` applies it to the unitary subgroup and transfers the exact order to the matrix monoid.

## Falsifier

A failed correspondence with block-one control, omission of the global phase, a nonprime local dimension, or infinite rather than finite hierarchy membership is outside the proved statement. The conjecture's converse is not used. The rendered result displays the whole quantified proposition.

## Evidence

Kernel evidence is supplied by the three Lean modules `D5/S3/Arith/Primes/CyclicDifferencePrimeContent.lean`, `D5/S3/Quantum/Algebra/WeylCliffordDescent.lean`, and `D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.lean`, their Scribe mirrors, and their canonical frozen state records. The live owner reuse includes `StabilizerGenuineEntanglementCommutationRank.pauli_word_mul` and `SubspaceStabilizerEntropy.displacement_unitary_pair`.

The four-slot escape audit is unfinished for the three new public theorems, the two published owner theorems and the published owner definition `StabilizerGenuineEntanglementCommutationRank.wordMul`: https://github.com/the-omega-institute/trureturing/issues/20302. No `declared_validated` registration is asserted.

### Convention experiment

Pinned experiment: [Anderson–Weippert convention checks](https://github.com/the-omega-institute/trureturing-experiments/tree/45ec3cd6e4ce67eca8b99d16c6bf5d692d8a3765/docs/reports/anderson-weippert-2024-qudit-controlled-order), `check.py`. Command: `git -C ../trureturing-experiments show 45ec3cd6e4ce67eca8b99d16c6bf5d692d8a3765:docs/reports/anderson-weippert-2024-qudit-controlled-order/check.py | python3 -` (with `pipefail`); exit 0. Script SHA-256: `667a533e45d84e2260201ea2820e78bf279081567bb731d24804b99b847a7f0f`.

Computed scope: one control and one target; $p=2$ through hierarchy level 4 and $p=3$ through level 3. The qubit least levels are 2 for $X,Z,iX$, 3 for $S,H$, and 4 for $T$; $SH$ and $\operatorname{diag}(1,e^i)$ have no membership through level 4. The qutrit gates $X_3,Z_3$ have least level 3 and order 3; $-I$ and $\operatorname{diag}(1,1,-1)$ have order 2 and no membership through level 3. The tested qutrit order-9 gates $\operatorname{diag}(1,1,e^{2\pi i/9})$ and $e^{2\pi i/9}I$ also have no membership through level 3. These are numerical finite-scope convention checks; a nonmembership reading through the cutoff is not nonmembership in every level. The script's order search has cap 200 and does not prove infinite order.

## Triage

### What the settlement shows

- **Settlement — kernel-checked:** `AndersonWeippertQuditControlledOrder.result` proves the exact binding claim for every prime $p$, every $n\geq0$, unitary target $U$, block-one control, and membership at some finite level. The order includes the global phase.
- **Arithmetic mechanism — kernel-checked:** the private `CyclicDifferencePrimeContent.content_prime_power` proves that the content of every positive iterated cyclic difference is a power of $p$; its live consumer is `order_prime_power_of_coeff`, consumed by `result`.
- **Hierarchy mechanism — kernel-checked:** `WeylCliffordDescent.hierarchy_terminates` proves termination of repeated commutators with a Pauli; `result` consumes it with the control shift.
- **Cyclic-polynomial description — proved in prose:** with $A_r(x)=\sum_j a_{r,j}x^j$ in $\mathbb Z[x]/(x^p-1)$, the recurrence gives $A_{r+1}=(1-x)A_r$ and $A_0=x$, hence $A_r=x(1-x)^r$ by induction. This explains the recurrence; the Lean proof uses the equivalent cyclic-vector argument.
- **Generality — kernel-checked for the block-one convention:** `result` is uniform in the number of target qudits; $n=1$ is the source's block-size formulation and $n=0$ is included. No fixed-parameter numerical certificate is delivered.
- **Other nonconstant trigger patterns — open:** the present claim and theorem do not quantify over such patterns. The suggested extension has no kernel theorem here.
- **Powered-control conventions — open:** $\operatorname{diag}(I,U,\ldots,U^{p-1})$ is not the control convention of this theorem.
- **Converse and least hierarchy level — open:** prime-power order is a proved necessary condition; no sufficiency or least-level classification is asserted.
- **Finite convention checks — computed:** the pinned experiment in Evidence, exit 0 and the stated SHA-256, covers exactly the listed qubit and qutrit gates and level cutoffs. Its finite readings do not supply the uniform theorem.
- **Retention — compiled declarations and dependency evidence:** the three new modules contain 51 source declarations; all retained auxiliary declarations are consumed by the settling derivation. The two existing owners publish three consumed declarations, with their statements and proofs unchanged. The helper-to-consumer map is obtained from elaborated proof terms; no unused scratch facts are part of the mathematical delivery.
- **Consequences for the source — mathematical scope:** the qudit necessity now holds for the stated convention. The source's qubit results remain unchanged; no source theorem is replaced by a converse, a level formula, or an assertion about other control conventions.
- **Literature — literature reading:** the preregistration's inspected source and follow-ups do not supply this settlement in that searched scope. Completeness remains `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority. Extensions to other trigger patterns and powered control, the converse, and the least hierarchy level remain open. The finite numerical experiment is not evidence of uniform membership or nonmembership beyond its cutoffs. Four-slot escape registration is unfinished under issue #20302.
