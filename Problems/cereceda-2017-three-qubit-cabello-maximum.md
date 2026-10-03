---
slug: cereceda-2017-three-qubit-cabello-maximum
bibkey: cereceda2017cabello
doi: 10.1007/s40509-016-0093-7
url: https://arxiv.org/abs/1609.04763v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result
---

# The maximal three-qubit violation of Cabello's nonlocality argument

## Problem

J. L. Cereceda, *Cabello's nonlocality for generalized three-qubit GHZ
states*, arXiv:1609.04763v2, Section 2, and Quantum Stud. Math. Found. 4(3)
(2017) 205–215, conjectures:

> we conjecture that, for the case in which $Q >0$, the maximum quantum violation of inequality (ineq2) (subject to the fulfillment of conditions (hc2)-(hc4)) is achieved, over all possible states and choice of observables, for the GHZ state $|\psi \rangle =\frac{1}{\sqrt{2}}(|v_1, v_2,v_3 \rangle + |w_1, w_2, w_3 \rangle)$, with the maximum violation being equal to $C_{\text{max}} =\frac{9}{64}$.

Here $P = P(U_1,U_2,U_3|+++)$, $Q = P(D_1,D_2,D_3|---)$, the conditions
(hc2)–(hc4) are $P(D_1,U_2,U_3|+++) = P(U_1,D_2,U_3|+++) =
P(U_1,U_2,D_3|+++) = 0$, and (ineq2) is $C = P - Q \le 0$; each $U_k$, $D_k$
is a $\pm1$-valued projective qubit observable. The conclusions restate the
conjecture for all entangled states of three qubits.

## Motivation

Cabello's argument extends Hardy's proof of nonlocality without
inequalities: when $Q < P$ the conditions contradict local realism, and $C$
measures its success. The paper computes the maximum $9/64$ for the
generalized GHZ states and conjectures that no three-qubit state does better.
The frozen declaration
`D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result` refutes the
conjecture.

## Gap

Issue #11927 classifies the conjecture as Tier 1 and records the bounded
literature check before any Lean: arXiv v2 is the latest version; the four
citing works listed by Semantic Scholar (arXiv:2001.02143, 2311.02045,
2601.18861, 2603.12738) do not treat the three-qubit maximum or $9/64$;
arXiv:2103.09919 treats the two-qubit case; web searches return only the
paper itself.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

1. Take $U_k=\sigma_z$, with eigenvectors $|0\rangle$, $|1\rangle$, and $D_k$
   with eigenvectors $d^+=(3|0\rangle+4|1\rangle)/5$ and
   $d^-=(-4|0\rangle+3|1\rangle)/5$ on every qubit.
2. Take
   $\psi=(16|000\rangle-12(|001\rangle+|010\rangle+|100\rangle)-15(|011\rangle+|101\rangle+|110\rangle)+9|111\rangle)/38$;
   since $16^2+3\cdot12^2+3\cdot15^2+9^2=38^2$ it is a unit vector.
3. Each constraint amplitude is $(3\cdot16-4\cdot12)/(5\cdot38)=0$.
4. $P=(16/38)^2=64/361$, $\langle d^-d^-d^-|\psi\rangle=-889/4750$,
   $Q=790321/22562500>0$ and $C=3209679/22562500=9/64+589239/361000000$.
5. $\psi$ is genuinely entangled: across each cut $k\,|\,\text{rest}$ a
   $2\times2$ determinant of its coordinates is
   $(16\cdot(-15)-(-12)(-12))/38^2\ne0$.

## Falsifier

The kernel-checked `result` excludes the bound $C\le9/64$ under the stated
conditions for genuinely entangled states, hence for all entangled states and
for all states. Changing the probabilities from $|\langle a\otimes b\otimes
c|\psi\rangle|^2$ for unit $\psi$, or the three vanishing conditions, would
change the question.

## Evidence

Exact `Fraction` arithmetic and an independent NumPy computation with
Kronecker products give the values above; with the same checker, the paper's
optimum ($t=1$, $x=y=z=1$, $\gamma=-\arccos(7/8)$) gives $P=10/64$,
$Q=1/64$, $C=9/64$ as a positive control (issue #11927).

The canonical source is
`D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.lean`. Its public
declarations are `amp`, `prob`, `IsONB`, `ProductCut1`, `ProductCut2`,
`ProductCut3`, `GenuinelyEntangled`, `claim` and `result`. The frozen module
state has statement identity `sha256:288ed74584004e463c75a6602111593c7a47e47a5e26211a8711f178a0ca41fe`. The result declaration has statement
identity `sha256:38bf23cdc6137069c6f0a403a7ec25d060d96e3cdb35749df566279d765db889`. The Freeze event is `sha256:845b119b6180ac292907b38d48bb835c3bff3b9df3ba46a99fe2527e540d470d`. It has no project-level
frozen prerequisites (pinned Mathlib only). The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.result`.
`proof_shape: bind-only` (evaluation at an explicit state and observables);
`admission_basis: open-problem-resolution` (issue #11927). Utility
`certified-instance`, refuting `claim`.

### What the refutation shows

- **Proved in this module:** there are a genuinely entangled unit
  three-qubit state and local observables satisfying the three vanishing
  conditions with $Q>0$ and $C=3209679/22562500>9/64$.
- **Where the conjecture fails:** the paper maximizes $C$ over the
  generalized GHZ states $t|v_1v_2v_3\rangle+|w_1w_2w_3\rangle$, and the
  extension of that maximum to all states is what fails. The witness lies
  outside that family (computed, not formalized): its two-qubit reduced
  states have concurrence about $0.0865$, while every state of the family,
  in any local bases, has two-qubit reduced states of concurrence $0$ (a
  NumPy control with random local unitaries gives $0$). The paper's
  computation for its family stands (the checker reproduces $9/64$ there).
- **Computed, not formalized (scout reading):** numerical optimization over
  general states reaches about $0.14479$; the true three-qubit maximum of $C$
  under these conditions is open here.
- **Computed, not formalized (orchestrator):** among symmetric real states
  with these observables and integer amplitudes up to $60$, 14 witnesses
  have a perfect-square norm; the one above has the smallest.
- **Unchanged:** the paper's results on the generalized GHZ family, on
  Hardy's argument ($Q=0$, maximum $1/8$) and on generalized no-signaling
  theories do not depend on the conjecture.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent counterexample; in particular the journal text was
not read. The Lean kernel verifies the encoded statement and its axiom
closure; correspondence to the external paper, including the reading of
"gives the outcome $+1$" as the projection onto the $+1$ eigenvector and the
restriction to genuinely entangled states as a weakening, is checked by
reading the source, the definitions and the mirror.
