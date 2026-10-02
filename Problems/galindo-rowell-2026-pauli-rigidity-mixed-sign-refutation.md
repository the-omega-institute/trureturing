---
slug: galindo-rowell-2026-pauli-rigidity-mixed-sign-refutation
bibkey: galindorowell2026unitaryyb
doi: null
url: https://arxiv.org/abs/2608.16865
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.result
---

# A mixed-sign Gaussian refutes Galindo–Rowell Conjecture 10.6

## Problem

C. Galindo and E. C. Rowell, *Unitary Yang–Baxter Operators: Towards a Classification*, arXiv:2608.16865v1, Conjecture 10.6 (§10.2.7), state:

> Let $d\geq2$ with $4\nmid d$, let $\alpha\in(\mathbb Z/d\mathbb Z)^\times$, and put $P_\alpha=X\otimes Z^\alpha$, $\tau_\alpha(s,t)=w^{\alpha st}$. If $a=(1,a_1,\ldots,a_{d-1})\in\mathbb T_d^{\mathrm{coef}}$, $R_\alpha(a)$ satisfies the Yang–Baxter equation, and $R_\alpha(a)$ is projectively unitary, then there is one sign $\epsilon\in\{+1,-1\}$ with $a_{s+t}=a_sa_t\tau_\alpha(s,t)^\epsilon$ for every $s,t\in\mathbb Z/d\mathbb Z$.

The Lean `claim` is this quantified statement with `ZMod d`, the displayed braid equation, and Mathlib projective unitarity. The theorem `result` proves its negation.

## Motivation

The source records exact computations for dimensions $2,3,5,6,7,9,10,11$. Dimension $15$ admits a mixed-sign quadratic phase whose polarization exponent is $4$ modulo $15$, while the two conjectured signs have exponents $1$ and $14$. This supplies a concrete counterexample outside the listed computations.

## Gap

Issue #11573 preregistered the named conjecture, its full quantifiers, the $d=15$ route, and a bounded literature screen before formalization. The source has arXiv version 1 only. Searches in the preregistration found no proof or refutation of Conjecture 10.6 in the searched scope; citing works not independently checked remain outside the settlement.

## Route

Take $d=15$, $\alpha=1$, a primitive fifteenth root $w$, and
$$
a_t=w^{2t^2}.
$$
The proof establishes the coefficient-to-operator bridge for the braid equation, translates the finite character sum to prove the coefficient identity, and uses character orthogonality to obtain $R R^\dagger=15I$. Thus $(\sqrt{15})^{-1}R$ is unitary. At $s=t=1$, the claimed signs would require $w^8=w^5$ or $w^8=w^3$, which contradicts primitivity.

## Falsifier

A primitive fifteenth root satisfying one of the two displayed equalities would break the final contradiction. A failure of the coefficient identity, the braid equation, or $R R^\dagger=15I$ would also invalidate the witness. The kernel-checked theorem establishes all of these obligations for the stated definitions.

## Evidence

- Lean module: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.lean`.
- Public declarations are the definitions required by the settlement (`clockZ`, `P`, `R`, `BraidYBE`, `ProjectivelyUnitary`), the definition `claim`, and the theorem `result : ¬ claim`.
- `make lean` and the direct module build complete with exit 0. The theorem's `#print axioms` closure is `[propext, Classical.choice, Quot.sound]`, the repository's standard three axioms.
- The finite character-sum translation, the orthogonality calculation, and the sign contradiction are checked by the proof term in `result`; no numerical approximation is used by the theorem.

## Triage

### What the settlement shows

The Pauli-direction rigidity assertion is false for the stated generality: Yang–Baxter and projective unitarity do not force the coefficient polarization into the two signed Gaussian torsors. The failure mechanism is a mixed-sign Gaussian at $d=15$, where the polarization exponent $4$ is a nontrivial square root of $1$ modulo $15$. The source's definitions of the shift, clock, cyclic operator, braid equation, and projective unitarity remain valid. The proposed restrictions excluding this $d=15$ mechanism and any revised torsor classifications are open; this delivery settles only the registered universal claim.

`theorem`: this dossier settles Conjecture 10.6 only in the quantified form encoded by `claim`; it does not settle the paper's other conjectures or its equivalent classification sentence beyond the witness supplied here.

## ASSUMED-UNVERIFIED

The literature statement is bounded by the searches recorded in issue #11573. Citing lists and inaccessible search surfaces were not independently verified, so exhaustive literature coverage and publication priority are `ASSUMED-UNVERIFIED`.

Registration is paused under CLAUDE.md §3.9 (信息逃逸登记暂缓).
