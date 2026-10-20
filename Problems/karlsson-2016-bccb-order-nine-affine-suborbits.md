---
slug: karlsson-2016-bccb-order-nine-affine-suborbits
bibkey: karlsson2016bccbhadamard
doi: 10.1016/j.laa.2016.04.012
url: https://arxiv.org/abs/1604.03770v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.result
---

# The two Karlsson families are the only affine suborbits of BC_9^(2)

## Problem

B. R. Karlsson, *BCCB complex Hadamard matrices of order 9, and MUBs*, arXiv:1604.03770v1, Linear Algebra Appl. 504 (2016), Conjecture 3:

> $BC_{9A}^{(1)}$ and $BC{}_{9B}^{(1)}$ are the only affine suborbits of $BC_{9}^{(2)}$.

The definition of an affine orbit, the matrix, the unitarity locus x + y + u + w = 1 and the two families are quoted in [the literature note](../Library/QuantumContext/karlsson2016bccbhadamard.md).

Issue [#19395](https://github.com/the-omega-institute/trureturing/issues/19395) fixes the reading. Consider:
- a nonconstant family of four unit parameters on a nonempty open subset of ℝ^p with sum 1;
- whose canonically dephased matrix has entries of the form c e^{iL(t)} with L linear.

Up to a fixed permutation of the parameters, such a family is (μ, −μ, −ω, −ω²) or (1, ξ, ωξ, ω²ξ). The conjecture is proved.

## Motivation

The paper constructs BC_9^{(2)}, a two-parameter non-affine orbit of order-9 complex Hadamard matrices that does not lie in the Fourier orbit F_9^{(4)}. It identifies two affine one-parameter suborbits. BC_{9A}^{(1)} is not a suborbit of the Fourier orbit; BC_{9B}^{(1)} is its intersection with the Fourier orbit. The source supports exhaustion only by a rotational heuristic on the polygon x + y + u + w = 1.

## Gap

The literature check before any Lean is recorded in #19395:
- arXiv has only v1;
- OpenAlex lists 8 citing works. The orchestrator checked arXiv:2306.00999 and arXiv:2204.11727, which use or cite the paper without a classification. The search seat checked the others, except one order-6 paper that returned HTTP 403;
- Zenodo and the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Bridge.** The dephased entries at (1,2), (3,6), (4,8) and (5,7) (zero-based) are 1/x, 1/y, 1/u and 1/w. So each parameter is c_j e^{i L_j(t)} on U, with |c_j| = 1.
2. **Independence.** The function Σ_j c_j e^{i L_j(t)} − 1 is real-analytic and vanishes on the open set U, so it vanishes on ℝ^p. The characters t ↦ e^{i L(t)} of distinct linear forms are linearly independent (Dedekind). So the coefficients over each frequency class sum to 1 for the zero form and to 0 otherwise.
3. **Counting.** The zero class is nonempty. A nonzero class has at least two members, and the family is nonconstant. So there is exactly one nonzero class, of size 2 or 3.
4. **Unit-circle algebra.**
   - With two varying members a and −a, the constants b and c satisfy b + c = 1 and |b| = |c| = 1, so b² − b + 1 = 0 and {b,c} = {−ω, −ω²}.
   - With three varying members, the constant is 1, and the ratios r and s satisfy 1 + r + s = 0 with |r| = |s| = 1. So {r,s} = {ω, ω²}.

## Falsifier

The proof would not settle the conjecture if the module's notion of affine suborbit were narrower than the source's. The module:
- takes the source's matrix on the locus x + y + u + w = 1 of unit parameters, which is BC_9^{(2)} by §5–§6;
- dephases it by its first row and column, as §2 prescribes;
- calls a family affine when every dephased entry has a phase linear in the parameters on an open parameter set, allowing any number p of parameters;
- excludes only constant families.

## Evidence

The canonical source is `D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.lean` (363 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits.lean.json`, statement `sha256:7f7fef48e200e5b4623dbdc3994f864aa5e93ac0ed9b7f69618e270a9ab94929`.

Declaration statements:
- `result`: `sha256:c26cfe4a79622006fe1b7f9d0cab510725d972cb751e7818844dae72f746fef5`;
- `claim`: `sha256:f86ff6593afb370c99af1ac798304d94318a081ddd9776b104c084586be7f777`.

## Triage

Tier 1 conjecture of a 2016 paper, preregistered in issue #19395 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** every nonconstant affine family on an open parameter set lies, after a fixed permutation of the parameters, in BC_{9A}^{(1)} or BC_{9B}^{(1)}. This holds for any number of parameters, so there is no affine suborbit of dimension two or more.

**Computed, not formalized** (orchestrator, recorded in #19395): for random μ and ξ, both families satisfy σ = 1 and H^†H = 9I to machine precision.

**Argued, not formalized.**
- *Mechanism.* An affine family moves each parameter along a character e^{iL(t)}. A unit-modulus sum can stay equal to 1 only if every nonconstant frequency cancels inside its own class. With four unit vectors this leaves either a cancelling pair, whose rotation is μ, or an equilateral triple, whose rotation is ξ. This is the rotational picture of the source made exhaustive.
- *Scope.* The argument uses only the four dephased entries 1/x, 1/y, 1/u, 1/w, unit modulus and the sum condition. It uses no other property of the matrix.

**Effect on the paper.** Conjecture 3 holds. The two families described in §8.1–§8.2 exhaust the affine suborbits of BC_9^{(2)}.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v1. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
