---
slug: de-vos-de-baerdemacker-2014-unitary-scaling-landscape-refutation
bibkey: devos2014scalingunitary
doi: 10.1142/S1230161214500139
url: https://arxiv.org/abs/1401.7883v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.result
---

# The unitary scaling landscape has a nonglobal local minimum

## Problem

A. De Vos and S. De Baerdemacker, *Scaling a unitary matrix*, arXiv:1401.7883v2, Open Syst. Inf. Dyn. 21 (2014) 1450013, Appendix B:

> We conjecture that all these stationary points are either maxima or saddle points or global minima. In other words: we conjecture that no local minima exist. Moreover, we conjecture that the global minima satisfy~$\Psi=0$.

The landscape Ψ(λ, ρ) = n² − |sum(B)|² with B_{jk} = e^{i(λ_j+ρ_k)} A_{jk} is quoted in [the literature note](../Library/QuantumContext/devos2014scalingunitary.md).

Issue [#19521](https://github.com/the-omega-institute/trureturing/issues/19521) fixes the reading: for every unitary A, every local minimum of Ψ_A is a global minimum. This first sentence of the conjecture is refuted. The second sentence, that global minima have Ψ = 0, is the existence of a scaling, attributed in the v2 comment to Idel and Wolf.

## Motivation

The landscape governs the authors' iterative algorithm for scaling a unitary matrix to one with all line sums 1, which yields a decomposition of U(n) into diagonal and doubly stochastic unitary factors. If every local minimum were global, descent on Ψ could not get stuck.

## Gap

The literature check before any Lean is recorded in #19521:
- arXiv:1408.5728 (Idel–Wolf) proves existence of a scaling and leaves convergence of the algorithm open;
- OpenAlex lists 14 citing works. The search seat checked Führ–Rzeszotnik arXiv:1506.06738, De Vos–De Baerdemacker 2015 and Glos–Sadowski arXiv:1510.00606, among others, and none answers the landscape conjecture;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Take n = 3 and A = (1/34)[[−2, 24, 24], [24, 1+17i, 1−17i], [24, 1−17i, 1+17i]].
1. **Unitarity.** A is unitary, by direct computation of A†A.
2. **Value at 0.** sum(A) = 49/17, so Ψ_A(0) = 200/289.
3. **Local minimum.** For phases with |ρ₂ − ρ₃| < 1/50, |sum(B)| ≤ Σ_j |(A y)_j| ≤ 49/17, where y_k = e^{iρ_k}. The second inequality is a radial certificate after removing the common column phase. It uses |sin v| ≤ |v|, cos v ≥ 1 − v²/2 and difference-of-squares estimates for the three row moduli. So Ψ_A ≥ 200/289 on an open neighbourhood of 0.
4. **Not global.** At ρ = (0, 2π/3, π/3), the three moduli |(A y)_j| sum to more than 49/17. Aligning λ_j = −arg (A y)_j makes |sum(B)| equal to that sum, so Ψ_A < 200/289 there.

## Falsifier

The refutation would fail if the module's landscape or the notion of local minimum differed from the source's. The module:
- uses Ψ_A(λ, ρ) = n² − |Σ_{j,k} e^{i(λ_j+ρ_k)} A_{jk}|² on ℝⁿ × ℝⁿ, as in Appendix B;
- uses Mathlib's `IsLocalMin` in the product topology, and global minimality over all of ℝⁿ × ℝⁿ.

The witness 0 is a genuine local minimum, not only a stationary point. The comparison point shows it is not global.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.lean` (280 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/UnitaryScalingLandscapeRefutation.lean.json`, statement `sha256:d52c86cb2eb26dd5cacf6af5ce6d80ddfed7c891e83019f33099f81b9bbab32e`.

Declaration statements:
- `result`: `sha256:ef9c0e6adc20723970bd2d8a69dedf2b4b538d4c59a1e2d7c97c380df6d48b59`;
- `claim`: `sha256:47c40c8cb00dbe502041e141e62c0ecdaf8398175e6cfda097c22852fad3420c`.

## Triage

Tier 1 conjecture of a 2014 paper, preregistered in issue #19521 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for n = 3 the landscape of the unitary A above has a local minimum at 0, with value 200/289, that is not a global minimum.

**Computed, not formalized** (orchestrator, numpy, recorded in #19521):
- the Hessian at 0 has eigenvalues 0, 0, 0.2076, 4.408, 4.408 and 12.21, the two zeros being the phase gauge directions;
- a global search from other starting points reaches Ψ ≈ 4·10⁻¹³, so a scaling of A exists, as Idel–Wolf predict.

**Argued, not formalized.**
- *Mechanism.* At ρ = 0 the row sums of A are real and positive (23/17, 13/17, 13/17), so the three row contributions to sum(B) are aligned. The radial certificate shows that no nearby column phases increase the total of the row moduli. The phase directions that keep Ψ constant are the two gauge directions.
- *Consequence for descent.* Started at 0, a method that only accepts decreases of Ψ cannot move, although Ψ = 0 is attainable elsewhere. So descent on the landscape does not reach a scaling from every starting point.
- *Scope.* The conjectured trichotomy fails in its third class: some stationary points with 0 < Ψ < n² are local minima, not saddles.

**Effect on the paper.** The conjecture that no local minima exist is false. The existence of a scaling, the second sentence, is unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v2. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
