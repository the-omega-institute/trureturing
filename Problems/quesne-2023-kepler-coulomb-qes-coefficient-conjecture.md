---
slug: quesne-2023-kepler-coulomb-qes-coefficient-conjecture
bibkey: quesne2023keplercoulomb
doi: 10.1016/j.aop.2023.169265
url: https://arxiv.org/abs/2206.01033v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.result
---

# The coefficient system of Quesne's Kepler–Coulomb extensions on the sphere has the conjectured closed forms for every m

## Problem

C. Quesne, *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*, Ann. Phys. 451, 169265 (2023), arXiv:2206.01033v3, builds extensions of the Kepler–Coulomb potential on a sphere of curvature κ with 2m additional terms and known ground and first excited states.
- **The system.** The generating-function method (§4.1, Eq. (4.10)) expresses the first two superpotentials through m + 1 constants a_0, …, a_m, which must solve the linear system (4.13)–(4.17) in the rescaled coupling Q and κ (§4.2).
- **The conjecture.** From the solutions for m ≤ 7: "Conjecture For any m > 1, the solution of the system of equations (4.13)–(4.17) can be written as" the closed forms (4.19)–(4.21) for m = 2µ + 1 and (4.22)–(4.24) for m = 2µ. They share the denominator Q^{2µ} + b_1κQ^{2µ−2} + ⋯ + b_µκ^µ, and the odd-index numerators contain brackets with constants c_j^{(k)}, "where b_1, b_2, …, b_µ, and c^{(k)}_1, c^{(k)}_2, …, c^{(k)}_{µ−k} or c^{(k)}_{µ−k−1} are some positive constants."
- **The open problem.** §5: "The problem that remains open is to prove our conjecture by finding the explicit values of the constants appearing …"

The verbatim statements are in [the literature note](../Library/Eigenstructure/quesne2023keplercoulomb.md).

Issue [#17076](https://github.com/the-omega-institute/trureturing/issues/17076) fixes the reading: the constants are independent of Q and κ, and for all Q, κ > 0 the system has a solution, every solution has the closed forms, and solutions agree on 0, …, m. The conjecture is proved for every m ≥ 2, with explicit constants.

## Motivation

By (4.28)–(4.29) the energies of the two known states depend on a_0 alone, and the source states that the wavefunctions (4.30)–(4.31) are normalizable provided a_m > 0, which it had checked only for the values of m computed explicitly. The closed forms for every m give both for the whole family of extended potentials.

## Gap

Issue #17076 records the literature check before any Lean:
- arXiv v1–v3; v3 is the published version and states the conjecture (§4.2) and the open problem (§5);
- Quesne's later arXiv papers do not treat this system by title, and the full text of the nearest one (arXiv:2401.04586v2) does not mention it;
- Banik–Singh–Roy–Panja (Comput. Math. Math. Phys., March 2026, DOI 10.1134/S0965542525701970) cite the extensions; their abstract describes a numerical scheme, and the full text was not read;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Write m = 2µ + ε with ε ∈ {0, 1}, x = Q²/κ, t_k = m − 2k − 1 and F(m, r) = m!/(m − r)!.
1. **Normalization.** With e_0 = a_0, e_k = a_{2k}/Q for k ≥ 1 and o_k = a_{2k+1} (and o_µ = 0 for even m), the system becomes (m + 1)e_0 − o_0 = 1, o_k = (t_k + 1)e_k − Σ_{l>k} e_l and t_k(o_k − o_{k+1}) = x e_{k+1}. The correspondence holds in both directions.
2. **The explicit solution.** Let P_k(x) = ∏_{r<µ−k}(x + (2r + 1 + ε)²) and E_k = F(m, 2k)P_k. Let H_k = F(m, 2µ + 1) + x Σ_{l>k} F(m, 2l − 1)P_l, and D = Σ_k E_k. The telescoping identities (t_k + 1)t_k E_k = (x + t_k²)E_{k+1}, t_k(H_k − H_{k+1}) = xE_{k+1} and (m + 1)E_0 − H_0 = D give the solution e_k = E_k(x)/D(x) and o_k = H_k(x)/D(x).
3. **Uniqueness.** Every solution satisfies (t_k + 1)t_k e_k = (x + t_k²)e_{k+1}, so it is proportional to (E_k(x)); the first equation fixes the scalar.
4. **Positive constants.** D has degree µ, leading coefficient 1 and positive coefficients in every degree; so does the bracket polynomial of the odd-index numerators (H_k for odd m, H_k/x for even m), up to the factor F(m, 2k + 1). The constants are b_j = [x^{µ−j}]D and c_j^{(k)} = [x^{deg−j}](bracket)/F(m, 2k + 1).
5. **Rescaling.** Multiplying by κ^µ turns D(Q²/κ) into Q^{2µ} + Σ_j b_jκ^jQ^{2µ−2j} and the products into the printed factors (Q² + (2r + 1 + ε)²κ), which gives (4.19)–(4.24).

## Falsifier

The proof would not settle the conjecture if the module's system differed from (4.13)–(4.17), if its closed forms differed from (4.19)–(4.24), or if its constants depended on Q or κ. The module writes the five equation families with the printed index ranges and the parity selector of (4.17), writes the printed products, factorial prefactors and brackets for each parity, and chooses the constants before Q and κ.

## Evidence

The canonical source is `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.lean` (901 lines).
- It defines `System`, `series`, `delta`, `OddForm`, `EvenForm`, `ClosedForms`, `PositiveConstants` and `claim`, and proves `result : claim` for every m ≥ 2.
- Positivity of a polynomial with positive coefficients at a nonnegative point is the frozen `NewtonHankelRealRootCriterion.eval_pos_of_positive_coefficients` (made public for this settlement). The identity (n.descFactorial i : ℝ) = n!/(n − i)! is the frozen `AlternatingFactorialSum.real_descFactorial`, which `MatchingPolynomial` also uses. The remaining steps use Mathlib's `Nat.descFactorial`, `Finset` sums and products and `Polynomial` coefficient lemmas.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.lean` reads out the coordinate a′ i of the uniqueness clause of `claim`. Its rejected realization, the constant 0, fails at m = 2 and Q = κ = 1: applied to a solution paired with itself, the modified clause forces a_0 = a_1 = 0, contradicting (m + 1)a_0 − a_1 = 1. It is `declared_validated`.
- The newly public `eval_pos_of_positive_coefficients` is registered in `Reg/D5/S3/Constants/NewtonHankelRealRootCriterion.lean`, reading out P.eval x. Its rejected realization, the constant 0, fails at P = 1, d = 0 and x = 0. It is `declared_validated`.
- The shared `real_descFactorial` is registered in `Reg/D5/S3/Zeros/Convolution/AlternatingFactorialSum.lean`, reading out (n.descFactorial i : ℝ). Its rejected realization, the constant 0, fails at n = i = 0, where the value is 1. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.lean.json`, statement `sha256:64ff65e36f629fae0ea0a33dce27ef930dee47d225b6c872f48d5aece5bee48e`.

Declaration statements:
- `result`: `sha256:6272475341279b2c9351a99e446c0bde0534fcdfea00ad7394fc7d8bba333fa1`;
- `claim`: `sha256:a8a4d4d35e2b6f35292780350e8135d5ff297e0956d6315e47a3c0e1b4a3df20`.

## Triage

Tier 1 conjecture of a 2022 paper (published 2023), preregistered in issue #17076 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the normalization, the telescoping identities, the proportionality argument, the coefficient positivity and the rescaling are obtained by instantiating pinned Mathlib results (for example `Finset.sum_Ico_sub`, `Finset.prod_range_induction` and `Finset.prod_X_add_C_coeff`) and the frozen lemmas `eval_pos_of_positive_coefficients` and `real_descFactorial`, followed by normalization | open-problem-resolution |
| the normalization, polynomial, telescoping, coefficient, uniqueness and rescaling helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 46 private theorems are bind-only helpers consumed on the proof path of `result`, and its 17 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every m ≥ 2 there are positive constants b_j and c_j^{(k)}, independent of Q and κ, such that for all Q, κ > 0 the system (4.13)–(4.17) has a solution, unique on 0, …, m, given by (4.19)–(4.24). The constants are the coefficients of the explicit polynomials of steps 2 and 4.

**Computed, not formalized** (orchestrator, SymPy, exact, 15 October 2026): for m = 2, …, 10 the system has a unique solution of the conjectured form, and every constant is a positive integer. For example, b = (3) at m = 2, b = (10) and c^{(0)} = (2) at m = 3, b = (22, 45) and c^{(0)} = (7) at m = 4, and b = (140, 5614, 64380, 99225) at m = 8. The m = 2 and m = 3 solutions agree with (4.11).

**Argued, not formalized.**
- The constants are positive integers for every m: D and the bracket polynomials have integer coefficients, being sums of products of integers, and F(m, 2k + 1) divides every coefficient of the odd-index numerator. Equivalently b_j = Σ_{k=0}^{j} F(m, 2k) e_{j−k}(t_k², …, t_{µ−1}²), with e_r the elementary symmetric polynomial.
- a_m > 0 for every m and all Q, κ > 0, because a_m is a positive multiple of κ^µ (times Q for even m) divided by the positive denominator. By the source's remark after (4.31), the two known wavefunctions are then normalizable on (0, 1/√κ) for every m.
- The mechanism is a two-term recurrence: eliminating the odd unknowns leaves (t_k + 1)t_k e_k = (x + t_k²)e_{k+1}, so e_k is e_{k+1} times (x + t_k²)/((t_k + 1)t_k), which produces the products and factorial ratios of (4.19)–(4.23).

**Open.**
- Closed forms for the potential parameters B_1, …, B_{2m} of Eq. (2.26), which the source does not give for general m.

**Effect on the paper.** The conjecture of §4.2 holds for every m > 1, with the constants given explicitly, so the energies (4.28)–(4.29) and the wavefunctions (4.30)–(4.31) are available in closed form for every member of the family.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
