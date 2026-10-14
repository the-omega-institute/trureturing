---
slug: adamopoulou-papamikos-2025-grassmann-measure-refutation
bibkey: adamopoulou2025entwininggrassmann
doi: 10.1016/j.physd.2024.134469
url: https://arxiv.org/abs/2311.18673v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.result
---

# The Grassmann entwining Yang–Baxter map S over Γ(3) does not preserve the measure y₁₁⁻³

## Problem

P. Adamopoulou and G. Papamikos, *Entwining Yang–Baxter maps over Grassmann algebras*, Physica D 472, 134469 (2025), arXiv:2311.18673v1, construct birational entwining Yang–Baxter maps R_{a,b}, S_{a,b}, T_{a,b} with variables in the Grassmann algebra Γ(n) (Eqs. (17)–(19)).
- **The map.** S_{a,b} (Eq. (18)) sends (x₁, x₂, χ₁, χ₂, y₁, y₂, ψ₁, ψ₂), with x, y even and χ, ψ odd, to u₁ = y₁²(1 + χ₁ψ₂)/(b x₁) + y₁(y₂ − a − ψ₁ψ₂)/b, u₂ = b/y₁, v₁ = x₁, v₂ = a + x₁x₂ − y₁/x₁ + χ₁χ₂, ξ₁ = ψ₁ − (y₁/x₁)χ₁, ξ₂ = ψ₂, η₁ = χ₁, η₂ = χ₂ + (y₁/x₁)ψ₂. Expanding every variable in a basis of Γ(n) gives a map on 2^{n+2} commutative coordinates.
- **Measure preservation.** A map preserves the measure m when its Jacobian determinant is J = m(z)/m(S(z)) (§4). The authors verify m = 1/y₁ for n = 1 and m = 1/y₁₁² for n = 2.
- **The conjecture.** "We conjecture that in Γ(n) the map R_{a,b} is volume preserving for every n, while the maps S_{a,b} and T_{a,b} preserve measures of the form y₁₁^{−n} and x₁₁^{−n}, respectively".

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/adamopoulou2025entwininggrassmann.md).

Issue [#16775](https://github.com/the-omega-institute/trureturing/issues/16775) fixes the reading: the S clause at n = 3, with J the determinant of the derivative of the 32-coordinate map. Refuting one clause at one n refutes the conjecture, a conjunction over all n of clauses for R, S and T. The S clause is refuted.

## Motivation

Invariant measures are a standard integrability property of discrete maps, and the conjecture predicts the measure for the whole hierarchy of commutative maps obtained by fixing n. The refutation shows that the exponent of y₁₁ in the n = 1 and n = 2 measures does not continue as n.

## Gap

Issue #16775 records the literature check before any Lean:
- arXiv v1 is the only version; the journal text was not read (the publisher page did not return it, and Firecrawl had no credits), so its agreement with v1 is `ASSUMED-UNVERIFIED`;
- Semantic Scholar lists 11 citing works; the full texts of the seven with arXiv identifiers cite the paper only in passing, and none of these seven addresses the conjecture; the other four were identified by title only, and their contents were not read;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Take a = 1, b = 2 and the point z₀ whose scalar coefficients are x₁ = 1, x₂ = 3, y₁ = 2, y₂ = 4, with every other coefficient 0.
1. **Γ(3).** It is Mathlib's exterior algebra on three generators; its eight monomials give the coordinates, and the quotients of Eq. (18) are products with the two-sided inverse c⁻¹·1 − c⁻²(u − c·1) of an even element with nonzero scalar part c (its degree-two part squares to zero).
2. **The derivative at z₀.** At a point where every positive-degree coefficient vanishes, the derivatives of Grassmann products and of the inverse multiply perturbations by scalars, so they preserve the monomial index. The derivative is block diagonal, with one 4 × 4 block per monomial.
3. **The blocks.** On each of the four even monomials the block is the Jacobian of the scalar map, [[−2, 0, 7/2, 1], [0, 0, −1/2, 0], [1, 0, 0, 0], [5, 1, −1, 0]], with determinant 1/2. On each of the four odd monomials it is [[−2, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 2]], with determinant 1.
4. **The contradiction.** J = (1/2)⁴ = 1/16, while m(z₀)/m(S(z₀)) = (1/8)/1 = 1/8.

## Falsifier

The refutation would not hold if the module's algebra were not Γ(3), if its map differed from Eq. (18), if its J were not the Jacobian determinant of the coefficient map, or if m were not y₁₁⁻³. The module uses `ExteriorAlgebra ℝ (Fin 3 → ℝ)` with its monomial basis, writes Eq. (18) through the Grassmann product and the two-sided even inverse, proves that each output has the right parity so the coefficient packing is lossless, and takes `LinearMap.det` of `fderiv ℝ (F 1 2) z`.

## Evidence

The canonical source is `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.lean` (564 lines).
- It defines the coefficient chart, the Grassmann product `gmul`, the even inverse `ginv`, the selectors and packing, the coefficient map `F`, `domain`, `m`, `jacobian` and `claim`, and proves `result : ¬ claim` at z₀.
- It uses pinned Mathlib only: `Module.Basis.ExteriorAlgebra` with `ExteriorAlgebra.basis_mul_of_disjoint` and `basis_mul_of_not_disjoint`, `ContinuousLinearMap.hasFDerivAt_of_bilinear`, `hasFDerivAt_inv`, `hasFDerivAt_pi`, `LinearMap.det_toMatrix'`, `Matrix.det_reindex_self` and `Matrix.det_blockDiagonal`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.lean.json`, statement `sha256:adc23f07fa872f5a22a98d5b521e08e6e21d89222881c79903b4df12037689b8`.

Declaration statements:
- `result`: `sha256:f1e0467ed81daea2959fb1f1e831024ba3ddfd68d73b352eb5c159b106a0b84a`;
- `claim`: `sha256:72cf3887d36eff94bbdbb912cb78b262ae37d910a78c968b73f7d7b33456d15e`.

## Triage

Tier 1 conjecture of a 2025 paper, preregistered in issue #16775 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the exterior-algebra chart, the even inverse, the derivative rules at a scalar point, the block-diagonal determinant and the density ratio are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |
| the chart, parity, inverse, derivative, block and determinant helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** at n = 3 and (a, b) = (1, 2), the Jacobian determinant of S at z₀ is 1/16, while the conjectured measure requires 1/8; the S clause of the conjecture fails.

**Computed, not formalized** (orchestrator, SymPy, exact rational arithmetic, 14 October 2026): with Γ(n) implemented on monomial coefficients and the full Jacobian differentiated symbolically, J = 1/2, 1/4 and 1/16 for n = 1, 2, 3 at the scalar point (1, 3, 2, 4), against (x₁₁/y₁₁)^n = 1/2, 1/4 and 1/8. The n = 1 and n = 2 values reproduce the source's measures (control). At n = 3 the same discrepancy holds at a point with all 28 other coefficients nonzero (J = 1/16) and at the scalar point (2, 1, 3, 5) (J = 16/81 against 8/27).

**Argued, not formalized.**
- The block structure of step 2 holds at every scalar point and for every n, with 2^{n−1} even and 2^{n−1} odd monomials, which suggests J = (x₁₁/y₁₁)^{2^{n−1}} at scalar points. That agrees with the conjectured (x₁₁/y₁₁)^n exactly for n = 1, 2. The formula is consistent with the computed values above but is not proved for general n or general points.
- If that formula holds on the whole domain, the measure preserved by S over Γ(n) would be y₁₁^{−2^{n−1}}, not y₁₁^{−n}.

**Open.**
- The invariant measures of S and T over Γ(n) for n ≥ 3, and whether R_{a,b} is volume preserving for every n (the R clause of the conjecture).

**Effect on the paper.** The conjectured family of measures y₁₁^{−n} for S fails at n = 3; the paper's verified n = 1 and n = 2 measures are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal text of the paper was not compared with arXiv v1. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
