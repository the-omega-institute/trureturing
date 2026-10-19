---
slug: marquette-vanderkamp-quispel-2026-lotka-volterra-birationality
bibkey: marquette2026lotkavolterra
doi: null
url: https://arxiv.org/abs/2602.17945v1
triage: theorem
motivation_gids:
  - D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.result
---

# The Lotka–Volterra integrals are birational coordinates in every dimension

## Problem

I. Marquette, P. H. van der Kamp and G. R. W. Quispel, *Subalgebras of integrals, commutants, and superintegrable deformations of Lotka–Volterra systems*, arXiv:2602.17945v1, Section 2:

> In arbitrary dimensions, we have not been able to prove the birationality of the change of variables, but we conjecture this to be the case, and we provide explicit formulas in Appendix \ref{secA}.

Appendix A restates it: "We conjecture that the transformation from the $n$ variables $x_i$ to the $n-1$ integrals and distinguished variable $x_n$ is a birational map." The integrals F_k and their coordinate reversals G_k are quoted in [the literature note](../Library/FluidDynamics/marquette2026lotkavolterra.md).

Issue [#19118](https://github.com/the-omega-institute/trureturing/issues/19118) fixes the reading: for every n ≥ 2 and every field of characteristic zero, the following n elements generate the rational function field F(x_1, …, x_n):
- odd n = 2m − 1: F_1, …, F_m, G_2, …, G_{m−1}, x_n;
- even n = 2m: F_1, …, F_m, G_1, …, G_{m−1}, x_n.

This is proved.

## Motivation

Birational coordinates make every rational observable a rational function of the known integrals and one evolving coordinate. That is the coordinate change the source's completeness method for rational first integrals needs.

## Gap

The literature check before any Lean is recorded in #19118:
- arXiv v1 is the only version;
- OpenAlex lists no citing work;
- the repository had no record of the paper.

The source reports Maple verification of its inverse formulas for m ≤ 7 (odd) and m ≤ 8 (even) only. `not-found-in-searched-scope`.

## Route

Write S_i = x_1 + ⋯ + x_i and H = S_n.
- **Odd n.** Two families of product identities hold: F_k G_{m−k}/F_1 = S_{2k−1}(H − S_{2k})/x_{2k} and F_k G_{m−k+1}/F_1 = S_{2k−1}(H − S_{2k−2})/x_{2k−1}.
  - They place D_i = S_{i−1}(H − S_i)/x_i in the generated field.
  - Starting from S_{n−1} = H − x_n, the recursion S_{i−1} = D_i S_i/(H − S_i + D_i) recovers every partial sum.
- **Even n.** The recovery runs in three steps:
  - x_{n−1} and the ratio product P = ∏ x_{2j}/x_{2j−1} come from F_{m−1}, G_1 and x_n;
  - the even partial sums S_{2k} = H F_k/(F_k + P G_{m−k}) follow;
  - the ratios R_k = G_{m−k}/(H − S_{2k}) give each coordinate pair.

Each denominator is a nonzero rational function, since nonempty sums of distinct variables do not vanish.

## Falsifier

The theorem would not settle the question if the module's integrals differed from the source's. The module:
- defines F_k literally in both parities, translating one-based indices to `Fin n`;
- defines G_k by the reindexed product of the coordinate reversal ι(F_k), in which the initial sum becomes H − S_{2(m−k)};
- takes as inputs the n − 1 distinct integrals of Proposition 8 and x_n.

The list displayed in Appendix A.2 for even n omits G_1. The reading follows Proposition 8 and the source's equation (63).

## Evidence

The canonical source is `D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.lean` (604 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registration.** `Reg/D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.lean` registers `result`, but the state is `declared_unresolved`. Verdict `IE-C050 … rule=source.dictionary_or_proof_coordinate`: the readout depends on the instance-implicit `Field F` binder. The template gap is tracked in issue #16937, and the escape audit of this delivery is incomplete.

Frozen state: `Golden/Frozen/state/D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.lean.json`, statement `sha256:5ffd5ccc723ab39c6e47df59153fd4e8cc6aba885f7d09f7e420b35b5758dc0b`.

Declaration statements:
- `result`: `sha256:b7aa6d99c07e3b0a7c41f9b0cd0285a18ff9f964ed410886cb1cd71cc2524a85`;
- `claim`: `sha256:ff0abb575bc46e0fec0edcebad39966cfad57c526f8098ccd0a9a333aa648609`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #19118 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |
| definitions | bind-only | none | definitions used by `claim` |
| private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The module states a general theorem, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** in every dimension n ≥ 2, the n − 1 distinct integrals and x_n generate the rational function field. A generating set of n elements of a field of transcendence degree n is algebraically independent, so the coordinate change is birational.

**Computed, not formalized** (orchestrator, recorded in #19118): SymPy confirms the product identities and the reconstruction for n = 3, …, 8.

**Argued, not formalized.**
- *Mechanism.* Each integral is a partial sum times a telescoping ratio product. Pairing a forward integral with a reversed one cancels every ratio except one coordinate, which leaves a rational expression in two partial sums. Hence the partial sums, and then the coordinates, can be read off one at a time.
- *Inverse formulas.* The proof gives explicit inverse formulas. The source's longer formulas of Appendix A are not needed and are not checked here.
- *Characteristic.* The argument uses only that nonempty sums of distinct variables are nonzero, which holds over every field. The theorem is stated in characteristic zero, as in the source.

**Effect on the paper.** The birationality used in the paper's completeness argument holds in every dimension.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
