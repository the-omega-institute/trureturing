---
slug: luo-zhen-liu-ebler-dahlsten-2023-neighbourhood-passivity-refutation
bibkey: luozhenliueblerdahlsten2023annealing
doi: 10.1103/PhysRevE.108.054119
url: https://arxiv.org/abs/2311.10424v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result
---

# Glauber annealing from a thermal state need not preserve neighbourhood passivity

## Problem

Y. Luo, Y.-Z. Zhen, X. Liu, D. Ebler and O. Dahlsten, *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*, arXiv:2311.10424v1, Phys. Rev. E 108, 054119 (2023), bound the activity A^D of simulated annealing with Glauber acceptance (Eqs. (30)–(36)).
- **Neighbourhood passivity** (§IV.B, Eq. (41)): P_i = Σ_{j∈N(i)} (γ′_i − γ′_j)(p_i − p_j)/(γ′_i + γ′_j), where primes denote the next step.
- **Its role.** If P_i ≥ 0 for all i, then A^D ≤ 1/2 (Eq. (40)), which would support the conjecture A^D(k) ≤ 1/2 of Eq. (39).
- **The expectation:** "as the system initially staying in a thermal state evolves towards a new thermal state in SA, we expect the passivity at least in the neighbourhoods to be preserved."

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/luozhenliueblerdahlsten2023annealing.md).

Issue [#17931](https://github.com/the-omega-institute/trureturing/issues/17931) fixes the reading: for every run from a Gibbs state on a connected regular neighbourhood with distinct energies and a strictly cooling schedule, P_i(k) ≥ 0 for every step k and state i. This expectation is refuted.

## Motivation

The paper uses neighbourhood passivity as the mechanism behind the activity bound A^D ≤ 1/2, which enters its bound on annealing performance. A failure of the mechanism leaves Eq. (39) supported only by its numerical evidence.

This repository settled a different statement of the same paper, Eq. (50), in #17238 ([dossier](luo-zhen-liu-ebler-dahlsten-2023-relaxation-order-refutation.md)).

## Gap

Issue #17931 records the literature check before any Lean:
- arXiv v1 is the only version;
- the companion arXiv:2311.10422 keeps Eq. (39) without settling the expectation (search seat);
- arXiv searches for neighbourhood passivity, the authors and the activity bound return only the source and its companion;
- the repository recorded only Eq. (50).

`not-found-in-searched-scope`.

## Route

1. **Witness.** The Petersen graph on ten states, which is connected and 3-regular.
   - Energies E = (3, 4, 6, 7, 5, 2, 8, 0, 1, 9), all distinct.
   - Inverse temperatures β(0) = log(11/10), β(1) = log 4 and β(2) = log 8, extended strictly increasingly.
   - The Gibbs states are rational: γ_i(log q) = q^{−E_i}/Σ_j q^{−E_j}.
2. **One step.** p(1) = P(1)γ(β(0)) is computed exactly; it is a strictly positive probability vector.
3. **The violation.** At state 0, with neighbours 1, 4 and 5 and weights 7/9, 63/65 and −7/9 at β(2):
   P_0(1) = (7/9)(p_0(1) − p_1(1)) + (63/65)(p_0(1) − p_4(1)) − (7/9)(p_0(1) − p_5(1)) = −1454086156987/205381037283201 < 0.

## Falsifier

The refutation would not settle the expectation if:
- the module's chain differed from Eqs. (30)–(32);
- its passivity differed from Eq. (41), in particular in the temperature of the Gibbs weights;
- the witness started outside a Gibbs state or used a degenerate graph or schedule.

The module reuses the frozen definitions of the Eq. (50) settlement for the regular neighbourhood, the Gibbs state, the Glauber matrix and the annealing run. Its passivity uses the Gibbs weights at β(k + 1) and p(k), as the source's primes prescribe. The witness graph is connected and regular, the energies are distinct, and the schedule is positive and strictly increasing.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.lean` (351 lines).
- It defines `neighbourhoodPassivity` and `claim`, and proves `result : ¬ claim`.
- It reuses `regularNeighborhood`, `gibbs`, `glauber` and `isSARun` of `GlauberRelaxationOrderRefutation`, whose `probability_mulVec` it makes public by removing only `private`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The newly public `GlauberRelaxationOrderRefutation.probability_mulVec` is registered in `Reg/D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.lean`, `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.lean.json`, statement `sha256:1ad105980c2fa1a3f4d7d0d9bf53f1d6fac58593c1f85dc8edabaac3670d912b`.

Declaration statements:
- `result`: `sha256:dfc895cff4730401ed7d6e368f13ec9130c066e40c0f374df074bdc1dea1bee5`;
- `claim`: `sha256:d0db9deb54284f8175d445199bfa0baf84e79ae480208ebb75cb402c83fda7b1`.

## Triage

Tier 1 expectation of a 2023 paper, preregistered in issue #17931 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the graph checks are decidable finite facts, and the run and the passivity value are rational computations | open-problem-resolution |
| the witness and run helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** on the Petersen graph, one Glauber step of a cooling run from a thermal state makes P_0(1) negative.

**Computed, not formalized** (orchestrator, exact rational arithmetic on the same run):
- the minimum of P_i(0) is about 0.0298, so passivity holds at the start;
- the other nine P_i(1) lie between 0.178 and 0.553.

**Argued, not formalized.**
- *Mechanism.* State 5 has lower energy than state 0, but its other neighbours 7 and 8 have even lower energies (0 and 1). One step therefore drains state 5 below state 0, p_5(1) < p_0(1). The neighbourhood sum at state 0 weighs this inverted pair with the same magnitude 7/9 as the pair with state 1. The inverted pair outweighs the two passive contributions.
- *What survives.* The aggregate quantity of Eq. (40) may still give A^D ≤ 1/2: neighbourhood passivity is sufficient for the activity bound, not necessary. The search seat reports A^D < 1/2 along this run; this is not formalized.

**Open.** Eq. (39), A^D(k) ≤ 1/2 for annealing with Glauber dynamics, is not addressed.

**Effect on the paper.** The passivity mechanism offered in §IV.B for Eq. (39) does not hold in general. Eq. (39) rests on its numerical evidence.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
