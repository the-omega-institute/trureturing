---
slug: luo-zhen-liu-ebler-dahlsten-2023-relaxation-order-refutation
bibkey: luozhenliueblerdahlsten2023annealing
doi: 10.1103/PhysRevE.108.054119
url: https://arxiv.org/abs/2311.10424v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.result
---

# A shorter relaxation time does not imply a faster energy relaxation in Glauber annealing

## Problem

Y. Luo, Y.-Z. Zhen, X. Liu, D. Ebler and O. Dahlsten, *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*, Phys. Rev. E 108, 054119 (2023), arXiv:2311.10424v1, bound the performance of simulated annealing (SA) by comparing it with a partial swap (PS) model.
- **The dynamics.** SA with Glauber acceptance moves p(k + 1) = P(k + 1)p(k), with P_ij = γ_i/(|N(j)|(γ_i + γ_j)) on neighbours (Eqs. (30)–(32)). The PS model moves p′ = p + µ^PS(γ′ − p) (Eq. (43)), and its second largest eigenvalue is 1 − µ^PS (Proposition 2).
- **The rate.** The energy relaxation rate of SA is µ = (E′_p − E_p)/(E′_γ − E_p) (Eq. (46)), under E_p ≥ E′_p and E_p ≥ E_γ ≥ E′_γ.
- **The conjecture.** With τ_rel(P) = 1/(1 − λ_2(P)): "we conjecture that the order of relaxation times of the two processes corresponding to µ and µ^PS is the inverse order of µ and µ^PS, i. e. τ_rel ≤ τ^PS_rel ⇒ µ ≥ µ^PS. (50)"

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/luozhenliueblerdahlsten2023annealing.md).

Issue [#17238](https://github.com/the-omega-institute/trureturing/issues/17238) fixes the reading: for every regular neighbourhood, energies, strictly cooling schedule, step k and rate 0 < m ≤ 1, m ≤ 1 − λ_2(P(β(k + 1))) implies µ(k) ≥ m. The conjecture is refuted.

## Motivation

Equation (50) is the step the paper uses to turn a spectral bound on the Glauber chain into the inequality µ(k) ≥ µ^PS(k), and from it E_p(k) ≤ E^PS_p(k) and the performance bound I(κ) ≤ I^PS(κ) (§IV.C–D). The companion letter, arXiv:2311.10422, rests its annealing bound on the same conjecture.

## Gap

Issue #17238 records the literature check before any Lean:
- arXiv v1 is the only version, and it states the conjecture as Eq. (50);
- the companion arXiv:2311.10422, read in full, restates it without settling it;
- the citing works listed by Semantic Scholar and Dahlsten's later arXiv papers do not treat it;
- Zenodo, Crossref, a web search, the repository Naixu-Guo/quantum-open-problems and google-deepmind/formal-conjectures gave no settlement;
- the repository had no entry for either paper.

`not-found-in-searched-scope`.

## Route

Take the cycle 0–1–2–3–0 (two neighbours per state), energies E = (0, 1, 1, 2), and e^{β(0)} = 2, e^{β(1)} = 32, e^{β(2)} = 33, e^{β(k)} = k + 31 for k ≥ 3.
1. **The run.** Starting from γ(β(0)) = (4, 2, 2, 1)/9, the chain gives p_1 = (4064/6765, 4/33, 3/11, 12/2255), and the energies are E_p1 = 2737/6765, E_p2 = 17612741/50142180, E_γ(β(1)) = 2/33 and E_γ(β(2)) = 1/17. All energy hypotheses hold at step 1.
2. **The rate.** µ(1) = (E_p2 − E_p1)/(E_γ(β(2)) − E_p1) = 2673903/17337104 < 5/32.
3. **The spectrum.** The characteristic polynomial of P(β(2)) is X(X − 1)(X² − X + 289/2180) = X(X − 1)(X − 1/2 − s)(X − 1/2 + s) with s = √(64/545). So the sorted roots are 1, 1/2 + s, 1/2 − s, 0, and λ_2 = 1/2 + s < 27/32 because s < 11/32.
4. **The contradiction.** m = 5/32 satisfies m ≤ 1 − λ_2(P(β(2))), but µ(1) < m.

## Falsifier

The refutation would not hold if:
- the module's Glauber matrix, SA run or rate µ differed from Eqs. (30)–(32) and (46);
- its λ_2 were not the second largest eigenvalue counted with multiplicity;
- its premise m ≤ 1 − λ_2 were weaker than τ_rel ≤ τ^PS_rel;
- the instance violated a hypothesis of the source.

The module defines the Glauber matrix with the Gibbs-ratio form of Eq. (32) on an n-regular, symmetric, irreflexive neighbourhood. It runs the chain from the Gibbs state at β(0), and `energyRate` is Eq. (46). `lambda2` is the second entry of the descending sort of the roots of the characteristic polynomial, under the hypothesis that it splits over ℝ. By Proposition 2, τ^PS_rel = 1/m, and for 0 < m and λ_2 < 1, τ_rel ≤ 1/m is m ≤ 1 − λ_2. The instance has two neighbours per state, positive and strictly increasing β, and a strictly decreasing energy.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.lean` (374 lines).
- It defines `regularNeighborhood`, `gibbs`, `edgeWeight`, `glauber`, `isSARun`, `meanEnergy`, `energyRate`, `lambda2` and `claim`, and proves `result : ¬ claim`.
- Probability vectors are the frozen `D5.S3.TotalVariation.CycleSingleCutMinimax.Probability`. The probability of the run uses Mathlib's column-stochastic lemmas, and the roots use `Polynomial.roots_multiset_prod_X_sub_C`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation.lean.json`, statement `sha256:46eeaec0f3e23997c9ec18685a96b6fc2c661cb8f7c9d6a6866d7c1e63049a9d`.

Declaration statements:
- `result`: `sha256:2476260edd81f4e3d92de720a8dd8744af1b236de92f6f8dca1de8d0265ba21d`;
- `claim`: `sha256:4414665ec842d5d0376190c96de10b49c93dec560ad4818bca73de53f8d89100`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #17238 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the Gibbs and Glauber bridges, the run, the energies, the characteristic polynomial, the root certificate and the inequalities are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |

Every other public declaration is a definition used by a public statement. The module's 19 private theorems are bind-only helpers consumed on the proof path of `result`, and its 8 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** in the four-state Glauber run above, the relaxation time at the second step is shorter than that of a partial swap model with rate 5/32, yet the energy relaxation rate is smaller than 5/32.

**Computed, not formalized** (orchestrator, NumPy, 15 October 2026):
- In the eigenbasis of P(β(2)), the deviation p_1 − γ(β(2)) has energy contributions 0.347394 on the eigenvalue λ_2 = 0.842682, −0.001971 on 0.157318 and 0.000336 on 0. The contraction of its energy is 0.845770 > λ_2, so µ(1) = 0.154230 < 1 − λ_2 = 0.157318.
- At the first step the contributions are 0.410763, −0.012845 and 0.208142, and µ(0) = 0.432439 > 1 − λ_2(P(β(1))) = 0.157662.
- The paper's specific rate (56), µ^PS(k) = λ_2(Q)/(2N_max) e^{−β(k+1)ΔE_max}, is 0.5·33⁻² ≈ 0.000459 at step 1 here, and µ(1) ≥ µ^PS(1) holds for it.

**Argued, not formalized.**
- The mechanism: µ = 1 − E(P d)/E(d) for the deviation d from the new Gibbs state. A spectral gap bounds every eigenmode's decay, but the energy coefficients of a probability deviation can have opposite signs. When a faster mode carries negative energy weight, the energy contracts more slowly than the slowest mode, and µ drops below 1 − λ_2.

**Open.**
- Whether µ(k) ≥ µ^PS(k) holds for every Glauber run with the specific rate (56), which the paper uses for its bound.

**Effect on the paper.** Equation (50) fails in general, so the step from τ_rel(P) ≤ τ_rel(P^PS) to µ ≥ µ^PS needs another argument; the bound I(κ) ≤ I^PS(κ) with the rate (56) is not refuted by this instance.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal version was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
