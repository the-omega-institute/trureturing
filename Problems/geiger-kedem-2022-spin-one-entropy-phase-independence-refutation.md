---
slug: geiger-kedem-2022-spin-one-entropy-phase-independence-refutation
bibkey: geigerkedem2022spinentropy
doi: 10.3390/e24091292
url: https://arxiv.org/abs/2111.11605v3
triage: theorem
motivation_gids:
  - D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.result
---

# The Geiger–Kedem spin-1 spin-entropy depends on the relative phases

## Problem

D. Geiger and Z. M. Kedem, *Spin Entropy*, Entropy 24, 1292 (2022), arXiv:2111.11605v3, define the spin-entropy of a pure spin state as the Shannon entropy of the S_z probabilities plus the differential entropy of the polarization-angle density (Eq. (4)).
- **Spin 1.** For the state (15), with amplitudes sin θ_α cos θ_β e^{iφ_x}, cos θ_α and sin θ_α sin θ_β e^{iφ_z}, Proposition 2 gives the spin-entropy (17). Its density is ρ_1(φ) = (1/2π)|sin θ_α cos θ_β e^{i(φ_x+2φ)} + cos θ_α e^{iφ} + sin θ_α sin θ_β e^{i(φ_z−2φ)}|².
- **The conjecture.** "Conjecture 1. The spin-entropy depends only on the variables that define the spin-entropy component along the z axis. In particular, the spin-entropy (17) of a state given by (15) can be simplified to" its zero-phase form (18).

The verbatim statements are in [the literature note](../Library/Entropy/geigerkedem2022spinentropy.md).

Issue [#17162](https://github.com/the-omega-institute/trureturing/issues/17162) fixes the reading: for all θ_α, θ_β ∈ [0, π/2] and φ_x, φ_z ∈ [0, 2π), Eq. (17) equals its value at φ_x = φ_z = 0. The conjecture is refuted.

## Motivation

The conjecture underlies the source's Figure 2, which plots Eq. (18) against (θ_α, θ_β), and its further conjecture (§II) that the ordering of states by spin-entropy is determined by the z-axis component alone. If the phases matter, the spin-entropy of a spin-1 state is not a function of its S_z probabilities.

## Gap

Issue #17162 records the literature check before any Lean:
- arXiv v1–v3, with v3 stating Conjecture 1;
- the authors' later paper, *Phase Space Spin-Entropy* (Entropy 26, 372 (2024)), read in full text, replaces the decomposition with an entropy on the sphere and does not evaluate the 2022 statement;
- a web search;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Take (a, b, c) = (3, 1, 1)/√11, that is θ_α = arctan √10 and θ_β = arctan(1/3), with φ_x = 0 and φ_z = 0 or π.
1. **The densities.** At these angles the source density is |P_s(e^{it})|²/(22π) with P_s(z) = 3 + z + s z⁴ and s = 1 (φ_z = 0) or s = −1 (φ_z = π).
2. **Cauchy coefficients.** On the closed unit disc, Re P_s ≥ 1, so P_s log P_s is holomorphic there. For f holomorphic on the closed disc, the circle average of conj(P_s) · f equals 3f(0) + f′(0) + s f⁽⁴⁾(0)/24, by the Cauchy formula for derivatives.
3. **The moments.** Taking f = P_s gives mass 10 + s². Taking f = P_s log P_s, with its derivatives at 0 up to order 4, gives the logarithmic moment (20 + 2s²) log 3 + 2(1 + s²) + s/162.
4. **The gap.** Normalizing, the differential entropies at s = −1 and s = 1 differ by 1/891, while the Shannon terms coincide. So the spin-entropy at φ_z = π exceeds that at φ_z = 0 by 1/891.

## Falsifier

The refutation would not hold if:
- the module's density differed from ρ_1 of Proposition 2;
- its entropy differed from Eq. (17);
- the integral were the totalized value of a non-integrable function;
- the witness lay outside the source's parameter ranges.

The module writes ρ_1 with the source's frequencies +2, +1, −2 and phases, and Eq. (17) with the interval integral over [0, 2π] and the two Shannon terms. The integrand is continuous for every parameter, and the witness angles lie in [0, π/2] with phases 0 and π in [0, 2π).

## Evidence

The canonical source is `D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.lean` (464 lines).
- It defines `density`, `spinEntropy` and `claim`, and proves `result : ¬ claim`. The Shannon terms S_c of Eq. (17) are Mathlib's `Real.binEntropy`.
- It uses pinned Mathlib only: `Real.binEntropy` with `Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub`, `Real.circleAverage`, the Cauchy formula for derivatives (`DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`), `Complex.log` on the slit plane, `Real.continuous_mul_log`, and the arctangent identities.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation.lean.json`, statement `sha256:2b37517cca1ed8d08b9c8da310555a0da9c93bf77218f53748edb93d023923bb`.

Declaration statements:
- `result`: `sha256:d88d1cabde4b67e4fc80a9264e8c2204bae6c65a1faaa811152e6729bf5d5698`;
- `claim`: `sha256:a6ab07e58bb12b7c19617e49b2d34e67be53d75c5c16d09c38b6f72f226e3d41`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #17162 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the density identification, the Cauchy coefficient extraction, the derivative values and the normalization are instantiations of pinned Mathlib results followed by normalization | open-problem-resolution |

Every other public declaration is a definition used by a public statement. The module's 21 private theorems are bind-only helpers consumed on the proof path of `result`, and its 5 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** at θ_α = arctan √10, θ_β = arctan(1/3) and φ_x = 0, the spin-entropy (17) at φ_z = π exceeds its value at φ_z = 0 by 1/891, so it is not a function of θ_α and θ_β alone.

**Computed, not formalized** (orchestrator, mpmath at 40 digits, 15 October 2026):
- S_1(φ_z = 0) = 2.27451630416694… and S_1(φ_z = π) = 2.27563863862261…, whose difference agrees with 1/891 to 40 digits.
- The closed form ln a² + 2(b² + c²) + (b⁴c/(6a³)) cos δ for (1/2π)∫|F_δ|² ln|F_δ|² matches the integral at δ ∈ {0, 0.7, π}.

**Argued, not formalized.**
- The same expansion shows that the spin-entropy depends on the relative phase δ through the term (b⁴c/(6a³)) cos δ, for every a > b + c with b, c > 0. So the failure is not confined to one point of the parameter space.
- The mechanism: the mass of |F_δ|² is a² + b² + c² for every δ, but its logarithmic moment is not phase-free. The phase enters through the coefficients of z³ and z⁴ in log F_δ, which pair with the cross terms bc e^{iδ}z³ and ac e^{iδ}z⁴ of |F_δ|². Their contributions are b⁴c e^{−iδ}/(3a³) and −b⁴c e^{−iδ}/(4a³), which do not cancel.

**Open.** Whether the source's second conjecture (§II), that the ordering of states by spin-entropy is determined by the z-axis component alone, also fails for spin 1.

**Effect on the paper.** Eq. (18) is not equal to the spin-entropy (17) in general, and Figure 2 displays only the zero-phase slice.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
