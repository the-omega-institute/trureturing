---
slug: dive-koukoulekidis-mousafeiris-mintert-2020-three-coherence-ramsey-threshold
bibkey: dive2020multilevelcoherence
doi: 10.1103/PhysRevResearch.2.013220
url: https://arxiv.org/abs/1901.08599v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.result
---

# The exact three-coherence threshold of the Ramsey moment ratio R3

## Problem

B. Dive, N. Koukoulekidis, S. Mousafeiris and F. Mintert, *Characterisation of multi-level quantum coherence without ideal measurements* (Phys. Rev. Research 2, 013220 (2020); arXiv:1901.08599), certify k-coherence from the interference pattern p(t) = ⟨χ|e^{−iHt} ρ e^{iHt}|χ⟩ of a Ramsey-type experiment.
- The certifier is the moment ratio R3 = M3/M1², with M_q = (1/2π)∫₀^{2π} p(t)^q dt.
- R3 is convex in ρ.
- Its maximum over states that are not (k + 1)-coherent is a threshold: a measured R3 above it proves at least (k + 1)-coherence, whatever the Hamiltonian and the measurement vector χ.
- Table I gives the thresholds 1 (k = 1) and 5/4 (k = 2). For k = 3 it gives only the analytic upper bound 179/96 ≈ 1.86 and the numerical value 1.77, with the remark "In the cases where the exact threshold values are not known, we use numerical methods to approximate them".

The verbatim statements are in [the literature note](../Library/QuantumBounds/dive2020multilevelcoherence.md).

Issue [#18378](https://github.com/the-omega-institute/trureturing/issues/18378) fixes the reading. The k = 3 threshold is the maximum of R3 over:
- all finite dimensions;
- integer spectra;
- unit measurement vectors;
- finite mixtures of unit vectors with at most three nonzero amplitudes, with M1 > 0.

It is proved to equal N(α)/D(α) ≈ 1.7731757563.

## Motivation

The threshold decides when an interference experiment certifies four-coherence. The analytic bound 179/96 leaves the interval (1.7732, 1.8646] uncertified. The exact value certifies every measured R3 above it, with the same independence from the Hamiltonian and from imperfect measurements.

## Gap

Issue #18378 records the literature check before any Lean:
- arXiv v1–v3 keep the analytic bound and the numerical value;
- the citing works that follow the threshold still use 179/96 or 1.77;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Write N(r) = r⁶ + 30r⁴ + 90r² + 20, D(r) = (r + 2)²(r² + 2)² and P(r) = r⁷ − 13r⁶ + 6r⁵ − 60r⁴ + 30r³ − 30r² + 140r − 20.
1. **Mixtures.** By convexity of x³, R3 of a mixture is at most the weighted average of the R3 of its pure components with M1 > 0.
2. **Coefficients.** With z_j = χ̄_j ψ_j grouped by energy there are at most three coefficients, and Σ|z| ≤ 1 by Cauchy–Schwarz.
   - By orthogonality of the characters e^{ikt}, M1 = Σ|z_h|². M3 is the sum over pairs of ordered triples with equal total energy, so replacing z by |z| does not lower M3.
   - R3 is homogeneous of degree 2 in the coefficients, so it suffices to take a, b, c ≥ 0 with a + b + c = 1.
3. **Spacings.** For energies 0 < x < x + z, two of the ten cubic monomials can share a frequency only when x = z, x = 2z or z = 2x. Equal spacing gives the largest third moment, M3 = u³ + 6u(X² + Y²) + 6X²Y, with u = a² + b² + c², X = b(a + c) and Y = ac.
4. **Reduction.** At fixed b, R3 = (5/2)u − 3A + (3/2)(A² + 2B)/u + 3AB/u² is convex in u, with A = (1 − b)² + b² and B = b²(1 − b)². Its maximum is at u = A (two levels, R3 ≤ 5/4) or at a = c, where R3 = N(r)/D(r) with r = b/a.
5. **Certificate.** P changes sign on (6169/5000, 12339/10000), which gives a root α. With T = N(α)/D(α), the identity T·D(r) − N(r) = (r − α)²Q(r) with Q > 0 on r ≥ 0 shows that T is the maximum. It is attained at energies 0, 1, 2 by ψ = χ with populations (1, α, 1)/(α + 2).

## Falsifier

The theorem would not settle the table entry under any of these conditions:
- R3, the moments or the signal differed from Eqs. (1)–(3);
- the admissible states differed from Table I's set C_3;
- the threshold were meant over a different class of measurements.

The module takes:
- the signal |Σ_j χ̄_j e^{−i n_j t} ψ_j|² for integer labels n_j, which covers the source's commensurate spectra after a shift and rescaling, and its finite mixtures;
- unit measurement vectors χ, the rank-one projective measurement of the source;
- finite mixtures of unit vectors with at most three nonzero amplitudes, the states that are not four-coherent by the definition on page 1.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.lean` (768 lines).
- It defines `signal`, `mixedSignal`, `moment`, `ratio3`, `IsThreeSparse`, `IsUnitVector`, `admissibleValues`, the three threshold polynomials and `claim`, and proves `result : claim`.
- It reuses the finite squared-norm expansion `normSq_finite_sum` of `LidarRestrictedAnticoncentrationRefutation`, and Mathlib's interval integrals of complex exponentials, finite sums and convexity lemmas.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration of `result` is `Reg/D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.lean.json`, statement `sha256:b8494da955214930279abcb9540ad0db93cfde6428893b58e9a96e130f93dfcb`.

Declaration statements:
- `result`: `sha256:f7474a9993411ec426d7e8bd60906b577241b88aadac6c5c6860bcc2bfab351e`;
- `claim`: `sha256:a15afd4f4c32f9c60318c1e8018e5b124bcaa67eca9b457f5242f5208efea34d`.

## Triage

Tier 1 open entry of a 2019 paper (published 2020), preregistered in issue #18378 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the Fourier, mixture, spacing, convexity and certificate steps are instantiations of Mathlib lemmas (the intermediate value theorem, interval integrals of complex exponentials, Cauchy–Schwarz, finite Jensen, convexity of reciprocal powers and its endpoint theorem) and finite normalization | open-problem-resolution |
| the Fourier, mixture, spacing, convexity and certificate helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The module is a general theorem over all dimensions, spectra, measurements and mixtures, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`.** The k = 3 threshold of Table I is T = N(α)/D(α) = 1.7731757563…, with α ≈ 1.2338561142 the root of P in (6169/5000, 12339/10000). It is attained, so no smaller value certifies four-coherence.

**Computed, not formalized** (orchestrator, recorded in #18378):
- a numerical maximization over the three-level spacings (0, 1, 2), (0, 1, 3), (0, 2, 3), (0, 1, 5) and (0, 2, 5) gives 1.77317575629 for equal spacing and 1.25 for the others;
- random six-level pure states and measurements stay below T.

**Argued, not formalized.**
- *Mechanism.*
  - Mixtures and phases can only lower R3.
  - Among the frequency collisions, only equal spacing contributes the cross term 6ab²c(3a² + 2b² + 3c²), which dominates the others.
  - At fixed middle population the ratio is convex in u, which forces the symmetric populations (a, b, a) or a two-level state. The source's analytic bound 179/96 instead relaxes the attainable coefficient region, which is why it exceeds T.
- *Scope.* The source's Table I lists k ≤ 3. Thresholds for higher coherence numbers, and the rank-one POVM variants with noisy measurement (Sec. IV of the source), are not addressed; the method reduces them to finite polynomial optimizations of the same kind.

**Effect on the paper.** Every measured R3 in (1.7732, 1.8646], which the analytic bound left inconclusive, now certifies at least four-coherence. The numerical "best known" value 1.77 of Table I is the exact threshold rounded.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
