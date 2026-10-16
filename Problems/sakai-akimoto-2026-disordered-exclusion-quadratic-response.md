---
slug: sakai-akimoto-2026-disordered-exclusion-quadratic-response
bibkey: sakaiakimoto2026currentresponse
doi: 10.1103/21vm-n8gp
url: https://arxiv.org/abs/2512.03316v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result
---

# A disordered exclusion ring whose ε² current response vanishes although neither symmetry condition holds

## Problem

I. Sakai and T. Akimoto, *Symmetry breaking of current response in disordered exclusion processes*, arXiv:2512.03316v2, Phys. Rev. E 113, 044123 (2026), study the stationary current J(ε) of an exclusion process on a ring of L sites with N particles.
- **Model.** A particle at site i hops to i + 1 at rate p_i(ε) = (1 + ε) w_{i,i+1}/2 and to i − 1 at rate q_i(ε) = (1 − ε) w_{i,i−1}/2, with ∏ w_{i,i−1}/w_{i,i+1} = 1 (Eq. (1)).
- **Condition (i).** The bond-bias ratio r_i(ε) = p_i(ε)/q_{i+1}(ε) does not depend on i (Eq. (5)).
- **Condition (ii).** There is a k such that, for every i, p_{k+i}(ε) = q_{k−i}(−ε) or p_{k+i}(ε) = q_{k−i+1}(−ε) (Appendix C).
- **The conjecture.** Either condition makes J odd in ε. The authors write (§III.D, p. 3): "We conjecture—and later confirm numerically— that an ε² contribution appears whenever neither condition (i) nor condition (ii) is satisfied."

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/sakaiakimoto2026currentresponse.md).

Issue [#17823](https://github.com/the-omega-institute/trureturing/issues/17823) fixes the reading:
- the ε² contribution is the coefficient c₂ of J(ε) = c₁ε + c₂ε² + o(ε²) under the unique stationary law;
- condition (ii) is read in its weakest per-site form;
- the claim is restricted to at least two particles and at least two holes, because the source (§III.F) already reports an exactly odd current for a single particle.

This restricted conjecture is refuted.

## Motivation

The conjecture describes when site disorder produces a quadratic, sign-dependent current response at small bias. The source treats the inversion-correspondence condition (ii) as a finely tuned, measure-zero case and still counts it as a mechanism for J₂ = 0. The conjecture thus asserts that these two symmetry mechanisms are the only ways for the ε² term to vanish.

## Gap

Issue #17823 records the literature check before any Lean:
- arXiv v1 (3 December 2025) and v2 (17 April 2026) both contain the conjecture;
- the arXiv full-text queries "bias-reversal symmetry" and "inversion-correspondence" return only the source;
- the one citing work (Takeishi–Akimoto, arXiv:2603.14164) treats stochastic resetting;
- the authors' later arXiv:2609.03560 concerns a boundary-driven open system. There it remarks that a reflection-asymmetric realization "may, in principle, exhibit cancellations among nonlinear current contributions", but it does not treat the ring conjecture;
- Zenodo, Crossref and the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Witness.** L = 4 and N = 2, with trap-model rates w_{i,i+1} = w_{i,i−1} = a_i, a = (2, 4, 3, 41).
   - The rates are positive and pairwise distinct, and they satisfy the equilibrium condition.
   - Condition (i) fails because the ratios a_i/a_{i+1} are not constant.
   - Condition (ii) fails because every reflection of the four-cycle moves some site onto a site with a different rate.
2. **Stationary law.** On the configurations 01, 02, 03, 12, 13, 23, put π(ε) = B(ε)/(5D(ε)), with D(ε) = 223175 + 17022ε² − 1628ε³ − 114725ε⁴ + 1628ε⁵ and B(ε) a vector of explicit quintic polynomials.
   - The generator annihilates B(ε) entrywise, and ΣB = 5D.
   - B(ε) and D(ε) are positive for |ε| < 1/100; for instance each quintic factor of B is at least 2825 − 14887/100.
3. **Uniqueness.** Every stationary law μ satisfies 5D(ε)μ_j − B_j(ε)Σμ = Σ_i c_{ji}(ε)(Mμ)_i with explicit polynomial coefficients, from the adjugate of the generator with one row replaced by ones. Hence μ = π(ε).
4. **Current.** J(ε) = 7872ε(25 + 9ε² − 16ε⁴)/D(ε). Since D′(0) = 0, J(ε) − (7872/8927)ε = ε³g(ε) with g continuous at 0, so c₁ = 7872/8927 and c₂ = 0.

## Falsifier

The refutation would not settle the conjecture if:
- the module's dynamics, stationary law or current differed from Eqs. (1), (2) and (C1);
- its conditions were stronger than (i) and (ii), so that their failure were easier;
- its witness had fewer than two particles or holes, or failed the equilibrium condition.

The module defines:
- the hop rates of the exclusion ring;
- stationary laws by support on N-particle configurations, nonnegativity, normalization and global balance;
- the current across bond (0, 1).

Condition (i) is required for every −1 < ε < 1. Condition (ii) is the per-site disjunction, each alternative holding for all ε. The claim quantifies over the locally unique stationary family and every expansion c₁ε + c₂ε² + o(ε²).

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.lean` (384 lines).
- It defines `p`, `q`, `rate`, `IsStationary`, `current`, `BondRatioUniform`, `InversionCorrespondence` and `claim`, and proves `result : ¬ claim`.
- It imports only Mathlib.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.lean.json`, statement `sha256:35cc805e668392c226b5ad0da975555f14869c8d83e372ec46a4469516384afa`.

Declaration statements:
- `result`: `sha256:abc4d6cb7ec347f2ca38a501f079212a0207edb65c9ae0bdfb0a8146d02ec86d`;
- `claim`: `sha256:9091d97b25bc5bc60a58a6ef1f1bf866be66e0bf3c4bf95d4af090131b2a5cd3`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #17823 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the stationarity, uniqueness and current identities are polynomial identities closed by `ring` and `linear_combination`, and the expansion uses pinned Mathlib asymptotics | open-problem-resolution |
| the witness, certificate and expansion helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** for L = 4, N = 2 and trap rates (2, 4, 3, 41), neither condition (i) nor (ii) holds, yet the ε² coefficient of the stationary current is 0.

**Computed, not formalized** (orchestrator, exact rational arithmetic, recorded in #17823):
- at the witness, J₃ = 498462912/1992283225 and J₄ = 12815616/1992283225 ≠ 0, so J is not odd: bias-reversal symmetry is still broken, and only its ε² term vanishes;
- a = (2, 4, 3, 40) and (2, 4, 3, 42) give J₂ of opposite signs, so a passes through a zero of J₂ between them;
- a = (1, 2, 3, 4) gives J₂ = 576/129605;
- a = (1, 1, 1, 2), which satisfies (ii), gives J₂ = 0;
- N = 1 gives J₂ = 0.

**Argued, not formalized.**
- *Mechanism.* For fixed L and N, J₂ is a rational function of the rates. Conditions (i) and (ii) describe symmetric families on which it vanishes identically. Its zero set is a hypersurface, and the sign change between a₄ = 40 and a₄ = 42 shows that this hypersurface meets the region where neither condition holds. Away from both symmetries, J₂ can thus vanish by cancellation alone.
- *What survives.* Since J₂ is not identically zero for L = 4 and N = 2 (a = (1, 2, 3, 4)), it is nonzero off a measure-zero set of rates. So for continuously distributed disorder, such as the source's exponential trap energies, an ε² contribution appears almost surely in this case. The conjecture holds in this almost-sure form for (L, N) = (4, 2), but not in its stated form.

**Open.**
- Whether J₂ is not identically zero for every L and 2 ≤ N ≤ L − 2 with nonuniform trap rates, which would give the almost-sure form in general.
- A characterization of the zero set of J₂.

**Effect on the paper.** Conditions (i) and (ii) are sufficient for a vanishing ε² response but not necessary. The numerical confirmations of the source concern random landscapes and are consistent with the almost-sure form.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
