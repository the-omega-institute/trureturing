---
slug: choudhary-goyal-konrad-ghosh-2013-temporal-hardy-spin-attainment
bibkey: choudhary2013temporalhardy
doi: null
url: https://arxiv.org/abs/1302.5296v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.result
---

# The temporal Hardy maximum 1/4 is attained with spin measurements for every spin

## Problem

S. K. Choudhary, S. K. Goyal, T. Konrad and S. Ghosh, *Persistence of Hardy's nonlocality in time*, arXiv:1302.5296v1, Appendix B:

> We conjecture that the maximum of the success probability appearing in the temporal version of Hardy's
> argument is $25\%$ for any spin-$s$ system.

The conclusion of the source states the same conjecture for spin measurements. The source proves that the success probability is at most 1/4 for every system and every projective measurement, and attains it with spin components for s = 1 and s = 3/2. The experiment and the four probabilities are quoted in [the literature note](../Library/QuantumContext/choudhary2013temporalhardy.md).

Issue [#19643](https://github.com/the-omega-institute/trureturing/issues/19643) fixes the reading. For every spin s = n/2 with n ≥ 1, some state and four spin-component observables u·S, with Lüders spectral projectors for chosen outcomes, satisfy the three zero conditions and have success probability 1/4. The conjecture is proved.

## Motivation

For spatial Hardy nonlocality, spin systems of higher dimension were found to behave more classically. The source shows that temporal Hardy nonlocality has the same maximum 1/4 in every dimension. With spin measurements it reached the maximum only for s ≤ 3/2. With the input restricted to spin eigenstates, the maximum is (1/2)^{4s} (arXiv:1007.2374), which decreases with s.

## Gap

The literature check before any Lean is recorded in #19643:
- arXiv:1302.5296 has only v1, and the 2016 review arXiv:1610.01152 repeats the conjecture;
- the restricted setting of arXiv:1007.2374 and the general bound of arXiv:1005.3421 do not settle attainability with spin components;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Fix n ≥ 1, s = n/2 and r = √(2^{1/n} − 1), so (1 + r²)ⁿ = 2. In the basis e_k = |s_z = s − k⟩ put b_k = √C(n,k) r^k, ψ = b − e₀ and χ = b/√2.
1. **Normalization.** ‖b‖² = (1 + r²)ⁿ = 2 and b₀ = 1, so ψ ⊥ e₀ and ‖ψ‖ = ‖χ‖ = 1, with χ = (ψ + e₀)/√2.
2. **Eigenvector.** For S = a Jz + c Jx with a = (1 − r²)/(1 + r²) and c = 2r/(1 + r²), a² + c² = 1. The ladder identities for the binomial coefficients give S b = (n/2) b.
3. **Simplicity.** The superdiagonal of S is strictly positive, so an n/2-eigenvector is determined by its first coordinate. Hence the n/2-spectral projector of S is Q = |χ⟩⟨χ|. The n/2-spectral projector of Jz is P = |e₀⟩⟨e₀|.
4. **Hardy conditions.** Take A₁ = B₂ = Jz and A₂ = B₁ = S, all outcomes n/2. Then Pψ = 0 and Qψ = (ψ + e₀)/2. So the three forbidden probabilities vanish, and the success probability is ‖P Q ψ‖² = 1/4.

## Falsifier

The proof would not settle the conjecture if the module's observables or probabilities differed from the source's. The module:
- uses spin components u·S = u₀Jx + u₁Jy + u₂Jz with real unit vectors u, built from the standard spin-n/2 matrices;
- characterizes the Lüders projector of an outcome a of an observable M as the self-adjoint idempotent whose fixed vectors are the a-eigenvectors of M;
- writes each probability as ⟨ψ|Π_X Π_Y Π_X|ψ⟩, with Π_{¬a} = I − Π_a, as in the source.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.lean` (443 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment.lean.json`, statement `sha256:b1037f1c5267141d8c768f58e599d09f9359a13f36324b2b3663910bef17e20b`.

Declaration statements:
- `result`: `sha256:59815daafec3b5cf2214ec65210f609b0780f762d52bbdd9858c5f83268f9b46`;
- `claim`: `sha256:2c5c596c3d6bd5ec941ecfb343c1e46a62f7672331120119e5f91c354019fdde`.

## Triage

Tier 1 conjecture of a 2013 paper, preregistered in issue #19643 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every spin s = n/2 with n ≥ 1, two spin components, Jz and a Jz + c Jx, with all outcomes +s, and the state ψ = b − e₀ satisfy the three Hardy zero conditions with success probability exactly 1/4.

**Computed, not formalized** (orchestrator, numpy, recorded in #19643): for n ∈ {1, …, 8, 10, 15, 20, 30} the construction gives rank-one spectral projectors, forbidden probabilities at most 8·10⁻³², and success probability within 1.1·10⁻¹⁵ of 1/4.

**Argued, not formalized.**
- *Mechanism.* The +s eigenvector of the rotated spin component is a spin-coherent state, and its components are binomial. Choosing the rotation angle so that its overlap with |s_z = s⟩ is exactly 1/√2 reproduces the qubit optimum inside the two-dimensional span of e₀ and χ.
- *Contrast.* Restricting the input to spin eigenstates (arXiv:1007.2374) gives at most (1/2)^{4s}. For s = 1/2 this is already 1/4, and indeed ψ = e₁ is a Jz eigenstate. For s ≥ 1 the restricted maximum is below 1/4, so the input ψ = b − e₀ that reaches 1/4 is not a spin eigenstate in that setting.
- *Scope.* Only two measurement directions in the x–z plane are needed for every s.

**Effect on the paper.** The maximum 1/4 of the temporal Hardy argument is attained by spin measurements for every spin, so the dimension independence of the bound extends to spin observables.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The 2016 review was not quoted. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
