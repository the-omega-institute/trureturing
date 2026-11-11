---
slug: quaternionic-deutsch
bibkey: krishna2026quaternionicdeutsch
doi: 10.48550/arXiv.2610.35881
url: https://arxiv.org/abs/2610.35881v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/QuaternionicDeutschEquality.result
---

# Lower and simultaneous quaternionic Deutsch equality

## Problem

K. Mahesh Krishna, *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle*, arXiv:2610.35881v1, Question 2.12, printed page 12:

> Let $(\Omega,\mu)$, $(\Delta,\nu)$ be measure spaces, $\mathcal Q$ be a quaternionic Hilbert space. For which pairs of 1-bounded continuous Parseval frames $\{\tau_\alpha\}_{\alpha\in\Omega}$ and $\{\omega_\beta\}_{\beta\in\Delta}$ for $\mathcal Q$, we have equality in Inequality (11)?

The answer specified by [#23061](https://github.com/the-omega-institute/trureturing/issues/23061) classifies equality at the lower Deutsch endpoint and simultaneous equality on the source's unchanged entropy domain. It does not classify equality at the upper link alone. Write
$u=x/\|x\|$, $p_\alpha=|\langle\tau_\alpha,u\rangle|^2$,
$q_\beta=|\langle\omega_\beta,u\rangle|^2$ and
$c=\sup_{\alpha,\beta}|\langle\tau_\alpha,\omega_\beta\rangle|$.
For every nonzero $x$ whose coefficients are nonzero at every index of both frames,

$$S_\tau(x)+S_\omega(x)=-2\log((1+c)/2)
\quad\Longleftrightarrow\quad
\dim_{\mathbb H}\mathcal Q=1,\quad
\|\tau_\alpha\|=1\ \mu\text{-a.e.},\quad
\|\omega_\beta\|=1\ \nu\text{-a.e.}.$$

Lower equality implies $\mu(\Omega)=\nu(\Delta)=c=1$ and $S_\tau(x)=S_\omega(x)=0$.
An admissible nonzero equality state exists exactly when this rigidity holds and every frame vector is nonzero, including vectors at null indices. An explicit equality model exists at arbitrary carrier and index universes.

### Statement echo

| Source clause or explicit answer clause | Lean counterpart | Scope |
| --- | --- | --- |
| Right quaternionic Hilbert space, Definition 1.9 | `RightHilbert`, opposite quaternion module, normed additive group, `CompleteSpace` | All seven inner-product fields; completeness remains a separate hypothesis |
| Arbitrary measure spaces | The two carriers, measurable-space instances and measures in `claim` | No finite-mass, separability or sigma-finiteness hypothesis |
| Continuous Parseval frames, Definition 2.7 | `ContinuousParseval` for both families | Measurability and Parseval for every vector |
| Pointwise 1-boundedness, Definition 2.8 | `OneBounded` | Every index, including null indices |
| Source entropy domain and right division | `EntropyDomain`, `unitVector`, `density`, `entropy` | Nonzero state and every coefficient nonzero; extended nonnegative integrals retain infinity |
| Equation (11)'s actual supremum and lower endpoint | `overlap`, `deutschEndpoint`, `lowerEquality` | Actual pointwise supremum, not an essential supremum |
| Proposed equality classification | `rigid` and the first universal clause of `claim` | Quaternionic module rank one and almost-everywhere unit norms |
| Simultaneous equality | `simultaneousEquality` and the implication in `claim` | Both masses and overlap one; both entropies zero |
| Which frame pairs admit equality | The existential equivalence in `claim` | Every-index nonzero frame vectors are necessary and sufficient together with rigidity |
| Nonvacuity of the answer | `equalityModelExists` conjunct of `claim` | Conclusion supplied by a singleton Dirac model, not an extra assumption |

The answer predicates and nonvacuity clause specify the proposed solution to the source's question. They are not additional premises. All definitions retain the literal conventions in #23061. `result` is universally quantified over the source spaces, measures and frames.

## Motivation

Equation (11) connects the sum of continuous Shannon entropies to the Deutsch endpoint. This answer identifies when its lower endpoint can be attained without discarding the source's representative-sensitive, every-index entropy domain. In particular, a zero vector at a null index changes admissibility despite leaving the Parseval integrals unchanged.

## Gap

The literature screen recorded in #23061 locates no explicit source-faithful quaternionic continuous-frame equality classification in its searched scope. Source definitions and quaternionic Buzano are literature-attested; the explicit classification is suspected-novel. Completeness of the literature screen is **ASSUMED-UNVERIFIED**.

The screen includes the earlier Zenodo text; the author's real/complex continuous predecessor, Functional Deutsch and continuous operator-valued inequalities; finite complex MU equality theory (Abdelkhalek et al., arXiv:1509.00398v1, Theorem IV.1); and Rumin, arXiv:1109.5889v2, Theorem 1.1 and its equality discussion. Existing stronger finite-measure uncertainty inequalities are not claimed as new. A complete quaternionic POVM specialization of Rumin is not verified. OpenAlex and Semantic Scholar citing-work enumeration were rate-limited in the recorded screen; unenumerated citing works and unlocated journal versions remain outside its completeness claim.

## Route

Quaternionic Buzano bounds each product $p_\alpha q_\beta$ by $M=((1+c)/2)^2$. For actual bounded suprema $A=\sup p$ and $B=\sup q$, entropy splits into $-\log A$ or $-\log B$ and a nonnegative remainder integral. Lower equality forces $AB=M$ and both remainders to vanish, hence $p=A$ and $q=B$ almost everywhere. This is `Saturation.pair_saturation` in the owning namespace.

Frame saturation gives unit frame norms and cross modulus $c$ on the corresponding full-measure sets. Parseval at these frame vectors gives $A=B=c^2$. Consequently $c^4=((1+c)/2)^2$ with $0\le c\le1$, so $(2c+1)(c-1)=0$ and $c=1$. The orthogonal residual of any vector has zero frame coefficients almost everywhere; Parseval makes it zero. This is the rank-one conclusion of `lower_to_rigid`.

Conversely, `rigid_to_simultaneous` uses rank one and almost-everywhere unit norms to give total masses and overlap one and both entropies zero. `rank_one_domain` handles every nonzero state when every frame vector is nonzero. `result` combines these implications and `equality_model`.

## Falsifier

A counterexample to `claim` would need the stated quaternionic inner-product laws, both measurable Parseval families, pointwise norm bounds and the literal every-index admissibility conditions. A zero coefficient admitted by a $0\log0$ convention changes the domain and does not refute this statement. Infinite entropy is retained as infinity and is not converted into a real value. No finite total mass or product-measure assumption is used to make the lower-to-rigid argument valid.

## Evidence

The owning module is [QuaternionicDeutschEquality.lean](../D5/S3/QuantumBounds/QuaternionicDeutschEquality.lean), under namespace `D5.S3.QuantumBounds.QuaternionicDeutschEquality`. Its generality is G and utility is none. Its sole public theorem is `result : claim`; the supporting statements named here are private declarations of that module. The [Blueprint](../Blueprint/D5/S3/QuantumBounds/QuaternionicDeutschEquality.md) displays all public definition bodies and the complete settling proposition. The [source note](../Library/Entropy/krishna2026quaternionicdeutsch.md) identifies the paper and verified locator.

The separate escape audit is unfinished for `D5.S3.QuantumBounds.QuaternionicDeutschEquality.result`: [#27109](https://github.com/the-omega-institute/trureturing/issues/27109). A source-faithful four-slot registration for the existential model together with the dependent universal classification requires a dependent arena/source bridge and actual-positive, sensitivity and observational-dependence witnesses. No `declared_validated` registration is asserted.

### Exact experiment

The program and data belong to [trureturing-experiments, immutable revision `ee464371360886227b2553316b0e2a1e84eec35d`](https://github.com/the-omega-institute/trureturing-experiments/tree/ee464371360886227b2553316b0e2a1e84eec35d/docs/reports/quaternionic-deutsch-equality/). The referenced file is `docs/reports/quaternionic-deutsch-equality/check.py`; its SHA-256 is `6b1e5cc58e781edfd3136800ac3d61e208f5f03d9a0d8d6fc2f80a528453a86d`. The immutable file is present in the experiments clone and was extracted for the command `python3 /Users/auric/.op-scratch/op/krishna35881/stageb/check.py`, exit 0.

The exact tested scope is 1,197 generated quaternionic Buzano triples in dimensions 1–3; eight generated frames in each dimension; and 5,376 admissible frame-pair/state cases (256 in dimension one, 1,024 in dimension two and 4,096 in dimension three). There are 64 lower equalities, all in dimension one. The null-index checks distinguish zero and nonzero subunit null-index vectors. The scalar factor has roots $1$ and $-1/2$. These are finite computations, not the proof of the uniform classification.

## Triage

| Item | Status and evidence kind | Evidence |
| --- | --- | --- |
| Lower equality, rigidity and simultaneous equality on the unchanged source-admissible domain | Proved; kernel-checked | `result` |
| Pair existence depends on every-index nonzero frame vectors, including null indices; under rigidity and those nonzero conditions every nonzero state is admissible and has equality | Proved; kernel-checked | `rank_one_domain`, `result`; rigidity alone does not exclude a zero null-index vector |
| The ULift quaternionic line with singleton Dirac index spaces is nonvacuous at arbitrary universes | Proved; kernel-checked | `equality_model`, consumed by `result` |
| Lower-to-rigid needs no completeness hypothesis; the binding claim preserves `CompleteSpace` | Proved; kernel-checked | Exact telescope of `lower_to_rigid`; `claim` retains completeness |
| Actual bounded suprema suffice for entropy saturation, without a product-measure sigma-finiteness step | Proved; kernel-checked | `Saturation.pair_saturation`, consumed by `lower_to_rigid` |
| 1,197 Buzano triples, 5,376 frame-pair/state cases, 64 lower equalities in dimension one, null-index and scalar-root checks | Computed | Exact experiment above; exit 0, immutable program identity and tested range specified |
| Structural classification of upper-link equality alone | Open | Outside `claim`; no such classification is asserted |
| Enlarged domain permitting zero coefficients with $0\log0$ | Open | No transfer of the present rigidity theorem; identical orthonormal bases with basis states illustrate the changed domain |
| Full quaternionic POVM comparison with Rumin | Open | The operator-measure construction and complete specialization are not verified |

### What the settlement shows

**Proved in this module:** the decisive mechanism is saturation of the entropy remainder followed by Parseval on saturated frame vectors and an orthogonal residual. The exact statement of `lower_to_rigid` does not require completeness; the complete-space formulation of `claim` is preserved. Measures need not be finite in the hypotheses: simultaneous equality forces both total masses to be one. Under rigidity, everywhere nonzero frame vectors are precisely the remaining pair-existence obstruction; the singleton model proves that the classification has actual realizations.

**Computed:** the finite experiment agrees with the classification on its stated dimensions and generated families. It supplies no uniform extension beyond that range.

**Open:** upper-link equality alone, the $0\log0$ extension and the full Rumin comparison remain separate. The source's quaternionic Kraus and Crouzeix questions are not consequences of this classification. The uncertainty inequalities themselves retain their original statements; the result adds their lower and simultaneous equality cases on the specified domain.

## ASSUMED-UNVERIFIED

Literature completeness and the absence of a settlement outside the recorded search scope are unverified. The proposed quaternionic POVM specialization of Rumin is unverified. The escape audit in #27109 is unfinished and distinct from the Lean proof of `claim`. No model-diversity claim follows from the codex-cli verification carriers.
