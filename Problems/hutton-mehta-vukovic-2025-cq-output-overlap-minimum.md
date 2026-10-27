---
slug: hutton-mehta-vukovic-2025-cq-output-overlap-minimum
bibkey: huttonmehtavukovic2025cqoverlap
doi: 10.48550/arXiv.2508.10664
url: https://arxiv.org/abs/2508.10664v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.result
---

# The minimum output overlap of orthogonal C–Q inputs

## Problem

Hutton, Mehta and Vukovic, *Deciding whether a C–Q channel preserves a bit is QCMA-complete*, arXiv:2508.10664v1, Conjecture 1.5, page 3, ask whether, for quantum states $\sigma_1,\ldots,\sigma_n\in M_d(\mathbb C)$ and $k\le n$ pairwise orthogonal pure states $u_1,\ldots,u_k\in\mathbb C^n$,

$$
\frac{1}{k(k-1)}\sum_{r\ne s}\operatorname{Tr}\!\left(\Bigl(\sum_i |(u_r)_i|^2\sigma_i\Bigr)\Bigl(\sum_j |(u_s)_j|^2\sigma_j\Bigr)\right)
\ge \min_{i_1,\ldots,i_k\text{ distinct}}\frac{1}{k(k-1)}\sum_{r\ne s}\operatorname{Tr}(\sigma_{i_r}\sigma_{i_s}).
$$

The denominator requires $2\le k$. A pure state is a unit vector, and a quantum state is positive semidefinite with trace one. Definition 1.3 specifies the channel on a pure input by $\Phi(|u\rangle\langle u|)=\sum_i|u_i|^2\sigma_i$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Arbitrary finite dimensions $n,d$ | Natural-number parameters of `claim` | All dimensions; empty impossible state/frame cases are retained |
| Arbitrary quantum states $\sigma_i$ | `IsState`: positive semidefinite and trace one | Literal conjunction; the proof converts it definitionally to the imported `CoPRelativeQuantumnessRefutation.IsDensity` |
| $k\le n$ orthogonal pure inputs | `k ≤ n`, `IsOrthonormalFamily u` | Coordinate inner products are the Kronecker delta, including unit norms |
| Defined average over unequal ordered pairs | `averageOutputOverlap` | Real reciprocal $1/(k(k-1))$, zero diagonal, real part of each trace |
| Minimum over $k$ distinct indices | `minDistinctOverlap` | Infimum over injective `Fin k → Fin n`; finite and nonempty under $k\le n$ |
| Lower bound | `result : claim` | Same inequality direction |
| Denominator defined | `2 ≤ k` | Makes the source normalization positive |

No source clause is dropped. The six public definitions retain the literal conventions of [#20116](https://github.com/the-omega-institute/trureturing/issues/20116).

## Motivation

The arbitrary-$k$ orthogonal lower bound is proposed after Theorem 1.4 as an extension of the two-input question. It compares an optimization over orthonormal frames with the finite set of computational basis choices. The source and its versioned locator are in [the Library note](../Library/Eigenstructure/huttonmehtavukovic2025cqoverlap.md).

The settling declaration is `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.result`. It has admission basis `open-problem-resolution (#20116; Proved)` and no digestion atom.

## Gap

The published conjecture requires a joint construction for all $k$ inputs. Separate pairwise bounds do not give one jointly realizable choice of $k$ distinct basis inputs. The squared maximal minors of the same input matrix provide that joint law.

## Route

Write $U_{ir}=(u_r)_i$, $U^*U=I$, and put $p_S=|\det U_S|^2$ on $k$-element row subsets. The imported `cauchyBinet` in `D5/S3/Quantum/Schatten/CompoundMatrices` gives the weighted determinant identity used by the private `HMV.weighted_cauchy`; `HMV.total_prob` and `HMV.pair_prob` derive normalization and two-point inclusion probabilities. Define

$$
A=\sum_{r\ne s}\operatorname{Tr}(\tau_r\tau_s),\quad
f(S)=\sum_{i\ne j\in S}\operatorname{Tr}(\sigma_i\sigma_j),\quad
T_{rs}=\sum_i\overline{U_{ir}}U_{is}\sigma_i.
$$

The private `HMV.subset_residual`, through `HMVResidual.residual_identity`, establishes

$$
A-\sum_Sp_Sf(S)=\sum_{r\ne s}\operatorname{Tr}(T_{rs}^*T_{rs}).
$$

The private `HMVResidual.cross_nonneg` applies Mathlib's positive-semidefinite trace nonnegativity to each product $T_{rs}^*T_{rs}$. `HMV.min_le_expected` bounds the minimum by this probability average. The proof of `result` combines these comparisons and divides by the positive real $k(k-1)$.

## Falsifier

A mismatch in the coordinate orthonormality hypothesis, ordered-pair convention, density predicate or minimum carrier would fail the statement correspondence. A counterexample to the residual identity for Hermitian matrices, to the subset probabilities for an isometric $U$, or to the claimed trace positivity would invalidate this route. The settling proof is universal and uses no numerical experiment as a premise.

## Evidence

The Lean module is `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.lean`; its sole public theorem is `D5.S3.Quantum.QuantumChannels.HuttonMehtaVukovicOutputOverlap.result`. The axiom closure of every public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$. Its state record is `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.lean.json`.

The four-slot escape audit for `result` is unfinished: [#21962](https://github.com/the-omega-institute/trureturing/issues/21962). No Reg mirror or validated registration is claimed. The missing evidence is the typed dependent-family source bridge, actual-positive law, rejected realization, whole-family sensitivity and observational dependence.

**Computed corroboration.** The experiment is [the immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d69f36f183a55265c3a9788695d47fad0ae307b7/docs/reports/hutton-mehta-vukovic-2025-cq-output-overlap-minimum), file `check.py`, SHA-256 `b3e116f56441b90137e7c356e5f8bc4267af1f9988be7f995770a5af7cf4eaa0`. Command: `python3 /Users/auric/.sshx/fbbf108be9866d1051e29b13/attempt-1/experiment-check.py`, using exactly those immutable bytes; exit 0. For 1800 random instances with $n\le6$, $2\le k\le n$, $d\le3$, it reports minimum $A-\min_Sf(S)=-1.776\times10^{-14}$, maximum normalization error $2.66\times10^{-15}$ and maximum residual error $6.75\times10^{-14}$. In 90 local-search runs the minimum gap is $-2.487\times10^{-14}$. These are floating-point readings over that finite tested scope, not exact inequalities or a uniform proof.

## Triage

Tier 1: an explicitly published conjecture in a recent paper, preregistered in #20116. Resolution: proved. All declarations are classified bind-only after expansion against frozen owners and pinned Mathlib; the external named settlement supplies the admission basis. `utility: none`: there is no finite numerical certificate, bounded enumeration or numerical-reduction claim in the Lean module.

### What the settlement shows

1. **Proved, kernel-checked:** `result` establishes Conjecture 1.5 for every $n,d$ and $2\le k\le n$ with the literal source conventions.
2. **Proved, kernel-checked proof step:** the local `hle` in `result`, using `HMV.subset_residual` and the nonnegative squared norms, establishes the stronger unnormalized real inequality $A\ge\mathbb E_p f$. It is a step of the settling proof, not an additional public theorem.
3. **Proved, kernel-checked:** the private `HMVResidual.residual_identity` and `HMV.subset_residual` assume arbitrary Hermitian matrices $\sigma_i$; positivity and trace one are not their hypotheses.
4. **Open as a separate statement; source inspection:** the final proof uses the state assumption only to extract Hermiticity through `IsDensity`. The normalized theorem for arbitrary Hermitian matrices is a follow-up candidate, without a separately compiled declaration here.
5. **Open boundary; statement comparison:** the result settles the arbitrary-$k$ orthogonal lower bound proposed after Theorem 1.4. It supplies no non-orthogonal correction extending Theorem 3.3. The paper's other results are not strengthened here beyond this orthogonal comparison.
6. **Open boundary:** equality/minimum-attainment characterizations and complexity consequences have not been separately formalized. The source's computational-complexity claims are not additional conclusions of `result`.
7. **Proved, kernel-checked clarification:** `HMV.expected_score` cancels the diagonal coefficient of the expected subset score because the two scalar products coincide when $i=j$. The residual identity retains its $i=j$ terms in the full double sum and handles them explicitly; their blanket deletion is not used.

The decisive mechanism is the probability law of squared minors of a common isometric matrix, together with the nonnegative Hilbert–Schmidt residual. The numerical corroboration is computed only in the finite scope stated in Evidence; extension of those computations is open and unnecessary for the universal kernel-checked result.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source and literature checks are attributed to the orchestrator in #20116: the source version is v1, the classical subset-law reference is Lyons, *Determinantal probability measures* (2003), equation (2.1) and Theorem 5.1, and the screened later works are 2510.04943v4, 2601.17497v2 and 2601.22471v3. Those readings do not prove exhaustive absence of another settlement. The correspondence to the paper is a source-fidelity argument; mathematical truth here is the exact compiled proposition. No claim about physical implementations, equality classification, complexity consequences or non-orthogonal inputs follows beyond the stated boundaries.
