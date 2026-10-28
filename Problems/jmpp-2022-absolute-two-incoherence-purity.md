---
slug: jmpp-2022-absolute-two-incoherence-purity
bibkey: johnstonmoeinpereiraplosker2022incoherence
doi: 10.1103/PhysRevA.106.052417
url: https://arxiv.org/abs/2205.05110v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result
---

# Absolute two-incoherence beyond the purity bound

## Problem

Johnston, Moein, Pereira and Plosker, *Absolutely k-incoherent quantum states and spectral inequalities for factor width of a matrix*, Phys. Rev. A 106, 052417, arXiv:2205.05110v2, Section 5, printed page 17:

> Theorem 7 gives a sufficient condition for absolute 2-incoherence that is also necessary in dimension n = 3. It is unclear whether or not it is necessary in dimension n = 4 or higher.

The condition is $\operatorname{Tr}(\rho^2)\le1/(n-1)$. The universal necessity assertion for all $n\ge4$ is refuted by one density matrix in dimension five. The source and literal definitions are in [the Library note](../Library/Eigenstructure/johnstonmoeinpereiraplosker2022incoherence.md); the external question is preregistered in [#17863](https://github.com/the-omega-institute/trureturing/issues/17863).

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| A vector has at most $k$ nonzero entries | `FactorWidthTwoCone.IsKSparse` | The finite support-cardinality expression. |
| A finite sum $\sum_jv_jv_j^*$ of such vectors | `FactorWidthTwoCone.IsKIncoherentSum` | Every summand has the required support; individual vectors need not be normalized. |
| A mixed quantum state | `GHZMeasureBiseparableBound.IsDensity` | Positive semidefinite matrix with complex trace one. |
| Every unitary conjugate is $k$-incoherent | `AbsoluteTwoIncoherencePurityRefutation.IsAbsolutelyKIncoherent` | All complex unitary matrices are quantified. |
| Necessity for dimension four or higher | `AbsoluteTwoIncoherencePurityRefutation.claim` | Every natural $n\ge4$, every density matrix satisfying absolute two-incoherence. |
| The eigenvalue purity bound | Real part of the trace of the square | For Hermitian matrices, the spectral theorem identifies this with the sum of squared eigenvalues. |
| Refutation | `AbsoluteTwoIncoherencePurityRefutation.result` | Exact negation of `claim`, witnessed at $n=5$. |

`FactorWidthTwoCone.IsLocally2` is the Hermitian support-two quadratic-form condition in Definition 1(b). It is an auxiliary dual-cone predicate, not an extra hypothesis in `claim` or `result`.

## Motivation

The purity ball in Theorem 7 is sufficient for absolute two-incoherence. Its boundary need not be the full boundary of that set. The settlement identifies a state outside the ball whose entire unitary orbit remains in the factor-width-two cone.

## Gap

The missing necessity fails because the orbit of a particular trace-one, unit-Frobenius-norm Hermitian matrix is separated from the trace-one locally two-positive matrices. The separation leaves room for an affine perturbation beyond the purity threshold. The assertion here concerns the source's universal necessity question; neither necessity at $n=4$ nor a uniform formal family over all $n\ge5$ is settled.

## Route

Put $r=\sqrt6$, $a=(1+r)/5$, $b=(1-2r/3)/5$, and

$$
B=\operatorname{diag}(a,a,b,b,b),\qquad
\rho_t=\frac{1+t}{4}(I-B)-\frac t5I.
$$

The settling proof uses $t=10^{-18}$. The private lemmas `rho_density` and `rho_purity` establish density and

$$
\operatorname{Tr}(\rho_t^2)=\frac15+\frac{(1+t)^2}{20}.
$$

For $t>0$ this is strictly greater than $1/4$. With $\varepsilon=10^{-8}$, `gap_n5` proves a uniform trace-pairing gap $\varepsilon^2/2$ against every trace-one locally two-positive matrix and every unitary conjugate of $B$.

A hypothetical smaller gap forces a squared-modulus Gram matrix $H$ of rank at most four close to the full-rank equal-overlap matrix with off-diagonal entry $3/8$. `H_distance_lower` gives squared Frobenius distance at least $25/64$, whereas `H_distance_upper` gives at most $10^{-6}$. Their contradiction proves the gap. `FactorWidthTwoCone.fw2_duality`, whose proof uses compactness of finite support decompositions, then converts the nonnegative dual pairings into sparse outer-product sums for every unitary conjugate of $\rho_t$.

## Falsifier

The exact result would fail if the displayed state had a unitary conjugate outside the factor-width-two cone or did not exceed purity $1/4$. The kernel checks both required properties through `witness_absolute`, `rho_purity`, and their use in `result`. Numerical optimization supplies no premise of these proofs.

## Evidence

The settling GID is `D5/S3/Quantum/Measurement/AbsoluteTwoIncoherencePurityRefutation.result`, with `admission_basis: open-problem-resolution (#17863; Refuted)`. The supporting module is `D5/S3/Quantum/Measurement/FactorWidthTwoCone`, with `admission_basis: escape-witness` supplied by `block_closed` on the proof path to `fw2_duality`. Existing owner statements are reused at their original declarations in `IncoherentCone` and `AntidistinguishabilityOverlapNonTight`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The six supporting public theorems and eight published owner theorems have an unfinished four-slot escape audit in [#18980](https://github.com/the-omega-institute/trureturing/issues/18980). No validated registration is claimed without compiled registration evidence and its required-CI reading.

### Experiment

[Numerical checker and results, pinned to `cb4521985393e13d9517583014c2d21a6e82873f`](https://github.com/the-omega-institute/trureturing-experiments/tree/cb4521985393e13d9517583014c2d21a6e82873f/docs/reports/johnston-moein-pereira-plosker-2022-absolute-2-incoherence).

The checked program is `check.py`, SHA-256 `5cd6f44dd762913ea53d6073e94f2571525a6cf0a2bbe04cb6d36293dce7588a`. The executed command is `/Users/auric/.sshx/6f7f08e6d50b6f8f47ab13e8/attempt-1/experiment-venv/bin/python -u /tmp/op-jmpp/check.py`; its input is exactly the linked commit's `check.py`, and its exit code is 0 (`ALL_OK`). The environment has NumPy 2.5.4, CVXPY 1.9.3 and Clarabel 0.11.1, with seed 20261017.

| Tested scope | Computed result |
| --- | --- |
| Spectral identities and purity, $n=5,6,7,8$, $t=1/(100000n^4)$ | The identities and purity formula agree within the program's tolerances; every tested state is positive definite and exceeds the threshold. The excess at $n=5$ is $1.600\cdot10^{-9}$. |
| Dual gap, $n=5,6$, 40 random unitaries and four 250-step local searches per dimension | Largest values found: 0.988699 and 0.982928; corresponding gaps: 0.011301 and 0.017072. |
| Primal decompositions, $n=5$, $t=10^{-3}$, 30 random unitaries and one search-selected unitary | Purity 0.250100; minimum decomposition slack $1.314\cdot10^{-2}$. |
| Dimension-four control, 40 random unitaries and three 200-step local searches | Largest value found 0.999777; gap $2.23\cdot10^{-4}$. |
| Pure-state control, five sampled unitaries | Minimum slack $-2.644$. |
| Mixed-state control of purity 0.208, ten sampled unitaries | Minimum slack 0.6224. |

Numerical optimization is finite sampling and local search, not a universal orbit certificate. The solver emits a possible-inaccuracy warning; the displayed optimization readings are approximate. They do not certify necessity or non-necessity at $n=4$, an optimal gap, or an all-dimension family. The exact formal witness uses $t=10^{-18}$, independently of this experiment.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| The mathematical settlement | **Kernel-checked:** `AbsoluteTwoIncoherencePurityRefutation.result` refutes universal necessity at $n=5$; it has no extra premise. |
| Failure mechanism | **Kernel-checked:** `gap_n5`, `H_distance_lower`, and `H_distance_upper` exclude near saturation using the rank-four obstruction in dimension five. |
| Counterexample properties | **Kernel-checked:** `witness_absolute` establishes absolute two-incoherence; `rho_purity` establishes the exact purity expression used by `result` to exceed $1/4$. |
| Nearest surviving statements | **Literature reading:** Theorem 7 retains its sufficient condition and its stated converse for $n\le3$. Necessity in dimension four remains **open** here. |
| Other source results | **Literature reading:** Section 5 asks for the converse; Theorem 7 does not assume that converse. The refutation changes no premise of that sufficient-condition theorem. |
| Uniform dimensions | **Open:** a formal family for every $n\ge5$ and a sharp perturbation threshold are not asserted. |
| Literature status | **Literature reading, completeness ASSUMED-UNVERIFIED:** the inspected sources in #17863 contain no settlement; related real-symmetric spectral results do not supply the complex Hermitian conclusion. Unpublished frame overlap remains unverified. |
| Integration and owners | **Kernel-checked:** two modules under `D5/S3/Quantum/Measurement`, with the original frozen owners' five and three helper statements published and reused; one Scribe per selected owner and new module. |
| Lean environment and resources | Current scoped build and direct compiler measurements use the pinned Lake environment; exact delivered-head resource readings are in the PR verification. No claim is based on a cold whole-project build or an unmeasured successful scratch run. |
| Reuse | **Search reading:** name, defining-expression and conclusion-shape searches cover the merged dev revision, private owners and pinned Mathlib. The compactness construction remains the supporting escape witness; direct owner applications supply the existing normalization facts. No exhaustive theorem-absence claim follows from bounded search. |
| Search and scratch boundaries | **Open:** unrestricted exact-search initialization and unmeasured scratch-process costs supply no successful resource-compliance evidence. Bounded search failures supply no proof of theorem absence. The delivered compiler readings determine the resource claim for these modules. |
| Anonymous fidelity checks | **Kernel-checked:** literal source conventions and their consumed spectral/purity identities occur in the delivered proof. Transient anonymous checks are not retained mathematical declarations. |
| Numerical checker | **Computed:** the pinned experiment entry states the tested dimensions, sampled unitaries and controls. It is independent evidence, with no numerical premise in the kernel proof. |
| Side effects and host limits | Git carries the formal source, Scribes, source note, frozen records and this dossier. Experiment material belongs to the experiments repository. Shared-resource failures and unavailable measurements, if any, are explicitly bounded in the delivery report rather than used as mathematical evidence. |

## ASSUMED-UNVERIFIED

Literature completeness, worldwide priority, and overlap with unpublished frame or boundary-spectrum work are not established. The follow-up papers named in #17863 are seat-reported literature readings. The numerical checker's local optima and sampled decompositions prove no statement about untested unitary matrices or dimensions. Dimension four, a formal all-$n\ge5$ family, and optimal perturbation constants remain open in this delivery. The four-slot escape audit remains unfinished under #18980.
