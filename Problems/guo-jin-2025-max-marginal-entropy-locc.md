---
slug: guo-jin-2025-max-marginal-entropy-locc
bibkey: guojin2025measure
doi: 10.48550/arXiv.2512.21992
url: https://arxiv.org/abs/2512.21992v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.result
---

# Maximum single-party entropy need not decrease on average under LOCC

## Problem

Y. Guo and Z.-X. Jin, *Measure of entanglement and the monogamy relation: a topical review*, arXiv:2512.21992v1, Section 9.4, p. 88, state:

> Note here that we can not prove here E′^(n) is nonincreasing on average under LOCC, but we conjecture that E′^(n) does not increase on average under LOCC for these cases mentioned above. Hereafter we always assume the conjecture is true.

Equation (189) defines $E'^{(n)}(|\psi\rangle)=\max_i h(\rho^{A_i})$, and Table 16 includes the von Neumann entropy $h=S$. Section 2 defines $S(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$. The settlement refutes the unrestricted entropy assertion using four parties of local dimension nine and one two-outcome local projective measurement.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite pure multipartite state | The amplitude argument of `claim`, indexed by `Fin n → Fin d` | Every finite party count and common local dimension; the witness has four parties and dimension nine. |
| Reduced state of party $i$ | `marginal` | The literal coordinate partial trace from the binding conventions in #20726. |
| $\max_i S(\rho^{A_i})$ | `maxMarginalEntropy` | The finite real supremum of the literal trace-log expression, divided by $\log 2$. |
| One local measurement, an LOCC operation | `applyLocal` and the Kraus-completeness hypothesis in `claim` | One coordinate changes, and the sum of adjoint products is the identity. A violation for this subclass refutes LOCC monotonicity. |
| Normalized input, probabilities, normalized branches | The finite squared-norm sums, norm-one hypothesis, and inverse-square-root scaling in `claim` | The binding convention is inlined literally; zero-probability branches contribute zero. Proofs reuse `finiteComplexEnergy` for that same sum. |
| Does not increase on average | The concluding inequality in `claim` | The maximum is inside the outcome average. |
| Refutation | `result` | Negation of the complete `claim`; no extra hypotheses. |

The real supremum represents a maximum for the nonempty finite party set in the witness. The claim extends the trace expression to arbitrary matrices, but its counterexample consists of normalized pure states and complete projectors. No positivity or physical-realization gap is used.

## Motivation

The settling GID is `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.result`, with `admission_basis: open-problem-resolution (#20726; Refuted)`. This external named problem has no anchor atom. One `OpenProblemResolutionClaim` records `Refuted` on the settling node. The [source note](../Library/Entropy/guojin2025measure.md) owns the source DOI.

## Gap

Fixed-party entropy monotonicity does not imply average monotonicity of the maximum over parties. The maximizing party can depend on the measurement outcome. The four-party witness distinguishes these two assertions.

## Route

The private `basis` and `psi` describe the sixteen basis tuples $(0,0,j,j)$ and $(j,j,0,0)$, with $1\le j\le8$, each of amplitude $1/4$. The private `psi_normalized` proves normalization. The private `psi_marginal` identifies every initial marginal as $\operatorname{diag}(1/2,1/16,\ldots,1/16)$, and `psi_max` gives initial value $5/2$.

The private `K` is the measurement on party zero with projectors $P_0=|0\rangle\langle0|$ and $P_1=I-P_0$. The private `K_complete` proves completeness, `apply_K` identifies the branches, and `branch_norm` gives probability $1/2$ for each. The private `branch_marginal` identifies an entropy-three marginal on party two for outcome zero and on party zero for outcome one. The private `branch_max_lower` proves that each outcome maximum is at least three. The private `outcome_term` gives the normalized probability-weighted contribution; `result` contradicts the proposed average inequality.

The entropy calculation applies `NoisyGraphStateCoherentInformationRefutation.entropy2`, `ChenKatoBrandaoCMIRefutation.entropy_diagonal`, `ThreeByThreeModulusEntropy.entropy_eq_spectrum`, and `PartialTraceMutualInformation.spectralEntropy`, with the functional-calculus carrier correspondence. `QuantitativeMultiOrbitWeilNegativeCertificate.finiteComplexEnergy` supplies the squared-norm expression. All theorem proofs are classified `bind-only`; each private helper has a named consumer. The public settling conclusion uses the external open-problem-resolution admission basis.

## Falsifier

A failure of input normalization, Kraus completeness, the initial value $5/2$, or either normalized outcome lower bound would invalidate the refutation. These obligations occur on the compiled proof path to `result`. The theorem asserts no upper bound on the outcome maxima.

## Evidence

The kernel-checked public conclusion is `D5.S3.Quantum.GuoJinMaxMarginalEntropyLOCC.result`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The experiment is [the immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d05903467105c17132f8eef4a51b8fbc5f5dcf98/docs/reports/guo-jin-2025-max-marginal-entropy-locc), revision `d05903467105c17132f8eef4a51b8fbc5f5dcf98`, path `docs/reports/guo-jin-2025-max-marginal-entropy-locc/check.py`. Its SHA-256 is `4617e83628541864bd1accdbe6f4251f35ce025c93de9fe891ebbf12801520ad`. The script was obtained with `git -C /Users/auric/trureturing-experiments show d05903467105c17132f8eef4a51b8fbc5f5dcf98:docs/reports/guo-jin-2025-max-marginal-entropy-locc/check.py`. The executed command `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 -u /Users/auric/.sshx/a1ca3d7c96ef2ad0a3010b1f/attempt-1/experiment-check.py` exits 0 on these identical script bytes.

It checks $L\in\{5,6,7,8,9,12,16\}$, with local dimension $L+1$. Both outcome probabilities are $1/2$, the initial marginal off-diagonal maximum is zero, and the entropy values agree numerically with $1+\tfrac12\log_2L$ and $\log_2L$. At $L=8$ it computes $2.5\to3$, $\tau:1.4375\to1.75$, and $1-\|\rho\|:0.5\to0.875$. Its fidelity check gives $E'_f(\mathrm{GHZ}_n)=1>E'_f(W_n)=H_2(1/n)$ for $3\le n\le8$. Its three-party random search uses seed $20261024$ and 3000 states for each local dimension two and three; the largest increase is $1.59\times10^{-15}$. These floating-point observations are not universal proofs.

## Triage

### What the settlement shows

1. **Proved in Lean:** the unrestricted $h=S$ conjecture is false (`result`). Its private proof witnesses $n=4$, local dimension nine, and a single two-outcome projective measurement. `psi_max` proves the initial maximum is $5/2$, and `branch_max_lower` proves each normalized outcome maximum is at least three.
2. **Proved in prose (failure mechanism):** outcome zero is $|0,0\rangle_{AB}\otimes8^{-1/2}\sum_{j=1}^8|j,j\rangle_{CD}$, and outcome one interchanges the pairs. Their single-party entropy vectors are $(0,0,3,3)$ and $(3,3,0,0)$: the fixed pair has a pure marginal, while each member of the other pair has eight equal eigenvalues $1/8$. The initial marginal eigenvalues are $1/2$ and eight copies of $1/16$, giving $5/2$. Thus the maximum cannot be interchanged with averaging using fixed-party monotonicity. Exact outcome maxima follow from this prose calculation; the Lean theorem uses only the lower bounds.
3. **Computed, finite scope:** the experiment entry checks the family formulas and a positive gap for $L\in\{5,6,7,8,9,12,16\}$. The asserted gap is $\tfrac12\log_2L-1$. Its positive sign for every $L>4$ is the elementary logarithmic comparison in the source's counterexample argument; a uniform Lean generalization is **open**. The numerical evidence covers exactly the seven listed values.
4. **Open:** the $n=3$ entropy conjecture and additional hypotheses restoring monotonicity. The numerical three-party search in the experiment entry gives no proof of either. The nearest surviving result is the unchanged fixed-party entropy monotonicity; no universal monotonicity theorem for the outcome-dependent maximum is asserted.
5. **Proved in prose (source-dependency boundary):** a false unrestricted premise cannot be cited as an established theorem in Section 9.4. This witness does not independently refute the source's conditional three-party consequences, because its party count is four; neither their antecedent restricted to three parties nor their conditional implication is negated here.
6. **Computed only:** the experiment entry observes violations for $\tau=2(1-\operatorname{Tr}\rho^2)$ and $1-\|\rho\|$ on the same seven finite family instances. The Lean `result` settles only the binding von Neumann entropy claim, and no Lean settlement for those other reduced functions is asserted.

## ASSUMED-UNVERIFIED

Literature completeness is **ASSUMED-UNVERIFIED**. The screen recorded in [#20726](https://github.com/the-omega-institute/trureturing/issues/20726) identifies the same conjecture in arXiv:2301.00334v3 and no settlement in the inspected portions of arXiv:2605.22150v1 and arXiv:2608.28985v1. The erratum and those later papers were not read in full. No originality claim or full literature-completeness claim is made.
