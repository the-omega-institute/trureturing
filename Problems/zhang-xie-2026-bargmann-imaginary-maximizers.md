---
slug: zhang-xie-2026-bargmann-imaginary-maximizers
bibkey: zhangxie2026bargmann
doi: 10.48550/arXiv.2601.01858
url: https://arxiv.org/abs/2601.01858v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/BargmannImaginaryMaximizers.result
---

# All qubit tuples maximizing the imaginary Bargmann invariant

## Problem

Lin Zhang and Bing Xie, *A Survey of Bargmann Invariants: Geometric Foundations and Applications*, arXiv:2601.01858v2, p. 26, ask:

> The quantity τ_n predicts the upper bound for the imaginary part of any nth-order Bargmann invariant. This immediately raises the question: what is the complete set of n-tuples Ψ = (|ψ_1⟩, …, |ψ_n⟩) in ℂ² that achieve Im Tr(ψ_1 … ψ_n) = τ_n? We leave this characterization, along with the operational interpretation of the condition z ∈ 𝓑_{n+1} ∖ 𝓑_n, as interesting open problems for future work.

The first question is **Proved** with the exact conventions in [preregistration #19224](https://github.com/the-omega-institute/trureturing/issues/19224). For every $n\ge3$, a tuple of unit vectors in $\mathbb C^2$ attains

$$\tau_n=\frac{\cos^n(\pi/n)}{\cos^{n-1}(\pi/[2(n-1)])}$$

if and only if $\psi_j=\eta_jUv_j$ for one common $2\times2$ unitary $U$, independent phases $|\eta_j|=1$, and

$$v_j=(\sqrt{1-t_n},\sqrt{t_n}\,e^{2\pi ij/n}),\qquad t_n=\frac{1-\tan(\pi/[2(n-1)])/\tan(\pi/n)}2.$$

The [Library note](../Library/QuantumContext/zhangxie2026bargmann.md) gives Definition 3.1, Corollary 5.5, Eq. (5.15), and the source question.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every $n\ge3$ | `claim` universally quantifies `n` with `3 ≤ n` | Exact |
| Unit vectors in $\mathbb C^2$ | `Ψ : Fin n → Fin 2 → ℂ`, with `star (Ψ j) ⬝ᵥ Ψ j = 1` for every `j` | Exact; the wave-function condition is inlined |
| Pure state $|\psi_j\rangle\langle\psi_j|$ and ordered trace | `bargmann` uses `Matrix.vecMulVec`, `List.ofFn`, `List.prod`, and `Matrix.trace` | Exact; the projector expression is inlined |
| Maximal imaginary value | `tau` is the source's cosine-power quotient | Exact; natural subtraction occurs in the exponent, real subtraction in the angle |
| Complete set | `result : claim` proves both directions of the equality/orbit equivalence | Exact |
| Explicit candidate answer | `maximizer` is the displayed latitude vector; one `U ∈ Matrix.unitaryGroup (Fin 2) ℂ` and phases `η` | The answer proposed in #19224, with no added hypothesis |

No clause is dropped or weakened. The source's second question is outside this equivalence.

## Motivation

The maximum value alone does not identify all tuples attaining it. The orbit equivalence identifies every maximizer, including its individual phase freedom and a common unitary rotation. It supplies the equality classification accompanying the source's sharp value.

## Gap

The literature screen in #19224 reports that Zhang–Xie v1/v2, Li–Tan (arXiv:2412.08022), Pratapsi–Gouveia–Novo–Galvão (arXiv:2506.17132v3), Xu (arXiv:2506.13266), and the citing works 2412.17237, 2507.14878, 2601.16435, 2604.18833, 2605.07405, 2608.28985, 2609.11090, 2609.22902 and 2610.04930 give the maximum or a realizing family without this classification. These are issue-supplied literature readings. Search completeness is `ASSUMED-UNVERIFIED`; no exhaustive novelty claim is made.

The Li–Tan positivity question in #19081 concerns a different transform and conclusion. The present theorem classifies equality tuples.

## Route

Write $a=\pi/n$, $b=\pi/[2(n-1)]$, and $\omega=e^{2\pi i/n}$. The following describes the proof in the settling module.

1. A positive imaginary Bargmann value makes every cyclic overlap nonzero. Rephasing puts those overlaps on a common ray $r_je^{i\phi}$, with $\phi=\arg(\Delta)/n$. AM–GM bounds their product by the $n$th power of their mean $R$.
2. Fourier inversion expresses the mean overlap as $\sum_k\omega^k\|f_k\|^2$, with total energy one. The exposed polygon edge gives $R\cos(a-\phi)\le\cos a$. Equality removes all modes except zero and one.
3. Scalar differentiation gives the unique maximum at $\phi=a-b$ and $R=\cos a/\cos b$.
4. Parseval and unit length at the vertices zero and one make the surviving modes orthogonal. The imaginary part of $\omega$ is nonzero for $n\ge3$. The mean overlap fixes the second mode's squared length to $t_n$.
5. The imported `D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq` realizes equal Gram matrices by a common unitary. It turns the two modes into the explicit latitude polygon.
6. Conversely, the polygon has constant cyclic overlap $(\cos a/\cos b)e^{i(a-b)}$ and imaginary invariant $\tau_n$. Common unitary transformations and independent vector phases preserve the ordered trace.

## Falsifier

The settlement would fail to answer the source if the ordered trace were replaced by an unordered product, the wave-function condition were weakened, one common unitary were replaced by independent unitaries, the phase or latitude convention were changed, or either implication were omitted. The four public definitions and `result` retain the conventions of #19224. The theorem has no dimension or size restriction beyond qubits and $n\ge3$.

## Evidence

The mathematical source is [BargmannImaginaryMaximizers.lean](../D5/S3/Quantum/Information/BargmannImaginaryMaximizers.lean), with its [Blueprint](../Blueprint/D5/S3/Quantum/Information/BargmannImaginaryMaximizers.md). The public surface consists of `bargmann`, `tau`, `maximizer`, `claim`, and the single theorem `result`. All auxiliary declarations are private and consumed. The module's admission basis is `open-problem-resolution (#19224; Proved)`, its generality is I, and its utility is `none`: the statements are symbolic identities, inequalities, structural existence statements and an all-$n$ classification, with no numerical certificate or finite enumeration. No separate supporting module is required.

The four-slot escape audit of `D5.S3.Quantum.Information.BargmannImaginaryMaximizers.result` is unfinished: [issue #19337](https://github.com/the-omega-institute/trureturing/issues/19337) identifies the missing source-family reconstruction, realization bridge, whole-family variation, sensitivity and observational-dependence evidence. No validated registration is claimed.

### Numerical check

[Experiment directory at commit `e479a10d3ae812bce418cee3a378e3f429514d0b`](https://github.com/the-omega-institute/trureturing-experiments/tree/e479a10d3ae812bce418cee3a378e3f429514d0b/docs/reports/zhang-xie-2026-bargmann-imaginary-maximizers).

Command: `python3 /Users/auric/trureturing-experiments/docs/reports/zhang-xie-2026-bargmann-imaginary-maximizers/check.py`; exit 0, `RESULT PASS`. Script SHA-256: `52e220563a11d433300db0d17c6ec17d8c90fdfc547dd58bf45e7c6a91102eb9`. The script and pinned repository object compare byte-identical. The tested scope is exactly $n=3,\ldots,8$, with 40 random-restart local searches per size and at most 4000 iterations per restart. These are finite numerical checks, not a proof of an upper bound or uniqueness.

| $n$ | $\tau_n$ and family value (12 decimals) | Maximum found minus $\tau_n$ | Smallest absolute-Gram distance over cyclic shifts/reflections |
| --- | --- | --- | --- |
| 3 | 0.250000000000 | $1.67\times10^{-16}$ | $6.03\times10^{-9}$ |
| 4 | 0.384900179460 | $3.89\times10^{-16}$ | $4.38\times10^{-9}$ |
| 5 | 0.475693086076 | $4.44\times10^{-16}$ | $9.70\times10^{-9}$ |
| 6 | 0.542190822893 | $0$ | $7.76\times10^{-9}$ |
| 7 | 0.593343000807 | $4.44\times10^{-16}$ | $2.14\times10^{-8}$ |
| 8 | 0.634037925654 | $-1.11\times10^{-16}$ | $2.71\times10^{-8}$ |

## Triage

| Item | Status and evidence kind |
| --- | --- |
| Exact qubit settlement for every $n\ge3$ | **Proved, kernel-checked:** `D5.S3.Quantum.Information.BargmannImaginaryMaximizers.result` |
| Fourier mechanism and two-mode rigidity | **Proved in the module:** private `Fourier.fourier_exposed_edge` and `Fourier.exposed_edge_two_mode_orthogonal` on the proof path of `result`; the Bloch-circle description below is an interpretation of the explicit vector |
| Equality case for adjacent overlaps | **Proved in the module:** private `maximizer_overlap` gives the constant overlap of the representative; private `Gauge.cyclic_phase_equalization` and `Scalar.scalar_saturation` identify the common-ray phase and mean at the maximum. Independent phases mean original overlaps need not themselves be equal |
| Attainment for $n=3,\ldots,8$ | **Computed:** numerical check above, same script, scope and exit 0; the all-$n$ equivalence is separately kernel-checked by `result` |
| Random-search maxima and absolute-Gram agreement for $n=3,\ldots,8$ | **Computed:** numerical check above; this is evidence about sampled local searches only |
| Integration, supporting module and utility | **Delivered structure:** one settling Lean module, Scribe and resolution claim; consumed private helpers and the frozen Gram reuse; no separate general module; `utility: none` for the symbolic statements |
| Source misfit | **None:** the statement echo preserves all source clauses |
| Operational interpretation of $\mathcal B_{n+1}\setminus\mathcal B_n$ | **Open:** the source's second question, outside `claim` |
| Classification in dimensions $d\ge3$ | **Open:** no declaration here states this extension |
| Four-slot escape registration | **Unfinished:** #19337; this is an audit boundary, not a mathematical premise |
| Literature status | **Literature reading:** screen recorded in #19224; completeness `ASSUMED-UNVERIFIED` |

### What the settlement shows

**Proved, kernel-checked by `result`:** qubit equality tuples form exactly one common unitary orbit, with independent vector phases, of the explicit latitude polygon for every $n\ge3$. Thus the source's known realizing family exhausts the qubit equality cases. The source's maximum value remains the same; the added conclusion is completeness of the equality family.

**Explanation from the explicit coordinates:** under the standard pure-qubit Bloch map, the displayed vectors have fixed polar coordinate $1-2t_n$ and equally spaced azimuths $2\pi j/n$, so they describe a regular polygon on a latitude circle. A common unitary rotates that picture. This geometric interpretation is not an additional Lean theorem.

**Proved in the private proof steps:** the exposed Fourier edge retains two modes; the unit-length equations make them orthogonal, and the overlap fixes their relative weights. The representative's constant overlap is sharp, while vector rephasing accounts for the phase freedom of general maximizers. The public theorem asserts the orbit equivalence, not a separate classification of every overlap gauge.

**Open:** neither the operational meaning of consecutive Bargmann-set differences nor the classification in dimensions at least three is asserted. No relaxed-hypothesis or higher-dimensional theorem is delivered, and no claim is made about changing other results of the survey.

## ASSUMED-UNVERIFIED

Literature-search completeness and exhaustive novelty are `ASSUMED-UNVERIFIED`. The source and literature screen beyond the quoted survey are supplied by #19224. The numerical experiment covers only the stated six sizes and finite local searches. Four-slot escape registration remains unfinished under #19337.
