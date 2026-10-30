---
slug: liu-qiu-dahlsten-vedral-2025-pure-product-signalling-negativity
bibkey: liuqiudahlstenvedral2025lighttouch
doi: 10.1038/s41534-024-00956-0
url: https://arxiv.org/abs/2303.10544v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.result
---

# Every finite-dimensional signalling channel has a pure product input with positive PDM negativity

## Problem

X. Liu, Y. Qiu, O. Dahlsten and V. Vedral, *Quantum causal inference with extremely light touch*, arXiv:2303.10544v4 (npj Quantum Information 11, 54, 2025), define the causal monotone in Eq. (causmono) as
$f(R) := \lVert R\rVert_{tr}-1 = \Tr \sqrt{ R R^\dag}-1$ (arxiv.tex lines 143–145). For a channel with Choi-Jamiolkowski matrix
$M_{12}:= \sum_{i,j}\ket{i}\bra{j}^T \otimes \mathcal{M}_{2|1}(\ket{i}\bra{j})$ (Eq. (CHOI), lines 161–164), their two-time PDM is
$R_{12}=\frac12(M_{12}\rho+\rho M_{12})$ with $\rho=\rho_1\otimes\mathbbm{1}_2$ (Theorem 2timesPDM, lines 166–173). After the null-negativity theorem for channels that do not signal from $B$ to $A$, the paper states:

> We moreover conjecture that if the channel is signalling from B to A, we can always find a pure {\em product} input state such that $f(R_{B_1A_2} )> 0$. We prove this conjecture for a quite general case of 2-qubit unitary evolutions in the Supplementary Information.

This is the conjecture at arxiv.tex line 231. The formal statement uses finite nonempty index types $\alpha_1,\beta_1,\alpha_2,\beta_2$, a `QuantumChannel` $p$ from $\alpha_1\times\beta_1$ to $\alpha_2\times\beta_2$, and the module's `IsSignallingBA` predicate. It asks for vectors $a:\alpha_1\to\mathbb C$ and $b:\beta_1\to\mathbb C$ with $a^*\!\cdot a=1$, $b^*\!\cdot b=1$, and $0<\operatorname{traceNorm}(\operatorname{pdmBA}(p,a,b)^\mathsf{H})-1$.

## Motivation

A positive PDM negativity is a witness of signalling from $B$ to $A$ in the source's causal-inference setting. Pure product inputs would give a simple witness family, while the source had proved the assertion only for a broad two-qubit unitary case. Settling the statement for arbitrary finite index types tests whether the witness mechanism depends on that special unitary and qubit structure.

## Gap

Issue [#23073](https://github.com/the-omega-institute/trureturing/issues/23073) records a Tier 1 conjecture from the source paper and the literature check before any Lean. The source's v4 TeX retains the conjecture and reports only the two-qubit unitary case in its Supplementary Information. Searches recorded in the issue found no prior settlement in the searched sources, and the repository search found no existing declaration for this statement. The bounded search therefore left the conjecture open before the formal result.

## Route

1. `signalling_dichotomy` assumes `[Nonempty α₁]`, `[Nonempty β₁]`, `[Nonempty α₂]`, `[Nonempty β₂]`, a channel `p`, and `hp : IsSignallingBA p`. It produces a unit vector `a` with `¬ IsReplacement (conditionalMap p a)`. The proof constructs the discard and maximally-mixed append channels, uses that unit pure projectors span the complex matrix space, and shows that if every conditional map were a replacement map then the marginal would factor through `partialTraceRight`, contradicting `hp`.
2. `pdm_reduction` has no extra hypotheses beyond the finite-type instances and `p`, `a`, `b`. It identifies `pdmBA p a b` with the Jordan product
   $\frac12(DM+MD)$, where $D=(\operatorname{vecMulVec}(b,b^*))\otimes I_{\alpha_2}$ and $M=\operatorname{cjMatrix}(\operatorname{conditionalMap}(p,a))$.
3. `orthogonal_pair` assumes `[Nonempty β₁]`, a linear map `e`, and `he : \neg\,\operatorname{IsReplacement}(e)`. It returns unit vectors `b,c` with $b^*\!\cdot c=0$ and `e (vecMulVec c (star b)) \ne 0`. Its coordinate-basis and normalized sum-and-difference argument shows that vanishing on every such cross operator would force `e` to be a replacement map.
4. `pdm_hermitian_trace` assumes `ha : star a ⬝ᵥ a = 1` and `hb : star b ⬝ᵥ b = 1`; it proves that `pdmBA p a b` is Hermitian and has trace one.
5. `negative_minor` assumes `hb`, `hbc : star b ⬝ᵥ c = 0`, `he : conditionalMap p a (vecMulVec c (star b)) \ne 0`, and the exact reduction equality `hr` supplied by `pdm_reduction`. It proves `¬ (pdmBA p a b).PosSemidef` by taking a nonzero matrix entry of the cross image, choosing the corresponding coordinate vectors, and contradicting the zero-quadratic-form property of a positive semidefinite matrix.
6. `negativity_of_not_posSemidef` assumes a Hermitian matrix `r`, `trace r = 1`, and `¬ r.PosSemidef`; it proves `0 < traceNorm rᴴ - 1` from the nonzero negative part and the Jordan trace-norm identity. Applying it to the outputs of steps 1–5 gives `result`.

## Falsifier

The settlement would not answer the source conjecture if `IsSignallingBA` failed to mean the absence of a CPTP factorization of the $A_2$ marginal through the $A_1$ marginal, or if `pdmBA` failed to implement the source's Choi convention, Jordan product, and reduction to $B_1A_2$. The module uses the input-transposed Choi matrix, traces out $A_1$ and $B_2$, and concludes the exact trace-norm inequality shown in `result`; its quantifiers range over arbitrary finite index types with the required `Fintype` and `DecidableEq` instances. The theorem proves existence of a unit pure-product witness and does not assert that the witness maximizes the source's monotone.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/SignallingPureProductNegativity.lean.json`.

Declaration statements:

- `result`: `sha256:fb8011f10068651f7de23dd7934cc1621d657cf839735700ed405e0f623b42f2`.

- **Proof.** `result` is proved by the compiled helper chain `signalling_dichotomy`, `orthogonal_pair`, `pdm_reduction`, `pdm_hermitian_trace`, `negative_minor`, and `negativity_of_not_posSemidef`.
- **Axioms.** `result` depends on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 explicit conjecture of a 2025 npj Quantum Information paper, preregistered in issue #23073 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** For every finite nonempty $\alpha_1,\beta_1,\alpha_2,\beta_2$ equipped with the module's `Fintype` and `DecidableEq` instances, every `QuantumChannel` $p:(\alpha_1\times\beta_1)\to(\alpha_2\times\beta_2)$ satisfying `IsSignallingBA p` admits $a:\alpha_1\to\mathbb C$ and $b:\beta_1\to\mathbb C$ with `star a ⬝ᵥ a = 1`, `star b ⬝ᵥ b = 1`, and $0<\operatorname{traceNorm}(\operatorname{pdmBA}(p,a,b)^\mathsf{H})-1$.

**Computed, not formalized:** No numerical or finite-family computation was run or recorded in issue #23073 for this settlement.

**Argued, not formalized.**

- *Mechanism.* The helper chain has the following interpretation: signalling prevents every unit-$a$ conditional map from being a replacement map; a non-replacement map has an orthogonal cross operator with nonzero image; the Jordan-product reduction then supplies a negative direction for the reduced PDM, and Hermiticity with trace one converts that negative direction into a strictly positive trace-norm excess. This interpretation is not a separate public declaration.
- *Extension and sharpness.* The formal quantifiers cover arbitrary finite-dimensional index types, so the existence mechanism reaches beyond the source's two-qubit unitary case within this matrix model. `result` gives no optimal value of the negativity and no maximizing-input theorem; whether pure product inputs always maximize the source's $f$ remains open.
- *Neighbouring statements.* The source's null-negativity theorem for non-signalling channels is not a declaration in this module. Combining that source statement with `result` would give a two-way signalling witness characterization under the shared definitions, but that combination is not formalized here. The source's two-qubit unitary calculation, causal-inference protocol, and other cases are not affected or settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources recorded in issue #23073 and does not establish exhaustive worldwide novelty or priority; the issue records that the full set of citing works was not read. The identification of the module's definitions with every operational convention in the source is limited to the quoted TeX definitions and the Blueprint. The interpretive combination with the source's null-negativity theorem, the optimization suggestion for pure products, and all assertions about extensions beyond finite dimensions are not formalized and remain open.
