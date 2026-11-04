---
slug: masini-theurer-plenio-2021-postprocessed-improvement-unfaithfulness
bibkey: masinitheurerplenio2021interferometry
doi: 10.1103/PhysRevA.103.042426
url: https://arxiv.org/abs/2102.04863v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.result
---

# Biased post-processed interferometric improvements are not faithful

## Problem

M. Masini, T. Theurer and M. B. Plenio, *Coherence of operations and interferometry*, Phys. Rev. A 103, 042426 (2021), arXiv:2102.04863v2, Section IV (Conclusions), `PaperMasiniTheurerPlenio.tex`, line 300:

> Whilst we provided a method to compute the pre-processed improvements and showed that they are not faithful for $\lambda\ne\mu$, it is an open question whether there exist analogous results for the post-processed cases.

The source defines faithfulness in Section II A, line 153:

> $M(\Theta)=0$ exactly if $\Theta$ is a free channel.

Here $\mu=1-\lambda$, $\Delta$ removes off-diagonal entries in the chosen incoherent basis, and the free channels for coherence creation are the maximally incoherent operations, characterized by $\Psi\Delta=\Delta\Psi\Delta$ (Section II A, lines 132–134). The phase channel is conjugation by $U=\operatorname{diag}(e^{i\phi_k})$ (Section II B, lines 171–175). The post-processed improvement is defined in Section III B, Eq. (14), line 273:

> $N_{\lambda,\vec{\phi}}(\Theta):=\max_{\Psi\in\mathcal{MIO}}\left|\left|\left(\lambda-\mu \Lambda_{\vec{\phi}}\right) \Psi \Theta\Delta\right|\right|_1-|\lambda-\mu |$.

The source calls the operation norm the induced trace norm (Section III A, line 202). The formal reading uses $\|\Phi\|_{1\to1}=\sup_{\|A\|_1\le1}\|\Phi(A)\|_1$ over all complex matrices, with no positivity or Hermiticity restriction on $A$.

Issue [#22607](https://github.com/the-omega-institute/trureturing/issues/22607) fixes the faithfulness half of the question: for every $\lambda\in[0,1]$ with $\lambda\ne\tfrac12$, every natural $M\ge1$, and every $\vec\phi\in\mathbb R^M$, there exists a qubit-to-qubit channel $\Theta$ that is not maximally incoherent and has $N_{\lambda,\vec\phi}(\Theta)=0$, optimizing over all MIO channels from the qubit to dimension $M$. This is proved.

The definitions and source locators are collected in [the literature note](../Library/Divergence/masinitheurerplenio2021interferometry.md).

## Motivation

The discrimination game tests whether a channel's ability to create coherence improves the success probability beyond guessing from the prior alone. Faithfulness would require every coherence-creating channel to provide a positive improvement. A zero-valued nonfree channel therefore separates the presence of coherence creation from its usefulness in a fixed game, even when all free post-processings are available.

## Gap

The literature check recorded in #22607 has a bounded scope:

- The v2 source retains the question in Section IV, line 300.
- The preregistration reports that both arXiv versions retain it, and that a screen of 13 citing full texts and the same-author paper arXiv:2609.40186 found no treatment of the biased post-processed case.
- It also records no match in formal-conjectures or MathDB and no existing repository record at preregistration.

A settlement was `not-found-in-searched-scope`. The v2 source quotation is directly checked; the reported literature and historical repository searches are not independently reproduced here.

## Route

Write $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\delta=|2\lambda-1|$, $\rho_t=(I_2+tX)/2$, and $\Theta_t(A)=\operatorname{tr}(A)\rho_t$. The following helpers are private declarations of the canonical module.

1. **The preparation channel.** For real $t$ with $0\le t\le1$, `prepared_channel` proves that $\Theta_t$ is completely positive and trace preserving. For real $t\ne0$, `prepared_not_mio` proves it is not MIO: the diagonal input $|0\rangle\langle0|$ is sent to $\rho_t$, whose off-diagonal entry is $t/2$.
2. **Uniform control of the post-processing.** For any natural $M$ and any MIO $\Psi$ from the qubit to dimension $M$, `postprocessing_data` supplies, with $D=\Psi(I_2/2)$ and $E=\Psi(X/2)$, $\Delta D=D$, $D\ge0$, $\operatorname{tr}D=1$, $\operatorname{tr}E=0$, and $D+E,D-E\ge0$. For any real $0\le\lambda\le1$, any real phase vector, and square complex $D,E$ satisfying $\Delta D=D$ and $D\pm E\ge0$, `sandwich` proves $D\pm F\ge0$, where $F=\lambda E-(1-\lambda)UEU^\dagger$. Indeed,
   $D+F=\lambda(D+E)+(1-\lambda)U(D-E)U^\dagger$ and $D-F=\lambda(D-E)+(1-\lambda)U(D+E)U^\dagger$.
3. **The sign of the output.** For real $\lambda,t$, any phase vector and square complex $D,E$, `biased_norm` assumes $D\ge0$, $\operatorname{tr}D=1$, $\operatorname{tr}E=0$, $0\le t\le|2\lambda-1|$, and $D\pm F\ge0$. It proves $\|(2\lambda-1)D+tF\|_1=|2\lambda-1|$. The matrix has trace $2\lambda-1$; it is positive semidefinite when $2\lambda-1\ge0$ and negative semidefinite when $2\lambda-1\le0$.
4. **The full induced norm.** `trace_bound` proves $|\operatorname{tr}A|\le\|A\|_1$ for every square complex matrix $A$. For natural input dimension $a\ge1$, any natural output dimension, and any square complex output matrix $H$, `norm_prepare` proves $\|A\mapsto\operatorname{tr}(A)H\|_{1\to1}=\|H\|_1$. A coordinate projector attains this value, and the trace bound bounds every value on the unit ball; the proof uses `IsGreatest.csSup_eq`.
5. **The optimized value.** For $0\le\lambda\le1$, any natural $M$, any phase vector and any MIO $\Psi$ from the qubit to dimension $M$, `postprocessed_norm` proves that the norm in the optimization for $\Theta_{\delta/2}$ is exactly $\delta$. For $M\ge1$, `mio_nonempty` supplies the diagonal preparation $A\mapsto\operatorname{tr}(A)|0\rangle\langle0|$. Under $M\ge1$ and $0\le\lambda\le1$, `improvement_zero` identifies the optimized value set with the singleton $\{\delta\}$ and concludes $N_{\lambda,\vec\phi}(\Theta_{\delta/2})=0$ for every phase vector.
6. **The biased witness.** If also $\lambda\ne\tfrac12$, then $0<\delta\le1$. Thus $t=\delta/2$ meets the channel and non-MIO hypotheses, giving `result` for every $M\ge1$ and every phase vector.

## Falsifier

The settlement would miss the question if the free operations, norm or optimization differed from the registered reading. The module uses complex linear maps on full matrix spaces; `IsChannel` means complete positivity and trace preservation, and `IsMIO` adds the dephasing identity for every complex input matrix. `phaseChannel` is exactly diagonal unitary conjugation. `inducedTraceNorm` uses the entire complex matrix unit ball, and `postImprovement` composes dephasing, $\Theta$, $\Psi$, and the weighted phase difference in that order.

The formal definition uses a real supremum instead of the source's maximum. For the witness this is justified by attainment and an upper bound in `norm_prepare` with input dimension two, and by the nonempty singleton value set in `improvement_zero` for $M\ge1$ and $0\le\lambda\le1$; no convention for an empty or unbounded supremum supplies the conclusion.

The theorem includes endpoint priors and $M=1$. It imposes no phase-separation hypothesis, so it also covers the phase vectors with unequal components assumed by the source in Section II B, line 177. It does not assert faithfulness or unfaithfulness at $\lambda=\tfrac12$.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.lean`.

- **Proof.** It proves `result`, the quantified existence statement above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful.lean.json`.

Declaration statements:

- `result`: `sha256:961004ed6d3cf0bf679d5fa0ee076ef1ce4c1d0ad75c34541b713585d6ac8898`.

## Triage

Tier 1 question of a 2021 Phys. Rev. A paper, preregistered in issue #22607 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every real $\lambda$ with $0\le\lambda\le1$ and $\lambda\ne\tfrac12$, every natural $M\ge1$, and every real phase function on $\mathrm{Fin}\,M$, there exists a complex linear map from two-by-two matrices to two-by-two matrices that is completely positive and trace preserving, is not MIO, and has `postImprovement` equal to zero.

**Computed, not formalized.** No numerical experiments are used in this dossier, and #22607 records no numerical computation to report.

**Argued, not formalized.**

- *Mechanism and a larger interval.* Fix $0\le\lambda\le1$, $\lambda\ne\tfrac12$, $M\ge1$, and any phase vector. The same construction gives a whole interval $0<t\le\delta$ of nonfree preparation channels, rather than only the witness $t=\delta/2$. To see this, $\delta\le1$ makes $\rho_t$ a convex combination of $(I_2+X)/2$ and $(I_2-X)/2$ with weights $(1+t)/2$ and $(1-t)/2$, so it is a trace-one positive matrix and its preparation map is a channel; its nonzero off-diagonal entry excludes MIO. For each MIO $\Psi$ from the qubit to dimension $M$, `postprocessing_data` gives the diagonal $D\ge0$, trace conditions and $D\pm E\ge0$ listed in Route. With these hypotheses and $0\le\lambda\le1$, `sandwich` gives $D\pm F\ge0$. Now $H=(2\lambda-1)D+tF$ has trace $2\lambda-1$. For $2\lambda-1\ge0$, write $H=(2\lambda-1-t)D+t(D+F)\ge0$; for $2\lambda-1\le0$, write $-H=(1-2\lambda-t)D+t(D-F)\ge0$. These are precisely the hypotheses of `biased_norm`, giving $\|H\|_1=\delta$. Dephasing preserves trace, so the composed map is $A\mapsto\operatorname{tr}(A)H$, and `norm_prepare` applies with input dimension two. Every admissible post-processing therefore has induced norm $\delta$, and `mio_nonempty` applies because $M\ge1$, giving a nonempty singleton optimization and zero improvement. This interval extension is not the statement of `result`.
- *Sharpness within this family.* For $0<\lambda<1$, $\lambda\ne\tfrac12$, and $\delta<t\le1$, take $M=2$, the MIO identity post-processing and phases $(0,\pi)$. Then $UXU^\dagger=-X$, so the output matrix is $H=((2\lambda-1)I_2+tX)/2$, with eigenvalues $(2\lambda-1+t)/2$ and $(2\lambda-1-t)/2$. Its trace norm is $\max(\delta,t)=t>\delta$. The induced norm of this trace-preparation map equals that trace norm by `norm_prepare` with input dimension two. Thus the norm cannot remain equal to the prior baseline for every phase vector and every MIO post-processing beyond $t=\delta$. This is an analytic calculation, not a numerical experiment or a formalized optimality theorem.
- *The unbiased neighbour.* Masini, Theurer and Plenio (2021), arXiv:2102.04863v2, Section III B, Theorem 5, TeX line 287, state: “The functionals $N_{\frac{1}{2},\vec{\phi}}(\Theta)$ are faithful for all $\vec{\phi}\in\mathbbm{R}^M$ with at least two different components.” This is a separate source result with a different prior hypothesis; it is not formalized by `result`.
- *Effect on the paper.* The settlement answers the faithfulness half of the concluding question. It is compatible with the source's convex-measure theorem: Section II A, lines 140–160, defines a resource measure using nullity, non-negativity and monotonicity, with faithfulness an additional property, and the proof of the post-processed measure theorem at lines 851–912 does not assume the concluding question. The other half, a general method to compute post-processed improvements for arbitrary channels, remains open in this settlement. The subsequent questions about combining creation and detection, optimizing phases and using Fisher information (Section IV, lines 300–303) are not resolved.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The v1 reading, screen of 13 citing full texts and arXiv:2609.40186, formal-conjectures and MathDB searches, and absence of a repository record at preregistration are reports from #22607 and have not been independently reproduced here.

The larger coherence interval, its sharpness calculation, and the interpretive consequences in “Argued, not formalized” are not additional Lean results. The source's unbiased faithfulness theorem and its general convex-measure and operational assertions are source-attested rather than formalized by this module. A general evaluation algorithm and the source's other concluding questions are not settled. No numerical evidence is offered.
