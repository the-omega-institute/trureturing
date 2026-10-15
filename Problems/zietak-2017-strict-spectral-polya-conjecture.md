---
slug: zietak-2017-strict-spectral-polya-conjecture
bibkey: zietak2017strictspectral
doi: 10.4064/bc112-0-16
url: https://doi.org/10.4064/bc112-0-16
triage: theorem
motivation_gids:
  - D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.result
---

# Ziętak's strict spectral approximant convergence conjecture

## Problem

K. Ziętak, “From the strict Chebyshev approximant of a vector to the strict spectral approximant of a matrix,” Banach Center Publications 112 (2017), Conjecture 1.1, asks whether Schatten-p approximant residuals converge to the residual of a strict spectral approximant for every complex matrix subspace.

The source statement is:

> Let M be a linear subspace of Cᵐˣⁿ and let Bₚ ∈ M be the cₚ-approximant to A ∈ Cᵐˣⁿ. As p tends to ∞, the matrix Rₚ = A − Bₚ converges to A − B⁽ˢᵗ⁾, where B⁽ˢᵗ⁾ is the strict spectral approximant to A.

### Statement echo

The Lean `claim` quantifies over all natural dimensions, complex matrix subspaces, targets, strict spectral approximants, and real-parameter functions of approximants. Its hypotheses require strict spectral minimality and a Schatten-$p$ minimizing approximant for every $p>1$; its conclusion is convergence of residual matrices. The module's `result` is the literal negation `¬ claim`.

## Motivation

Ziętak's conjecture is a named published open problem. Grover–Gupta, “Properties of best approximations with respect to the Ky Fan p-k norm, and the strict spectral approximant of a matrix,” LAA 743 (2026), Theorem 3.7, restates the convergence question and proves the case $\min(m,n)\le2$. The present 3×3 settlement supplies a counterexample outside that range.

## Gap

Ziętak and the cited follow-up paper leave the general linear matrix-subspace assertion unsettled in the literature screen recorded in [#15746](https://github.com/the-omega-institute/trureturing/issues/15746). The source and Grover–Gupta were checked for a prior counterexample; no settlement of the linear matrix-subspace statement was found in that literature screen. The Egger–Huotari (1989) vector witnesses were not readable, so their possible matrix-subspace relevance remains an ASSUMED-UNVERIFIED boundary.

## Route

Set $A=I_3$, $H=\begin{pmatrix}1&0&1\\0&-2&0\\1&0&0\end{pmatrix}$, $E=E_{33}$, and $\mathcal M=\operatorname{span}_{\mathbb C}\{H,E\}$. Every residual has the form $R(s,t)=\begin{pmatrix}1+s&0&s\\0&1-2s&0\\s&0&t\end{pmatrix}$. The two leading diagonal bounds force $s=0$ on the spectral-optimal face, whose lexicographic minimum occurs at $t=0$. Thus $E$ is a strict spectral approximant.

For every $p > 1$, a Schatten-$p$ minimizer exists. Hermitian projection reduces a complex minimizer to the real comparison. A moving competitor and power estimates show that every minimizer eventually has real last residual entry below −1/4. This is separated from the strict residual's last entry 0, so the universal convergence claim fails.

## Falsifier

A proof that every admissible function of Schatten-p approximants converges to every strict spectral residual would falsify the result. For this instance, a minimizer with real last residual entry eventually at least −1/4, or a failure of the strict-minimality or minimizer-existence hypotheses, would falsify the supplied route.

## Evidence

The kernel-checked settlement is `D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.lean`, with `result : ¬ claim` and standard axiom closure `{propext, Classical.choice, Quot.sound}`. The corresponding Scribe node carries `OpenProblemResolutionClaim` with `ResolutionKind.Refuted` for issue #15746.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The four-slot audits of the six public theorems in `UpperBranchReduction` are unfinished; [issue #16250](https://github.com/the-omega-institute/trureturing/issues/16250) states their declaration identities and missing dependent-family evidence. No unfinished Reg source is included.

The numerical reading is the experiment entry [`docs/reports/zietak-2017-strict-spectral-polya-conjecture/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/2b5379616c9b15e648489b590d9b3dbacf9783a9/docs/reports/zietak-2017-strict-spectral-polya-conjecture), pinned to commit `2b5379616c9b15e648489b590d9b3dbacf9783a9`. Running `python3 check.py` exited 0 with final line `bad= 0`; the script SHA-256 is `770c269a194d78eb323be7dc404dcca70eef294006c008fbbb16506b9394581d`. The $3\times3$ samples are $(q,c)\in\{(2,1),(1.5,0.5),(3,2),(1.1,0.1)\}$ at $p\in\{10,50,200,1000,3000\}$; each parameter pair also has 20,000 random complex disk tests, and each exponent has 200 local complex perturbation tests. The $4\times4$ samples are $(q,c,\delta)\in\{(2,1,1/2),(3,2,1/4)\}$ at the same exponents. These are finite computed readings, including $t_{3000}<-0.99$ for the $3\times3$ samples and $|t_{3000}-(\delta-1)|<0.02$ for the $4\times4$ samples.

## Triage

- **Kernel-checked — the refuted instance.** For $q=2$ and $c=1$, the strict spectral approximant is E, every $p>1$ has a $c_p$-approximant, and every such minimizer is eventually separated from E. The declarations are `strict_approximant`, `exists_cp_approximant`, `cp_minimizers_separated`, and `result`.
- **Proved in prose — coupling mechanism.** The strict residual $\operatorname{diag}(1,1,0)$ has a repeated leading singular-value cluster. The coupling is noncommuting: $(HE)_{13}=1$ whereas $(EH)_{13}=0$, hence $HE\ne EH$. A finite-p optimizer can split that cluster while increasing the third residual magnitude. The uniform separation itself is kernel-checked by `real_minimizers_separated`; the mechanism description is an explanation of this construction.
- **Computed — family readings.** The experiment checks only the parameter pairs and exponents specified in Evidence.
- **Open — the full family and exact limit.** The statement $B_p\to2E$ for every $q>1$, $c>0$ is not kernel-checked or established by those finite samples.
- **Computed — 4×4 extension readings.** For $A=\operatorname{diag}(1,1,3\delta/4,\delta/4)$, $0<\delta<1$, and $T=\operatorname{diag}(0,0,1,-1)$, take $\mathcal M=\operatorname{span}\{H\oplus0,T\}$. The target is positive definite. The strict residual $\operatorname{diag}(1,1,\delta/2,\delta/2)$ is invertible, with strict approximant $(\delta/4)T$. The tested finite-$p$ values approach the proposed different limit $(1-\delta/4)T$. The convergence for arbitrary $\delta,q,c$ is **open** beyond the sampled values.
- **Literature — surviving special case.** Grover–Gupta Theorem 3.7 proves convergence for $\min(m,n)\le2$; this Refuted instance has $\min(m,n)=3$ and does not alter that theorem.
- **Proved in prose — fixed-competitor boundary.** Eventual comparison with each fixed competitor has quantifier order $\forall X\,\exists p_0\,\forall p\ge p_0$. It supplies no uniform threshold $\exists p_0\,\forall X\,\forall p\ge p_0$ for moving minimizers. Ziętak's 1997 fixed-competitor theorem therefore does not supply the uniform comparison needed for the conjecture.
- **Open — neighbouring questions.** Which subspaces satisfy the conjecture, including commuting subspaces, and the exact general limit of $B_p$ remain unresolved.
- **Open — source dependence.** Ziętak's other statements that rely on Conjecture 1.1 require re-examination where they use convergence rather than a fixed-competitor result.

- **Open — uniqueness and reality of minimizing parameters.** The module proves minimizer existence and a Hermitian-projection comparison, which suffice for the refutation. It does not prove uniqueness, that every complex minimizer is real, or the proposed stationarity identities.
- **Open — uniform stationarity and exact-limit route.** The two stationarity identities and the unrestricted parameter limit remain obligations of the family-level route. The unconditional instance uses `real_minimizers_separated` instead.

### What the settlement shows

The refutation applies to the universal linear-subspace claim by exhibiting a 3×3 subspace with a strict residual and uniformly separated finite-p minimizers. It does not refute the low-dimensional theorem or establish the exact general limit $B_p\to2E$; those are separate statements.

The proposed exact-limit route for all $q>1$ and $c>0$ uses stationarity. Write $d=1+s_p$, $h=1-qs_p$ and let the coupled $2\times2$ block have eigenvalues $\lambda_p$ and $-b_p$. With $r_p=cs_p/(d+b_p)$, the proposed identities are $b_p^{p-1}=\lambda_p^{p-1}r_p^2$ and $\lambda_p^{p-1}(1-r_p^2+2cr_p)=qh^{p-1}$. If $b_p$ stays bounded below $1$ along a subsequence, the first identity forces $s_p$ and $r_p$ to be exponentially small. Dividing the second identity by $h^{p-1}$ then gives $1=q$ in the limit, contradicting $q>1$. This yields $b_p\to1$ and $t_p\to-1$ once minimizer reality, the bounds, and these stationarity identities are established. Those obligations and the analogous unrestricted $4\times4$ limit are not proved by this module or by the finite experiment.

## ASSUMED-UNVERIFIED

The Egger–Huotari (1989) witnesses were not readable, so their possible realization by complex linear matrix subspaces is unverified. Literature completeness beyond the cited Ziętak and Grover–Gupta sources is not claimed.
