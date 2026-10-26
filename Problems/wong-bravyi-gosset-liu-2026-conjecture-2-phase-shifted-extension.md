---
slug: wong-bravyi-gosset-liu-2026-conjecture-2-phase-shifted-extension
bibkey: wong2026leeyang
doi: 10.48550/arXiv.2602.03605
triage: theorem
motivation_gids:
  - D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.result
url: https://arxiv.org/abs/2602.03605v1
---

# The phase-shifted extension of Conjecture 2

## Problem

Wong, Bravyi, Gosset and Liu, *Lee-Yang tensors and Hamiltonian complexity*, arXiv:2602.03605v1, Section 5.5, Conjecture 2:

> Suppose n ≥ 2, s ∈ [0,1), and the interaction graph is connected. Then the second smallest eigenvalue of H_s coincides with the smallest eigenvalue of H_s restricted to the odd-weight subspace.

Section 5.6 asks:

> We leave as an open question whether Conjectures 1, 2, 3 hold for phase-shifted EPR-like Hamiltonians.

The question settled here is the extension of Conjecture 2. Preregistration: [#18759](https://github.com/the-omega-institute/trureturing/issues/18759). This is an external published question, tier 1.

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| $n\ge2$ | `claim` quantifies over natural `n` with `2 ≤ n`. |
| Connected interaction graph | `SimpleGraph (Fin n)`, its adjacency decision procedure, and `G.Connected`. The decision procedure is computational infrastructure. |
| $0\le s<1$ | The two inequalities in `claim`. |
| $h(z)=\lvert00\rangle\langle00\rvert+z\lvert11\rangle\langle00\rvert+\overline z\lvert00\rangle\langle11\rvert+\lvert z\rvert^2\lvert11\rangle\langle11\rvert$ | `hpq` has exactly these four entries, with the identity on all other bits. |
| $H_s(\theta)=-\sum_{\{p,q\}\in E}h_{p,q}(se^{i\theta_{p,q}})$ | `H` counts each undirected edge once using `p < q`. |
| Arbitrary edge angles in $[0,2\pi)$ | Real representatives in the exponential; the counterexample uses only $0$ and $\pi$, both in the source interval. |
| Second smallest eigenvalue | `eigAsc`, sorted with multiplicity, and `List.getD` at index $1$. |
| Smallest eigenvalue on the odd-weight subspace | Restriction by `Matrix.submatrix` to the odd computational basis and index $0$. The odd weight count is inlined literally in `claim`; the private certificate relates it to Mathlib's `hammingNorm`. |
| Negative settlement | `result : ¬ claim`. |

The arbitrary default in `List.getD` and the empty non-Hermitian branch of `eigAsc` totalize the definitions. The witness matrices are Hermitian and the relevant lists have the required entries. The computational basis is `Fin n → Fin 2` directly.

## Motivation

The settling declaration is `D5/S0/Certificates/LeeYangPhaseShiftedParityRefutation.result`. It refutes the universal phase-shifted parity assertion using a connected four-cycle, $s=3/5$, and one edge of phase $\pi$. The original zero-phase Conjecture 2 is outside this negative conclusion.

## Gap

The published question permits independent edge phases. On a cycle their flux can change the ordering of the parity sectors. The formal conclusion needs strict separation of the second full-space eigenvalue from the odd minimum; it needs neither simplicity nor a parameter interval.

## Route

The certificate uses edges $\{0,1\}$, $\{0,3\}$, $\{1,2\}$, $\{2,3\}$ and phase $\pi$ only on $\{0,3\}$. Explicit eigenvectors exhibit the full-space eigenvalues
$-(67+\sqrt{1989})/25<-(35+\sqrt{901})/25<-5/2$.
The odd restriction satisfies $25M^2+68M+18I=0$, which places all its eigenvalues above $-5/2$. Increasing order with multiplicity then gives the strict inequality needed to negate `claim`.

All auxiliary declarations are private and consumed. The proof classification is bind-only, with admission basis `open-problem-resolution (#18759; Refuted)` and computational utility `certified-instance` under `refutes`.

## Falsifier

A failure of the Hamiltonian entries, the odd restriction, either explicit eigenvector equation, or the strict inequalities would invalidate this certificate. The theorem concerns the preregistered literal operator and eigenvalue conventions, with the axiom closure contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Evidence

Kernel-checked: `D5.S0.Certificates.LeeYangPhaseShiftedParityRefutation.result`. Its private `ham_separation` proves the strict separation at $s=3/5$; it does not state an exact value for the second eigenvalue or its simplicity.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment: [pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f55c81f21d6288891d11b00f8b56992a1cdcc597/docs/reports/wong-bravyi-gosset-liu-2026-phase-shifted-conjecture-2). Command: `python3 check.py`, exit 0; script SHA-256 `1f0420b714cff8a5de260b1ef7230c6f2eed1dec54aac146895fd8902c4dcf88`. The implementation seat reran these pinned bytes. At $s=3/5$, it checks exact Hermiticity, parity preservation and the characteristic-polynomial roots, and computes the numerical eigenvalues $-4.4639$, $-2.6007$, and the odd minimum $-2.4228$; simplicity is a numerical reading. The zero-phase four-cycle control at $s=0.6$ has second eigenvalue and odd minimum $-2.72$. The phase grid is exactly $s=0.05,0.10,\ldots,0.95$; violations occur at $0.55,0.60,\ldots,0.95$. This finite grid is not a uniform parameter proof.

## Triage

| Item | Status and evidence kind |
| --- | --- |
| External phase-shifted extension question, tier 1 | Literature reading: Sections 5.5–5.6 of arXiv:2602.03605v1 and preregistration #18759. Literature completeness is `ASSUMED-UNVERIFIED`. |
| Refutation under the binding conventions | Kernel-checked: `result`, at the single witness $s=3/5$. |
| Single settling module and its Scribe | Delivered: the named module and its Blueprint mirror; no supporting module or published owner is required. |
| Judge changes required | None: the delivery changes mathematical content and its documentation only. |
| Mathematical failure found | None in the accepted kernel certificate; the falsifier above states what would defeat the certificate. |
| Range $1/3\le s^2<1$ | Proved in prose below, using the displayed parity block decomposition; not a Lean theorem of this module. |
| Numerical violation at $s=0.55$ | Computed by the pinned experiment on the stated finite grid. |
| Phase-shifted Conjecture 1 | Literature reading reported in #18759: Wei, arXiv:2609.26802v2, Appendix E, refutes the unphased statement on a six-vertex tree, which also supplies zero phases. This secondary report has not been independently re-read here and is `ASSUMED-UNVERIFIED`. |
| Phase-shifted Conjecture 3, gap bound $1-s^2$ | Open in this delivery; no comparison with that bound is asserted. |

### What the settlement shows

**Kernel-checked instance.** The second full eigenvalue is strictly below the odd-sector minimum for the specified $\pi$-flux four-cycle at $s=3/5$. In particular the universal phase-shifted extension is false. Simplicity and exact spectral ordering are not extra Lean conclusions.

**Proved in prose: parameter range and mechanism.** Put $t=s^2$ and $d=1+t$, with $1/3\le t<1$. For $K=-H$, let $a=|1100\rangle$, $b=|0110\rangle$, $c=|0011\rangle$, $e=|1001\rangle$, $u=(a+b+c-e)/2$ and $v=(a-b+c+e)/2$. The remaining two weight-two vectors are $(a-c)/\sqrt2$ and $(b+e)/\sqrt2$. In the orthonormal basis $(|0000\rangle,u,|1111\rangle,v,(a-c)/\sqrt2,(b+e)/\sqrt2,|1010\rangle,|0101\rangle)$, applying the four local interactions gives the even block
$\begin{pmatrix}4&2s\\2s&d\end{pmatrix}\oplus\begin{pmatrix}4t&2s\\2s&d\end{pmatrix}\oplus dI_2\oplus0I_2$.
In suitable signed weight-one and weight-three bases the odd block is $\begin{pmatrix}2I_4&sM\\sM&2tI_4\end{pmatrix}$, where
$M=\begin{pmatrix}0&1&0&-1\\1&0&1&0\\0&1&0&1\\-1&0&1&0\end{pmatrix}$ and multiplication gives $M^2=2I_4$.
Thus the even eigenvalues are $\alpha_\pm=(5+t\pm\sqrt{(1+t)(9+t)})/2$, $\beta_\pm=(1+5t\pm\sqrt{(1+t)(1+9t)})/2$, $d,d,0,0$, and the odd eigenvalues are $\omega_\pm=1+t\pm\sqrt{1+t^2}$, each four times.

For this range, $(1+t)(9+t)-(1+t)(1+9t)=8(1+t)(1-t)>0$, so $\alpha_+>\beta_+$. The two lower even roots are below $d$ because each two-by-two block has nonzero off-diagonal entry; also $\beta_+>d>0$. Finally $(1+t)(1+9t)-4(1+t^2)=5t^2+10t-3\ge8/9>0$ and $3t-1\ge0$, so $\beta_+>\omega_+$. Consequently $\alpha_+$ and $\beta_+$ are the simple largest and second-largest eigenvalues of $K$, and the second eigenvalue of $H$ lies in the even sector strictly below the odd minimum throughout $1/3\le s^2<1$. These are algebraic consequences of this block decomposition, not additional frozen declarations.

The flux makes the two even coupling channels orthogonal. The computed zero-phase control shows that this graph at $s=0.6$ can satisfy the original parity equality. The original zero-phase Conjecture 2 and the phase-shifted gap conjecture remain open in this delivery. No unconditional theorem of the source is invalidated: conclusions conditional on the phase-shifted extension of Conjecture 2 cannot use that assertion for arbitrary phases.

## ASSUMED-UNVERIFIED

Literature completeness and priority beyond the primary source and the screen recorded in #18759 are `ASSUMED-UNVERIFIED`. The report concerning Wei's Conjecture 1 counterexample is attributed to that screen. The parameter argument is a prose proof; the frozen Lean certificate establishes the single refuting instance and the negation of `claim`.
