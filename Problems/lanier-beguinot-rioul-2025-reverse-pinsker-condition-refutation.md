---
slug: lanier-beguinot-rioul-2025-reverse-pinsker-condition-refutation
bibkey: lanier2025maximal
doi: 10.48550/arXiv.2501.14340
url: https://arxiv.org/abs/2501.14340v1
triage: theorem
motivation_gids:
  - D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.result
---

# A qubit refutation of the maximal reverse Pinsker bound

## Problem

D. Lanier, J. Béguinot and O. Rioul, *From Classical to Quantum: Explicit Classical Distributions Achieving Maximal Quantum f-Divergence*, arXiv:2501.14340v1, §III-C, p. 5:

> We conjecture that (49) is in fact not necessary for (50) to hold.

The same paragraph states:

> Our bound holds in general for any f-divergence, in particular for the maximal f-divergence.

Section I specifies a convex real generator on the nonnegative half-line with $f(1)=0$. Equation (4) defines

$$
D_f^{\max}(\rho\Vert\sigma)
=\operatorname{Tr}\bigl(\sigma^{1/2}f(\sigma^{-1/2}\rho\sigma^{-1/2})\sigma^{1/2}\bigr).
$$

Theorem 4 assumes $|\rho-\sigma|\leq\rho+\sigma$ (49), and asserts

$$
D_f(\rho\Vert\sigma)\leq\frac{\|\rho-\sigma\|_1}{2}
\left(\frac{f(m)}{1-m}+\frac{f(M)}{M-1}\right),\tag{50}
$$

where $m,M$ are the extreme eigenvalues of $\sigma^{-1/2}\rho\sigma^{-1/2}$. Preregistration: [#19943](https://github.com/the-omega-institute/trureturing/issues/19943).

### Statement echo

| Source clause | Lean counterpart | Fidelity and scope |
| --- | --- | --- |
| Every finite dimension | `claim`: natural dimension and `Matrix (Fin n) (Fin n) ℂ` | Includes the qubit instance. |
| Convex real generator for nonnegative arguments, zero at one | `ConvexOn ℝ (Set.Ici 0) f`, `f 1 = 0` | Values outside the half-line do not affect the positive relative matrix. |
| States; invertible second state | `ρ.PosSemidef`, `ρ.trace = 1`, `σ.PosDef`, `σ.trace = 1` | Positive definiteness expresses an invertible positive state. |
| Equation (4) | `maxDivergence` | Literal relative-matrix expression and real part of the CFC trace. |
| Equation (50) | `reversePinskerBound` | Repository trace norm; real spectral infimum and supremum. The witness has nonzero denominators. |
| Remove condition (49) | `claim` | No absolute-difference order hypothesis. |
| Conditional printed assertion | private `claimTheorem4` | Adds exactly the matrix-order condition (49). |
| Refutation | public `result` | Negates the complete binding `claim`. |

The public formulas inline the source relative-matrix expression. The proof uses `D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence`, which has that expression, without introducing a duplicate definition. The library note is `Library/Divergence/lanier2025maximal.md`.

## Motivation

The maximal-divergence instance suffices to test the source's universal statement. The generator $f(x)=(x-1)^2$ is operator convex; its Definition 2 data-processing admissibility uses the Matsumoto theorem cited by the source. That literature premise is separate from the kernel-checked refutation of the spectral formula.

## Gap

Condition (49) does not identify maximal absolute-generator divergence with the trace norm. The same positive qubit pair violates the proposed inequality while satisfying (49), so imposing that condition does not repair the printed maximal-divergence statement.

## Route

Set

$$
\sigma=\begin{pmatrix}9/25&0\\0&16/25\end{pmatrix},\qquad
\rho=\begin{pmatrix}9/25&12/125\\12/125&16/25\end{pmatrix},\qquad f(x)=(x-1)^2.
$$

The private lemmas verify the state assumptions and evaluate Mathlib's matrix square root, inverse, real spectrum and continuous functional calculus. In particular,

$$
\sigma^{1/2}=\operatorname{diag}(3/5,4/5),\qquad
\sigma^{-1/2}\rho\sigma^{-1/2}
=\begin{pmatrix}1&1/5\\1/5&1\end{pmatrix},\qquad
\{m,M\}=\{4/5,6/5\}.
$$

## Falsifier

The private `divergence_eq`, `trace_norm` and `bound_eq` certify

$$
D_f^{\max}=\frac1{25}=\frac{25}{625},\qquad
\|\rho-\sigma\|_1=\frac{24}{125},\qquad
\operatorname{RHS}(50)=\frac{24}{625}.
$$

The private `condition_49` proves (49). Its matrix is

$$
\rho+\sigma-|\rho-\sigma|
=\begin{pmatrix}78/125&12/125\\12/125&148/125\end{pmatrix}.
$$

The private `theorem4_false` refutes the conditional assertion; `result` derives the negation of the unconditional conjecture. The strict gap is $1/625$.

## Evidence

The canonical module is `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation.lean`; its only public theorem is `result`. Its three public definitions are `maxDivergence`, `reversePinskerBound` and `claim`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

### Declaration judgement

| module | declaration | proof_shape | escape_witness | consumers | direct frozen dependencies |
| --- | --- | --- | --- | --- | --- |
| `D5/S3/Divergence/LanierBeguinotRioulReversePinskerRefutation` | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.result` (`sha256:7c29b604b6801d9787203df8296dcdf6954e0f1fa361f3a7ff620d546df26874`) | bind-only | none | designated settlement | `D5/S3/Quantum/Foundation/FiniteTraceDistance` + `D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm` + `sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059`<br>`D5/S3/Quantum/Matrix/SpectralPower` + `D5.S3.Quantum.Matrix.SpectralPower.posDef_two` + `sha256:aab0c093aa3d2b2ec35e668b9050f590c2f79cbaf6d347b59632a1280bc73376`<br>`D5/S3/Resource/LogDet/PathSpectralClassical` + `D5.S3.Resource.LogDet.PathSpectralClassical.relativeCongruence` + `sha256:0355622d27d9d0fc4cad0f3d1700e9456d0d9e7ecfb087fd94aff70911218c61` |

Admission basis: `open-problem-resolution (#19943; Refuted)`. The proof steps are `bind-only`; the certified instance settles the preregistered external named conjecture. The helper map below is derived from compiled constant dependencies; names denote source declarations in this module.

| helper (full name) | proof_shape | direct consumer(s) |
| --- | --- | --- |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.claimTheorem4` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sigma` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_sigma`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sigma_trace`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.delta_square`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_delta`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.trace_norm`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.condition_49`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inf_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sup_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rho` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rho_psd`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rho_trace`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.delta_square`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_delta`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.trace_norm`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.condition_49`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inf_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sup_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.root` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.root_nonneg`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_sigma`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inv_root`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.root_inv` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inv_root`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rel` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rel_sa`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.spectrum_rel`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inf_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sup_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.cfc_rel`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.delta_abs` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.delta_square`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_delta`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.trace_norm`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.condition_49` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.f` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.cfc_rel`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sigma_pos` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.root_nonneg` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_sigma` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_sigma` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inv_root` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.relative_eq` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inf_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sup_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rho_psd` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rho_trace` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sigma_trace` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.delta_square` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_delta` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.delta_abs_nonneg` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_delta` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sqrt_delta` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.abs_delta`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.trace_norm` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.abs_delta` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.condition_49` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.trace_norm` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.condition_49` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.rel_sa` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.cfc_rel` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.spectrum_rel` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inf_spectrum`, `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sup_spectrum` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.inf_spectrum` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.sup_spectrum` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.cfc_rel` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.divergence_eq` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.bound_eq` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.f_convex` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` |
| `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.theorem4_false` | bind-only | `D5.S3.Divergence.LanierBeguinotRioulReversePinskerRefutation.result` |

### Experiment

[Published numerical checker](https://github.com/the-omega-institute/trureturing-experiments/tree/ec0476c9a5059125ae488f65fef099ec30b5c335/docs/reports/lanier-beguinot-rioul-2025-reverse-pinsker-condition-49), script `check.py`, SHA-256 `d59f200ed130c0b8567fd55232471d9c118a235cd2da37c672b6b0c7dfeef999`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/lanier-beguinot-rioul-2025-reverse-pinsker-condition-49/check.py`; exit 0. The executed script has exactly the pinned bytes.

Computed scope: exact rational arithmetic at $a=9/25,t=12/125$ gives $m=4/5$, $M=6/5$, divergence $1/25$, trace norm $24/125$, proposed bound $24/625$, $\det\rho=3456/15625$, and determinant $456/625$ for the (49) matrix. The nine floating-point pairs $a\in\{0.6,0.75,0.9\}$, $t\in\{0.02,0.1,0.2\}$ have divergence/bound ratios approximately $1.0206,1.1547,1.6667$, respectively; only $a=0.9,t=0.2$ fails (49). The seeded samples each contain 2000 dimension-four pairs: Hilbert–Schmidt sampling gives 33 satisfying (49), 355 violating (50), and 3 doing both; Haar eigenbasis with normalized uniform eigenvalues gives 1582 satisfying (49) and 51 doing both. These finite samples do not establish a universal frequency or identify the source's unspecified sampler.

## Triage

### What the settlement shows

1. **Proved — kernel-checked settlement.** `result` refutes the exact binding conjecture. The private `theorem4_false` refutes the printed conditional maximal-divergence assertion on the same pair. No assertion about all downstream results follows solely from these negations.

2. **Proved — kernel-checked mechanism for the instance.** `condition_49`, `divergence_eq` and `bound_eq` certify the order hypothesis and the incompatible values $25/625$ and $24/625$. The normalization of the quantum total variation is too small for the proposed maximal-divergence bound on this pair.

3. **Proved in prose — where the printed argument fails.** The relative matrix has normalized eigenvectors $(1,\pm1)/\sqrt2$. Each has $\sigma$-weight $s_i=1/2$. Thus $r_i=\lambda_i s_i$ gives $r=(2/5,3/5)$, $s=(1/2,1/2)$, classical total variation $1/10$, and maximal $g(x)=|x-1|$ divergence $\sum_i s_i|\lambda_i-1|=1/5$. The quantum total variation is $12/125<1/10$, and $\|\rho-\sigma\|_1=24/125<1/5$. Hence (49) does not imply the equality used in the source's citation to [7, Eq. (64)]. These explanatory identities are not additional Lean theorems.

4. **Proved in prose — a surviving bound.** For a nontrivial spectral interval $m<1<M$, convexity and $f(1)=0$ bound $f(x)$ by $f(m)(1-x)/(1-m)$ on $[m,1]$ and by $f(M)(x-1)/(M-1)$ on $[1,M]$. In the classical spectral representation, $\sum_i s_i\lambda_i=\sum_i s_i=1$, so the positive and negative deviation sums both equal $D_g^{\max}/2$. Summing the two chord inequalities proves (50) with the trace norm replaced by $D_g^{\max}$. Therefore the printed bound follows under the actual equality $D_g^{\max}=\|\rho-\sigma\|_1$. Commuting states have this equality by simultaneous diagonalization. This is a prose derivation, not an additional formal theorem.

5. **Proved in prose — family boundary.** For $0<a<1$, $q=a(1-a)$, $0<t<\sqrt q$, set $\sigma=\operatorname{diag}(a,1-a)$ and $\rho=\sigma+tX$. The relative eigenvalues are $1\pm t/\sqrt q$. For $f(x)=(x-1)^2$, squaring the off-diagonal relative difference gives $D_f^{\max}=t^2/q$; the trace norm is $2t$ and the proposed right side is $2t^2/\sqrt q$. The ratio is $1/(2\sqrt q)>1$ if $a\ne1/2$. The (49) matrix has trace $2-2t>0$ and determinant $4q-2t$, so (49) is equivalent to $t\le2q$. This derivation gives a family of failures; the Lean module certifies the single rational pair only. The experiment covers exactly the finite scope in its entry.

6. **Open — downstream constants.** Recheck the exact constant wherever printed Theorem 4 is used, including arXiv:2605.06452v1, Lemma 4 (Tan, George and Tomamichel). The preregistration's literature reading records a local regime with constants absorbed into $\lesssim$; this delivery does not settle that paper's downstream conclusions. The source's bound (53) for the hockey-stick divergence is a different divergence and is not refuted by this maximal-divergence instance.

7. **Proved — certified instance and declaration scope.** The module is admitted as `open-problem-resolution (#19943; Refuted)`, with `generality: I` and `utility: kind=certified-instance; basis=refutes`. The theorem judgement is `bind-only`, with no escape witness claimed. Every private helper has a compiled consumer.

8. **Proved — registration scope.** The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). All other theorems remain private; there are no other public audit targets.

9. **Computed — finite experiment scope.** The pinned `check.py` entry computes the exact rational witness, the nine pairs $a\in\{0.6,0.75,0.9\}$ and $t\in\{0.02,0.1,0.2\}$, and two seeded samples of 2000 dimension-four pairs. The nine pairs give divergence/bound ratios approximately $1.0206,1.1547,1.6667$, respectively; only $(a,t)=(0.9,0.2)$ fails (49). Hilbert–Schmidt sampling gives 33 satisfying (49), 355 violating (50), and 3 doing both; Haar eigenbasis with normalized uniform eigenvalues gives 1582 satisfying (49) and 51 doing both. The experiment entry gives the command, exit 0, pinned commit and script SHA-256. These finite readings establish no universal frequency.

10. **Open — literature completeness.** The preregistration records arXiv:2501.14340v1 and arXiv:2605.06452v1. The QIP paper DOI `10.1007/s11128-026-05309-8` was not read. Completeness and originality are `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Global prior-art completeness and originality. The Definition 2 data-processing admissibility of the maximal spectral expression for the operator-convex generator uses the source's Matsumoto theorem; this general theorem is not machine-checked here. The family and surviving-bound derivations are prose mathematics, distinct from the single kernel-checked instance. Downstream conclusions of arXiv:2605.06452v1 remain open.
