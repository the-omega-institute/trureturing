---
slug: klausen-2025-lattice-lindbladian-zero-spectrum
bibkey: klausen2025spectragenerators
doi: 10.48550/arXiv.2206.09879
url: https://arxiv.org/abs/2206.09879v3
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.result
---

# Zero belongs to the spectrum of a finite-range translation-invariant lattice Lindbladian

## Problem

Frederik Ravn Klausen, *Spectra of generators of Markovian evolution in the thermodynamic limit: From non-Hermitian to full evolution via tridiagonal Laurent matrices*, arXiv:2206.09879v3 (2025), asks in “Further questions” (`section04.tex`, line 574; verbatim TeX):

> Prove that if $\Li$ is \eqref{eq:finite-range}, \eqref{eq:translation-invariance}, and  \eqref{eq:Rank1} then $0 \in \sigma(\Li)$, thereby strengthening \Cref{thm:no_gap}.

Here the source macro `\Li` denotes $\mathcal L$, the three assumption labels mean (Finite Range), (TransInv), and (Rank 1), and the theorem label is `thm:no_gap`. The source assumes bounded self-adjoint $H$ and $G>0$; (Rank 1) means $\operatorname{rank}(L_k)=1$ for every $k\in\mathbb Z$ (`section02.tex`, lines 12 and 50). It takes $\mathcal L$ on $\mathrm{HS}(\ell^2(\mathbb Z))$ (`section02.tex`, lines 6–13 and 54–57). Its theorem (`section03.tex`, lines 506–509) reads:

> If $\Li$ is \eqref{eq:finite-range}, \eqref{eq:translation-invariance},  \eqref{eq:Rank1} and $0 \in \sigma(\Li)$.
> Then $\Li$ is gapless or $\dim(\ker(\Li))=\infty.$

Issue [#23482](https://github.com/the-omega-institute/trureturing/issues/23482) fixes the matrix-kernel reading. Put $E=\ell^2(\mathbb Z\times\mathbb Z;\mathbb C)$, the module's `ObserverHilbertSpace (ℤ × ℤ)`. For every $r\in\mathbb N$, every $g\in\mathbb R$, every $h:\mathbb Z^2\to\mathbb C$, and every $\ell:\mathbb Z^3\to\mathbb C$, assume:

- `IsFiniteRange r h ℓ`: $h(x,y)=0$ whenever $|x-y|>r$, and $\ell(k,x,y)=0$ whenever $\max\{|x-k|,|y-k|\}>r$;
- `IsTranslationInvariant h ℓ`: $h(x+1,y+1)=h(x,y)$ and $\ell(k+1,x+1,y+1)=\ell(k,x,y)$ for all integer indices.

The conclusion of `result` is that there exists a continuous complex linear operator $T:E\to E$ such that, for every $\rho\in E$ and every $x,y\in\mathbb Z$, $(T\rho)(x,y)=\operatorname{lindbladEntry}(g,h,\ell,\rho,x,y)$, and $0\in\sigma_{\mathbb C}(T)$. Explicitly, the entry is

$$
\begin{aligned}
&-i\left(\sum_z h(x,z)\rho(z,y)-\sum_z\rho(x,z)h(z,y)\right)\\
&\quad+g\sum_k\left[
\sum_u\sum_v\ell(k,x,u)\rho(u,v)\overline{\ell(k,y,v)}
-\frac12\sum_z\left(\sum_w\overline{\ell(k,w,x)}\ell(k,w,z)\right)\rho(z,y)
-\frac12\sum_z\rho(x,z)\left(\sum_w\overline{\ell(k,w,z)}\ell(k,w,y)\right)
\right].
\end{aligned}
$$

All indices in these sums range over $\mathbb Z$; the Lean definition uses unconditional sums, whose nonzero terms are finite under `IsFiniteRange`. The theorem imposes no rank condition on the jumps, no self-adjointness condition on $h$, and no sign condition on $g$. Its specialization to $g>0$ and self-adjoint $h$ answers the registered question, including its rank-one case.

## Motivation

The missing spectral-membership premise is exactly the premise in Klausen's `thm:no_gap` that is additional to the three structural assumptions. Settling it makes the source's gapless-or-infinite-kernel alternative applicable to every generator in that rank-one class. The operator space matters: spectral information on Hilbert–Schmidt kernels does not automatically transfer to trace-class operators or to all bounded operators.

## Gap

Issue #23482 records the orchestrator's bounded literature check before any Lean:

- the v3 source explicitly retains the question;
- its Semantic Scholar search returned one citing work, Julian Lyne, Nico S. Bassler, Seong eun Park, Guido Pupillo and Claudiu Genes (2023), arXiv:2311.04129, and recorded no treatment of this question there;
- its arXiv and related-paper checks recorded no journal reference for the source and no settlement in Frederik Ravn Klausen and Simone Warzel (2025), *Decoherence is an echo of Anderson localization in open quantum systems* (the source bibliography's `klausen2025decoherence`), or Yikang Zhang and Thomas Barthel (2025), arXiv:2504.02256;
- its web and Zenodo searches found no settlement, and its repository searches found no existing record.

`not-found-in-searched-scope`.

The question and the source passages cited here are checked against the v3 TeX. The other searches and paper readings are attributed to the orchestrator's record in #23482; they are not an exhaustive literature or priority claim.

## Route

Throughout, $r\in\mathbb N$, $g\in\mathbb R$, $h:\mathbb Z^2\to\mathbb C$, and $\ell:\mathbb Z^3\to\mathbb C$ have the types specified in Problem. The lemmas named below are private helpers of the canonical module.

1. **Bounded realization.** Under `IsFiniteRange r h ℓ` and `IsTranslationInvariant h ℓ`, `bounded_operator` constructs a continuous complex linear $T:E\to E$ with the specified entries for all $\rho\in E$ and $x,y\in\mathbb Z$. Under these same two hypotheses, `matrix_bound` supplies a common nonnegative bound on all entries of $h$ and $\ell$. Under `IsFiniteRange r h ℓ`, for every $\rho\in E$ and $p\in\mathbb Z^2$, `finite_window` expands the output at $p$ as a sum of $c_w(p)\rho(p+w)$ over $w\in[-2r,2r]^2\cap\mathbb Z^2$, where $c_w(p)$ is `coefficient g h ℓ w p`, the output at $p$ on the matrix-unit kernel at $p+w$. Under both predicates, `coefficient_bound` gives a real $m\ge0$ with $|c_w(p)|\le m$ for all $w,p\in\mathbb Z^2$. For any $w\in\mathbb Z^2$, $c:\mathbb Z^2\to\mathbb C$, and $m\in\mathbb R$ with $m\ge0$ and $|c(p)|\le m$ for every $p$, `weighted_shift_exists` realizes $\rho(p)\mapsto c(p)\rho(p+w)$ by a continuous complex linear operator of norm at most $m$; the finite sum gives $T$.
2. **Localized trace.** For each $n\in\mathbb N$, `projection n` is the kernel $P_n$ equal to one at $(x,x)$ for $-n\le x\le n$ and zero elsewhere. For every $n\in\mathbb N$ and $\rho\in E$, `projection_trace` gives $\langle P_n,\rho\rangle=\sum_{x=-n}^n\rho(x,x)$, and `projection_norm_sq` gives $\|P_n\|^2=2n+1$. Under `IsFiniteRange r h ℓ`, for every $u,v\in\mathbb Z$, `trace_single_zero` gives $\sum_x\operatorname{lindbladEntry}(g,h,\ell,e_{uv},x,x)=0$, where $e_{uv}$ is the matrix-unit kernel. The commutator terms cancel and the jump gain cancels the two half losses, with all relevant sums finite.
3. **Boundary estimate.** Under `IsFiniteRange r h ℓ` and `IsTranslationInvariant h ℓ`, `boundary_estimate` gives a real $K\ge0$ such that, for every $n\in\mathbb N$ and $\rho\in E$, $|\sum_{x=-n}^n\operatorname{lindbladEntry}(g,h,\ell,\rho,x,x)|\le K\|\rho\|$. In its proof, the coefficient of $\rho(u,v)$ in this restricted trace vanishes unless $u$ is within $2r$ of one of $-n,n$ and $|v-u|\le4r$; there are at most $2(4r+1)(8r+1)$ such pairs, independently of $n$. This counts a containing boundary set and does not require its two endpoint intervals to be disjoint.
4. **Spectral obstruction.** For any continuous complex linear $T:E\to E$ satisfying $|\langle P_n,T\rho\rangle|\le K\|\rho\|$ for some real $K\ge0$, every $n\in\mathbb N$, and every $\rho\in E$, `nonunit_from_boundary` concludes that $T$ is not a unit. Indeed, a bounded inverse $S$ would give $\|P_n\|^2\le K\|S\|\|P_n\|$, hence $\sqrt{2n+1}\le K\|S\|$ for all $n$, a contradiction. `result` uses the entry identity and `projection_trace` to supply this hypothesis, then applies Mathlib's `spectrum.zero_mem_iff`.

## Falsifier

The settlement would miss the source question if its support, coupling, or spectral space differed from the registered reading.

- **Hamiltonian range.** The source's displayed (Finite Range), `section02.tex`, line 41, uses the jump index $k$ also in the condition on $H$. The registered reading makes the Hamiltonian banded, $h(x,y)=0$ for $|x-y|>r$, while retaining the source's jump-support condition exactly. This is an explicit interpretation of that display, not a literal transcription of its Hamiltonian clause.
- **Coupling.** The formal entry multiplies the whole dissipator by $g$. The unparenthesized display in `section02.tex`, line 10, is ambiguous on this point; the effective Hamiltonian at line 22 and the vectorized formula in `section03.tex`, lines 179–182, give this placement for the source's self-adjoint $H$ and $G>0$.
- **Space and spectrum.** The module works on the complex square-summable kernel space, and `spectrum ℂ T` is the spectrum in its algebra of continuous complex linear endomorphisms. The source's matrix-unit vectorization is at `section03.tex`, lines 162–165. Its identification with Hilbert–Schmidt operators and the resulting spectral transport are mathematical interpretation, not additional Lean conclusions of this module.
- **Strength.** Spectral membership is the conclusion. The theorem neither supplies a nonzero kernel vector nor distinguishes gaplessness from an infinite-dimensional kernel.

The definitions and source locators are also recorded in [the literature note](../Library/HilbertOperators/klausen2025spectragenerators.md).

## Evidence

The canonical source is `D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.lean`.

- **Proof.** It proves `result`, the quantified operator-existence and spectral-membership statement in Problem.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/LatticeLindbladianZeroSpectrum.lean.json`.

Declaration statements:

- `result`: `sha256:7cbf804f16076ba892b76f89a255123644185488090e98794644f806a98c3939`.

## Triage

Tier 1 question explicitly listed in the author's 2025 v3 preprint, preregistered in issue #23482 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural radius $r$, real coupling $g$, complex Hamiltonian matrix $h$ and complex jump-matrix family $\ell$ satisfying `IsFiniteRange r h ℓ` and `IsTranslationInvariant h ℓ`, there exists a continuous complex linear operator on $\ell^2(\mathbb Z\times\mathbb Z;\mathbb C)$ whose entries equal `lindbladEntry g h ℓ` for every input kernel and every pair of integer indices, and zero belongs to its complex spectrum.

**Computed, not formalized** (orchestrator, Claude Code/Opus, recorded in #23482): in finite truncations of the source's non-normal example and of one random range-two example, the Hilbert–Schmidt norm of $\mathcal L^\dagger(P_N)$ did not grow with $N$.

**Argued, not formalized.**

- *Hilbert–Schmidt interpretation.* The matrix units form an orthonormal basis of the Hilbert–Schmidt space, and the coordinate kernels form an orthonormal basis of $E$. Sending one basis to the other extends to a surjective linear isometry because both norms are the square root of the sum of squared matrix entries. Under finite range the matrix products give exactly the finite sums defining `lindbladEntry`. For the source's self-adjoint $H$ and positive $G$, this identifies the bounded realization with its Lindblad generator. Conjugating an operator and its inverse by this isometry preserves invertibility at each complex spectral parameter, so it preserves the spectrum.
- *Decisive mechanism and formal scope.* Under `IsFiniteRange r h ℓ` and `IsTranslationInvariant h ℓ`, `boundary_estimate` gives the uniform nonnegative constant $K$ for all $n$ and $\rho\in E$, while `projection_norm_sq` gives the growing norm for every $n\in\mathbb N$. Thus local trace cancellation at the boundary obstructs an inverse. The obstruction uses neither positivity, self-adjointness nor rank one; these hypotheses are absent from `result`. The identity kernel itself is outside $E$, since its squared norm would be $\sum_{x\in\mathbb Z}1$.
- *Why a stationary vector is stronger.* Consider $H=S+S^*$, where $S$ is the bilateral shift, $L_k=|\delta_k\rangle\langle\delta_k|$, and $g>0$. These matrices satisfy both formal predicates with $r=1$, and the generator is $T\rho=-i[H,\rho]+g(D\rho-\rho)$, where $D$ is the orthogonal projection onto diagonal kernels. Left and right multiplication by the bounded self-adjoint $H$ are self-adjoint on the Hilbert–Schmidt space, so the commutator term contributes zero to $\operatorname{Re}\langle\rho,T\rho\rangle$, while the dissipator contributes $-g\|\rho-D\rho\|^2$. Therefore $T\rho=0$ forces $\rho=D\rho$. Writing its diagonal as $f(x)$, the adjacent entries of $[H,\rho]$ force $f(x+1)=f(x)$ for every $x$; a constant square-summable sequence on $\mathbb Z$ is zero. Thus this example has no nonzero Hilbert–Schmidt stationary kernel despite spectral zero.
- *Effect on the paper.* For the source's finite-range translation-invariant rank-one class, the Hilbert–Schmidt interpretation supplies the spectral-membership premise in the quoted `thm:no_gap`. Applying that source theorem gives its gapless-or-infinite-dimensional-kernel alternative without an additional spectral-membership assumption. This application and the source theorem itself are not formalized here. Removing rank one from that alternative remains open in this settlement, as do the source's separate finite-volume gap-closing and spectral-convergence questions. No conclusion for $\mathbb Z^d$ with $d>1$, trace-class spectra, or spectra on all bounded operators is supplied.

## ASSUMED-UNVERIFIED

The literature check is bounded by the orchestrator's searches recorded in #23482 and does not establish exhaustive novelty or priority. The Semantic Scholar citation listing, web and Zenodo searches, repository searches, and readings of the related papers in that issue were not independently reproduced. The v3 TeX question, assumptions, vectorization, effective Hamiltonian and `thm:no_gap` were read directly; the arXiv abstract page supplies the arXiv-issued DOI, with no journal reference displayed.

The Hilbert–Schmidt isometry, transport of spectra, identification with the source generator under the registered support and coupling interpretations, stationary-kernel example, and application of the source's gapless-or-infinite-kernel theorem are not formalized in this module. The arguments and unresolved extensions in “Argued, not formalized” lie outside the type of `result`. The two finite numerical checks are the orchestrator's reported computations; neither was independently reproduced, the random example is not specified sufficiently in the issue for exact reproduction, and no infinite sequence or untested family is inferred from their tested values.
