---
slug: barriga-2026-dft-ten-mode-edge-bound
bibkey: barriga2026dftbosonic
doi: null
url: https://arxiv.org/abs/2609.05644
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result
---

# A 23-edge coupling realizes the ten-mode Fourier transform

## Problem

Barriga et al., *N-dimensional discrete Fourier transform via bosonic
Hamiltonian*, arXiv:2609.05644v1, realize the discrete Fourier transform $F_N$
with a single waveguide array, $\Phi^{\rm out}e^{-i\mathcal C}\Phi^{\rm in}=F_N$.
The third conjecture of §III.D states that the remaining solutions for
non-prime $N$ have between $N\ell/2$ and $|E(K_{N-1})|-\ell$ edges, and the
same section fixes $\ell=5$ for $N=10$:

> Third, all the other possible solutions for non-prime $N$ are in the
> following range of edges
> $\lvert E(R_{\ell})\rvert \leq \lvert E\rvert < \lvert E(K_{N-1})\rvert-\ell$

Issue #13297 fixes the reading, taking the most restrictive notion of solution.
`claim`: every real symmetric $10\times10$ coupling matrix with nonnegative
off-diagonal entries, connected support, and diagonal unimodular phases
$\Phi^{\rm out},\Phi^{\rm in}$ with $\Phi^{\rm out}e^{-iH}\Phi^{\rm in}=F_{10}$
has at least 25 edges. The propagator is the frozen
`ProjectionProbabilityFlow.hamiltonianPropagator`.

## Motivation

The edge ranges guide the authors' numerical search over coupling graphs, which
grows to about $10^9$ graphs for $N=11$. A false lower bound would discard
sparse designs.
`D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result` proves
that the bound fails for $N=10$.

## Gap

Issue #13297 records the literature check. The paper has a single version and
no citing work was found. The authors report four 5-regular solutions (25
edges) and none sparser. A Good–Thomas realization
$F_{10}\cong F_2\otimes F_5$ with a complete-graph $F_5$ has exactly
$5+2\cdot10=25$ edges, which is not below the bound.
`not-found-in-searched-scope`.

## Route

1. **Five-mode circulant.** Let $s=\sqrt5$, $a=\pi(35-13s)/25$,
   $b=\pi(35+13s)/25$, and let $C_0$ be the symmetric circulant on
   $\mathbb Z_5$ with $a$ at distance 1 and $b$ at distance 2. Its Fourier
   eigenvalues are $28\pi/5,-4\pi,6\pi/5,6\pi/5,-4\pi$, and
   $(e^{-iC_0})_{jk}=(\omega_5/\sqrt5)\,\omega_5^{4(j-k)^2}$ with
   $\omega_5=e^{2\pi i/5}$.
2. **Rank-one $2\pi$ shift.** With $q=(21s-65)/20$, $\gamma=q+i\sqrt{1-q^2}$
   and $P_{jk}=\tfrac15\big(\operatorname{Re}(\gamma\omega_5^{j+k-1})+\cos
   \tfrac{2\pi(j-k)}5\big)$, $P$ is a rank-one projector onto a vector of the
   $-4\pi$ eigenspace. So $K=C_0+2\pi P$ commutes with $C_0$, and
   $e^{-iK}=e^{-iC_0}e^{-2\pi iP}=e^{-iC_0}$. The choice of $q$ makes
   $K_{01}=0$; all other off-diagonal entries of $K$ are positive.
3. **Ten modes.** Under $x\mapsto(x\bmod2,x\bmod5)$,
   $H=(\pi/4)X\otimes I_5+I_2\otimes K$. Then
   $e^{-iH}=\omega_5DF_{10}D$ with $D=\operatorname{diag}((-i)^{x\bmod2}
   \omega_5^{4(x\bmod5)^2})$, by the identity $5ab+4jk\equiv-xy\pmod{10}$.
4. **Count.** The support of $H$ is the cliques on the even and on the odd
   vertices minus $\{0,6\}$ and $\{1,5\}$, plus the matching $\{x,x+5\}$:
   $9+9+5=23$ edges, connected, with nonnegative couplings.

## Falsifier

The proof would fail if $P$ were not idempotent or did not commute with
$C_0$, or if $K_{01}$ were not exactly zero.

## Evidence

The canonical source is
`D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.lean`.
Its public declarations are `F10`, `edgeCount`, `supportGraph`,
`IsUnimodularDiagonal`, `claim` and `result`; the coupling matrix and the
exponential identities are private. Its direct frozen dependency is
`D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator`
(`sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb`).
The frozen module state has statement identity
`sha256:48af97a89b3fcb5bf779d67b1b6c1e920844bf168ef0adb135dba0605a3fe714`.
The result declaration has statement identity
`sha256:3b91d5e4ac703d3d8891b85de29efd1f90b30db6dfec6ccb039da952da746518`.
The Freeze event is
`sha256:1312c3a15e46ff4689f11d85a0fd2ca5a39fd13fdea96634a2ad4140094f7cea`.
Its project-level frozen prerequisite is
`sha256:890d665ee397056086d1f0182c51fc425f698af5b1aed0a36f13e2fd5b2b9f54`.
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Numerical check (issue #13297): $\max|e^{-iH}-\omega_5DF_{10}D|=1.9\cdot10^{-15}$;
perturbing one coupling by 0.01 raises it to $1.4\cdot10^{-3}$.

## Triage

Tier 1 external named conjecture (§III.D of a 2026 paper), preregistered in
issue #13297 before any Lean. `theorem`; resolution `refuted`. The public
theorem has `proof_shape: content`; its escape witness is the exact
exponential identity for the rank-one-shifted coupling. Admission basis
`open-problem-resolution`; utility `certified-instance` with `refutes`.

What the refutation shows beyond the single bound:

- **Mechanism (proved here for $K$; the general fact is standard).** A propagator $e^{-iH}$ determines $H$ only up to
  adding $2\pi$ times projectors inside eigenspaces of $H$. When an eigenvalue
  is repeated, such a shift can move the support of $H$. The edge count of a
  coupling graph is therefore not an invariant of the realized transform, and
  edge bounds based on the number of variables need not hold.
- **Factorized constructions (argued, not formalized).** For coprime
  $N=mn$, the Good–Thomas factorization gives $H=H_m\otimes I+I\otimes H_n$
  with edge count $n|E_m|+m|E_n|$. Any reduction in a factor's realization
  therefore propagates.
- **Further reductions (open).** The eigenspaces $t=1,4$ and $t=2,3$ of $C_0$
  each admit further shifts. Whether more edges of $K$ can be removed at once,
  or whether $F_5$ itself has a realization with fewer than 9 edges and exact
  phases, is not checked. The authors report a 5-edge cycle realization of
  $F_5$ found numerically. An exact version of it would give
  $5+2\cdot5=15$ edges for $N=10$; this is not verified here.
- **Effect on the paper.** The first two conjectures assert that every graph
  in a range of edges realizes the transform, and are unaffected. The third
  conjecture's lower bound fails for $N=10$; its upper bound is not tested.
  The physical-admissibility and tolerance analysis of §III.E is not addressed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
