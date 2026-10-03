---
slug: bai-2007-residual-sum-monotone
bibkey: bai2007multipartite
doi: 10.1103/PhysRevA.76.022336
url: https://arxiv.org/abs/quant-ph/0703098v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result
---

# Monotonicity of the residual-correlation sum of four qubits

## Problem

Y.-K. Bai, D. Yang, Z. D. Wang, *Multipartite quantum correlation and
entanglement in four-qubit pure states*, Phys. Rev. A 76, 022336 (2007),
arXiv:quant-ph/0703098v2:

> Nevertheless, we conjecture that the correlation $M$ is an entanglement
> monotone

Here $M=\sum_k\tau_k-2\sum_{p>q}C_{pq}^2$ (Eq. (7)) for a four-qubit pure
state, with the linear entropies $\tau_k=2(1-\mathrm{tr}\,\rho_k^2)$ of the
one-qubit reduced states and Wootters' concurrences
$C_{pq}=\max(\sqrt{\lambda_1}-\sqrt{\lambda_2}-\sqrt{\lambda_3}-\sqrt{\lambda_4},0)$
of the six two-qubit reduced states, $\lambda_1\ge\dots\ge\lambda_4$ the
eigenvalues of $\rho_{pq}(\sigma_y\otimes\sigma_y)\rho_{pq}^\ast(\sigma_y
\otimes\sigma_y)$. An entanglement monotone does not increase on average
under LOCC; in particular, for every local instrument $\{K_j\}$ on one qubit,
$\sum_jp_jM(\phi_j)\le M(\psi)$, where $p_j=\|K_j\psi\|^2$ and
$\phi_j=K_j\psi/\sqrt{p_j}$.

## Motivation

A monotone $M$ would make $E_{ms}=M/4$ a computable measure of the
multipartite entanglement per qubit of four-qubit pure states, and the
$N$-qubit analogue $M_N/N$ a measure for $N$ qubits; the paper also proposes
to use $E_{ms}$ to rule out LOCC transformations that would increase it.
The frozen declaration
`D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result`
shows that $M$ can increase on average under a two-outcome measurement on
one qubit.

## Gap

Issue #12466 classifies the conjecture as Tier 1 and records the checks made
before any Lean:

- arXiv:quant-ph/0703098 v2 is the latest version and states the
  conjecture, supported by an argument that two components of $M$ decrease
  enough to compensate the third and by the average change of $M$ for nine
  representative states under diagonal POVMs on one qubit;
- Bai–Wang, arXiv:0709.4642v3 (Phys. Rev. A 77, 032313 (2008)), prove the
  monotonicity for cluster-class states and call the general case open;
  Bai–Ye–Wang, arXiv:0806.2017v2 (Phys. Rev. A 78, 062325 (2008)), and Park,
  arXiv:1801.07846v1, keep it as a conjecture;
- the paper's own counterexamples concern the single residuals $M_k$, which
  are not monotone, not their sum; Eltschka–Osterloh–Siewert
  (arXiv:0904.1034) and Bai–Xu–Wang (arXiv:1401.3205) treat different
  quantities.

These are seat-reported and orchestrator-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $\psi=(20|0001\rangle+2|1000\rangle+6|1011\rangle+|1110\rangle)/21$ and
   the instrument $K_0=\mathrm{diag}(21/29,0)$, $K_1=\mathrm{diag}(20/29,1)$
   on qubit $A$, with $K_0^\dagger K_0+K_1^\dagger K_1=I$. Then
   $p_0=400/841$ with $\phi_0=|0001\rangle$, and $p_1=441/841$ with
   $\phi_1=(400|0001\rangle+58|1000\rangle+174|1011\rangle+29|1110\rangle)/441$.
2. Every two-qubit reduced state of $\psi$, $\phi_0$ and $\phi_1$ is a real X
   matrix: diagonal $u,v,r,s$ in the basis $00,01,10,11$, an entry $w$
   between $00$ and $11$ and an entry $z$ between $01$ and $10$. For such a
   matrix, $\rho(\sigma_y\otimes\sigma_y)\rho^\ast(\sigma_y\otimes\sigma_y)$
   has characteristic polynomial
   $(X^2-2(us+w^2)X+(us-w^2)^2)(X^2-2(vr+z^2)X+(vr-z^2)^2)$, hence
   eigenvalues $(\sqrt{us}\pm|w|)^2$ and $(\sqrt{vr}\pm|z|)^2$; sorting them
   gives the concurrence $2|w|$, $2|z|$ or $0$ in the cases that occur.
3. The concurrences of the pairs $AB,AC,AD,BC,BD,CD$ are
   $(0,240,80,4,12,0)/441$ for $\psi$,
   $(0,139200,46400,3364,10092,0)/194481$ for $\phi_1$, and $0$ for $\phi_0$;
   with the one-qubit linear entropies,
   $M(\psi)=7552/194481$, $M(\phi_0)=0$ and
   $M(\phi_1)=2967747712/37822859361$.
4. $p_0M(\phi_0)+p_1M(\phi_1)=3528832/85766121$ exceeds
   $M(\psi)=7552/194481$ by $198400/85766121$.

## Falsifier

The kernel-checked `result` is the negation of the statement that for every
four-qubit vector $\psi$ with $\sum_w|\psi(w)|^2=1$ and every finite family
$K_0,\dots,K_{n-1}$ of $2\times2$ complex matrices with
$\sum_jK_j^\dagger K_j=I$, acting on qubit $A$, the sum over $j$ of
$p_jM(\phi_j)$ (omitting the outcomes with $p_j=0$) is at most $M(\psi)$.
The reduced states are the frozen `PurityTimeReversalOverlapMinimum.reducedState`,
$(\sigma_y\otimes\sigma_y)\rho^\ast(\sigma_y\otimes\sigma_y)$ is the
frozen `timeReversed` on the pair, and $K_j$ acts on qubit $A$ as the frozen
`StabilizerPairLocalUnitaryInequivalence.localOp 0 (K j)`; the eigenvalues are
the real parts of the roots, with multiplicity, of the characteristic
polynomial, sorted decreasingly, and $\mathrm{tr}\,\rho_k^2$ enters through
its real part. For density matrices these agree with the paper's quantities,
since $\rho_k^2$ has real trace and $\rho(\sigma_y\otimes\sigma_y)\rho^\ast
(\sigma_y\otimes\sigma_y)$ has nonnegative real eigenvalues; inside the proof
of `result` the roots are computed exactly for the three states used. A local
instrument on one qubit is a one-step LOCC protocol, so the failure refutes
the conjecture.

## Evidence

Exact recomputation (SymPy, issue #12466): the partial traces, the products
$\rho(\sigma_y\otimes\sigma_y)\rho^\ast(\sigma_y\otimes\sigma_y)$, their
eigenvalues, the concurrences, the linear entropies, $M$ and the averages
above; the literature seat recomputed a first counterexample of the same
family independently.

The canonical source is
`D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.lean`.
Its public declarations are `linearEntropy`, `concurrence`, `residualSum`,
`claim`, `psi`, `instrument` and `result`; the partial traces and the time
reversal are frozen in
`D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum`, the partial
trace over the second factor in
`D5/S3/Quantum/Information/PartialTraceMutualInformation`, and the
single-qubit operator `localOp` in
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`.
The frozen module state has statement identity
`sha256:00c982b5bcada21cd382a329e018c76bb956a89e7e2f3238561fc61111828a03`. The
result declaration has statement identity
`sha256:348ca75622d24ba1be6771830ba3706601aa14f655a8a0c927034b382b3f3877`. The
Freeze event is
`sha256:341d148480aca74c188abee69fdf7f9f12bc563aac330d6ac9b435dcc97ff517`; its
project-level frozen prerequisites are the Freeze events of
`D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum` and
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`.
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2007 journal article; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/FourQubitResidualSumMonotoneRefutation.result`.
`proof_shape: bind-only` (the settlement of the named conjecture is the new
content; no escape witness); `admission_basis: open-problem-resolution`
(issue #12466). Utility kind `certified-instance`, basis `refutes` the
module's `claim`.

### What the settlement shows

- **Proved by `result`:** the conjecture fails: some normalized four-qubit
  state and some complete instrument on qubit $A$ raise the average of $M$.
- **Proved inside the proof of `result`, for these states only:** the
  witness is the four-term state $\psi$ with the two-outcome diagonal
  measurement $K_0=\mathrm{diag}(21/29,0)$, $K_1=\mathrm{diag}(20/29,1)$ on
  qubit $A$; the values of the four linear entropies and the six concurrences
  of $\psi$, $\phi_0$ and $\phi_1$, and $M(\psi)$, $M(\phi_0)$,
  $M(\phi_1)$, so that the average of $M$ increases by
  $198400/85766121$.
- **Computed, not stated in Lean (orchestrator, exact):** along the paper's
  decomposition $M=\xi_1+\xi_2+\xi_3$ for a POVM on qubit $A$, the average
  changes are $-65600/85766121$ for $\xi_1=M_A$,
  $-2360000/85766121$ for
  $\xi_2=\tau_B+\tau_C+\tau_D-2(C_{BC}^2+C_{BD}^2+C_{CD}^2)$, and
  $+2624000/85766121$ for $\xi_3=-C_{AB}^2-C_{AC}^2-C_{AD}^2$; the decrease
  of $\xi_1$ and $\xi_2$ does not compensate the increase of $\xi_3$. Of the
  single residuals, $M_A$ and $M_B$ decrease and $M_C$, $M_D$ increase on
  average.
- **Computed, not stated in Lean (orchestrator, floating point with a
  tolerance of $10^{-9}$):** for the same state and the diagonal POVMs
  $\mathrm{diag}(\alpha,\beta)$,
  $\mathrm{diag}(\sqrt{1-\alpha^2},\sqrt{1-\beta^2})$ on qubit $A$ with
  $\alpha,\beta$ on the paper's grid $\{0.05,0.06,\dots,0.95\}$, the average
  of $M$ increases at 7424 of the 8281 grid points, decreases at 766 and is
  unchanged at the 91 points $\alpha=\beta$, where both Kraus operators are
  multiples of the identity and both outcomes equal $\psi$ (largest increase
  about $0.0054$, at $\alpha=0.91$, $\beta=0.05$); the increase is not an
  effect of the boundary value $\beta=0$.
- **Mechanism (orchestrator, exact; not stated in Lean):** the outcome
  $K_0$ collapses $\psi$ to the product state $|0001\rangle$, with
  probability $400/841$ and $M=0$, while the other outcome roughly doubles
  $M$: $M(\phi_1)/M(\psi)=23185529/11474379\approx2.021$, which exceeds
  $1/p_1=841/441\approx1.907$.
- **Follows from it (orchestrator argument, not stated in Lean):** appending
  $N-4$ qubits in the state $|0\rangle$ leaves every one-qubit entropy and
  every two-qubit concurrence among the first four qubits unchanged and adds
  only zero terms, and the measurement on qubit $A$ keeps the product form;
  so the $N$-qubit sum $M_N=\sum_k\tau_k-2\sum_{i>j}C_{ij}^2$ of Eq. (9) is
  not an entanglement monotone for any $N\ge4$.
- **Effect on the paper's other conclusions (checked by reading the v2
  source):**
  - *Refuted:* the conjecture that $M$ is an entanglement monotone (l.
    374–375, restated in l. 453–456), the compensation argument behind it
    (l. 376–390), the proposal of $E_{ms}=M/4$ as a monotone measure of the
    multipartite entanglement per qubit (l. 458–465, l. 564–568), and the
    conjectured monotonicity of $M_N$ for $N$ qubits (l. 524–528).
  - *Needs another justification:* the use of $E_{ms}$ to rule out an LOCC
    transformation whenever $E_{ms}$ increases (l. 499–506) is conditional
    on the monotonicity and has no basis in general.
  - *Unaffected:* the definition of $M$, its nonnegativity (from the
    Osborne–Verstraete monogamy inequality) and its LU invariance (l.
    367–369); Eq. (6), the average decrease of $M_A$ under a POVM on qubit
    $A$ (here $M_A$ decreases); the conclusion that the single residuals
    $M_k$ are not monotones (here $M_C$ and $M_D$ increase); the analysis of
    the three- and four-qubit correlations $t_3$ and $t_4$ (l. 308–358); and
    the values of $\Delta M$ for the nine representative states in Fig. 2,
    which are numerical observations on those states.
- **Open here:** the largest natural class of four-qubit states on which
  $M$ does not increase on average under local instruments (Bai–Wang 2008
  prove it for the cluster-class states), and whether $M$ is monotone on the
  nine representative families of the paper for all of their parameters.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained; the citing-work readings are
seat-reported. The Lean kernel verifies the encoded statement and its axiom
closure; its correspondence to the paper, including the restriction to local
instruments on qubit $A$ and the reading of the eigenvalues as the sorted
roots of the characteristic polynomial, is checked by reading the source and
the definitions.
