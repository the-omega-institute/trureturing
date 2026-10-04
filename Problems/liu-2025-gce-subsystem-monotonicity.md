---
slug: liu-2025-gce-subsystem-monotonicity
bibkey: liu2025generalized
doi: 10.1103/jtlj-qs3y
url: https://arxiv.org/abs/2406.18517v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result
---

# Subsystem monotonicity of generalized concentratable entanglement

## Problem

X. Liu, J. Knörzer, Z. J. Wang and J. Tura, *Generalized Concentratable
Entanglement via Parallelized Permutation Tests*, Phys. Rev. Research 7,
L032022 (2025), arXiv:2406.18517v1. For an $n$-qubit pure state $\psi$ and a
set $s$ of qubits,

> $\mathcal{C}^{(K)}_{\ket{\psi}}(s):=\frac{1}{K-1}\left(1-\frac{1}{2^{|s|}}\sum_{\alpha\in\mathcal{P}(s)}\Tr(\rho_{\alpha}^K)\right)$ for any $K>1$ […] We take $\Tr(\rho^K_{\varnothing})=1$ in the sum.

The conjecture (arXiv Conjecture 6, journal Conjecture 1), clause 1:

> $\mathcal{C}^{(K)}_{\ket{\psi}}(s')\leqslant \mathcal{C}^{(K)}_{\ket{\psi}}(s)$ if $s'\subseteq s$.

The paper states that this clause and the subadditivity clause "have been
proven to be true for $K=2$" and conjectures that "they also hold for $K>1$".

## Motivation

Monotonicity under enlarging the subsystem is a basic property expected of a
multipartite entanglement measure built from subsystem purities. The frozen
declaration
`D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result`
shows that the clause fails for real $K>1$.

## Gap

Issue #12852 classifies the conjecture as Tier 1. Before any Lean it recorded
the following checks:

- Luo–Guo–Meng–Bai, arXiv:2511.09415v2, prove the subadditivity clause (their
  l. 470: "a positive answer to Conjecture~1.2"); they state nothing on the
  subsystem clause.
- QIQCOP Zoo and this repository have no record of the paper or of
  concentratable entanglement.
- A separate seat found no settlement and no short implication. It examined
  the concentratable-entanglement literature and the Tsallis
  strong-subadditivity counterexamples of Petz–Virosztek and Coles.
- Ren–Li–Luo, Adv. Quantum Technol. 9, e00617 (2026), has no arXiv version;
  its abstract concerns LOCC monotonicity, continuity and state comparisons.
  Its full text was not inspected.

These are orchestrator-checked and seat-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $\psi\propto-1100\,|0000\rangle-100\,|0101\rangle-100\,|1010\rangle
   +75\,|1100\rangle-9\,|1111\rangle$, squared norm $1235706$; $K=5/2$,
   $s'=\{0,1\}$, $s=\{0,1,2\}$.
2. Write $Q_\alpha=1235706\,\rho_\alpha$. Then:
   - $Q_0=Q_1=\operatorname{diag}(1220000,15706)$ and
     $Q_2=\operatorname{diag}(1225625,10081)$;
   - $Q_{01}$, $Q_{02}$ and $Q_{12}$ are direct sums of diagonal entries and
     one $2\times2$ block $M$, with $\det M=9900^2$, $100^2$ and $10000^2$;
   - $Q_{012}=uu^{\mathsf T}+ww^{\mathsf T}$ with $u\perp w$,
     $|u|^2=1225625$ and $|w|^2=10081$.
3. Each $Q_\alpha$ has an explicit positive semidefinite square root $S$:
   - square roots of its diagonal entries;
   - $(M+\sqrt{\det M}\,I)/\sqrt{\operatorname{tr}M+2\sqrt{\det M}}$ on a
     $2\times2$ block;
   - $uu^{\mathsf T}/|u|+ww^{\mathsf T}/|w|$ for $Q_{012}$.
4. Hence $\rho_\alpha^{5/2}=S'^5$ with $S'=S/\sqrt{1235706}$, and
   $\operatorname{Tr}\rho_\alpha^{5/2}=\operatorname{Tr}(Q_\alpha^2S)/
   1235706^{5/2}$.
5. With $T_\alpha=\operatorname{Tr}\rho_\alpha^{5/2}$,
   $8(K-1)\bigl(\mathcal C(s')-\mathcal C(s)\bigr)
   =T_2+T_{02}+T_{12}+T_{012}-1-T_0-T_1-T_{01}$. Rational bounds for eight
   square roots show that it lies near $5.77\cdot10^{-7}$ and is positive.

## Falsifier

The kernel-checked `result` is the negation of the following statement. For
every number of qubits $N$ and every vector $\psi$ on the configurations
$\mathrm{Fin}\,N\to\mathrm{Fin}\,2$ with $\sum_w\|\psi(w)\|^2=1$, all subsets
$s'\subseteq s$ of the qubits and every real $K>1$,
$\mathcal C^{(K)}_\psi(s')\le\mathcal C^{(K)}_\psi(s)$. The definitions are as
follows:

- the reduced states are the frozen `reducedState` of
  `PurityTimeReversalOverlapMinimum`;
- $\Tr(\rho_\alpha^K)$ is the real part of the trace of the
  continuous-functional-calculus power `ρ_α ^ (K : ℝ)`;
- the empty set contributes 1, as the paper prescribes;
- `gce` is Eq. (defeq) literally.

## Evidence

- Values (mpmath, 60 digits):
  - $\mathcal C^{(5/2)}(\{0,1\})-\mathcal C^{(5/2)}(\{0,1,2\})\approx4.81\cdot10^{-8}$;
  - for the scaled certificate, $1235706^{5/2}\cdot8(K-1)(\mathcal C(s')-\mathcal C(s))$
    lies in $[980145105.97,\,980145116.46]$ under the rational bounds used in
    Lean.
- A separate seat independently recomputed the related witness
  $(-400,20,-20,20,1)$ on the same support: gap
  $1.1168\cdot10^{-8}$ (seat-reported, also recomputed by the orchestrator).

The canonical source is
`D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.lean`.
- Public declarations: `powerTrace`, `gce`, `claim`, `coeff`, `psi`,
  `tripleEquiv`, `out1Equiv` and `result`.
- Reuse: the frozen `reducedState`, `Outside` and `join` of
  `PurityTimeReversalOverlapMinimum`, `partialTraceRight` of
  `PartialTraceMutualInformation`, and the coordinate equivalences
  `pairEquiv`, `outEquiv`, `singleEquiv`, `out3Equiv` and `fourEquiv` of
  `FourQubitResidualSumMonotoneRefutation`, made public for this purpose.
- Freeze identities:
__IDS__
- Axioms: the proof uses only `propext`, `Classical.choice` and
  `Quot.sound`. It contains no `sorry`, no `native_decide` and no new axiom.

## Triage

Tier 1 conjecture of a 2025 journal article. Resolution: `Refuted`, by
`D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.result`.

- `proof_shape: bind-only`. The settlement of the named conjecture is the new
  content; there is no escape witness.
- `admission_basis: open-problem-resolution` (issue #12852).
- Utility kind `certified-instance`, basis `refutes` the module's `claim`.

### What the settlement shows

- **Proved by `result`:** at $K=5/2$, adding the qubit $2$ to $\{0,1\}$
  lowers the generalized concentratable entanglement of the stated four-qubit
  state, so clause 1 of the conjecture fails for real $K>1$.
- **Proved inside the proof of `result`:** the seven reduced states of the
  witness, their explicit square roots, and the identity
  $\operatorname{Tr}\rho^{5/2}=\operatorname{Tr}(Q^2S)/1235706^{5/2}$ for
  each of them.
- **Where the example lives (orchestrator readings, not stated in Lean):**
  - On the family
    $\psi_t\propto-|0000\rangle+t|0101\rangle-t|1010\rangle+t|1100\rangle+t^2|1111\rangle$,
    the clause fails for small $t$ at $K=2.2$ and $K=2.5$, and holds at
    $K=3,4,5,6$ (double-precision spectra at $t=0.3,0.2,0.1,0.05,0.02$).
  - The search seat reports the expansion
    $\mathcal C^{(5/2)}(\{0,1,2\})-\mathcal C^{(5/2)}(\{0,1\})
    =\frac{8\sqrt2-1-5\sqrt5}{12}t^5+O(t^6)$, with a negative leading
    coefficient. The orchestrator did not verify this expansion.
  - The paper's numerics used $K=1.2,1.8,3,5$ and Haar-random states, away
    from this window just above $K=2$.
- **Effect on the paper's other conclusions (checked by reading the arXiv
  source):**
  - The paper shows clause 1 equivalent to a "not-so-strong subadditivity"
    sum of Tsallis-entropy strong-subadditivity expressions (arXiv
    Proposition 7, journal Proposition 4). That inequality therefore also
    fails at $K=5/2$.
  - The proved properties (LOCC monotonicity on average, vanishing on product
    states, continuity, the single-label identity) and the subadditivity
    clause, proved by Luo–Guo–Meng–Bai, are unaffected.
  - The estimation protocols and the $K=2$ statements are unaffected.
- **Open here:**
  - whether clause 1 holds for every integer $K\ge3$; the paper's appendix
    sketches a route through $\mathfrak q(\mathbf z)\ge0$;
  - whether it fails for some $K\in(1,2)$;
  - the full set of $K$ for which it fails.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and the full text
of Ren–Li–Luo (2026) was not inspected. The Lean kernel verifies the encoded
statement and its axiom closure. Its correspondence to the paper, including
reading $\Tr(\rho_\alpha^K)$ through the continuous functional calculus and
the empty-set convention, is checked by reading the source and the
definitions.
