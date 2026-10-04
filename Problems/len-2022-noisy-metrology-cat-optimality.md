---
slug: len-2022-noisy-metrology-cat-optimality
bibkey: len2022quantum
doi: 10.1038/s41467-022-33563-8
url: https://arxiv.org/abs/2109.01160v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result
---

# Optimality of cat pairs for metrology with noisy measurements

## Problem

Y. L. Len, T. Gefen, A. Retzker and J. Kołodyński, *Quantum metrology with
imperfect measurements*, Nature Communications 13, 6971 (2022),
arXiv:2109.01160v2. An imperfect measurement multiplies the quantum Fisher
information by

> $\gamma_\cM=\max_{\ket{\xi},\ket{\xi_{\perp}}} \sum_x \frac{\mathrm{Re}\!\left\{\langle\xi_{\perp}|M_{x}|\xi\rangle\right\}^{2}}{\langle\xi|M_{x}|\xi\rangle}$

and for $N$ probes measured independently $M_{\xvec}=M_{x_1}\otimes\cdots\otimes
M_{x_N}$. The supplement conjectures:

> for any classical noise channel, $M_{x}=\sum_{i}p\!\left(x|i\right)\Pi_{i}$ that is applied independently on each of the $N$ probes, the optimal $|\zeta^{N} \rangle,|\zeta_{\perp}^{N}\rangle$ take the form of ``cat states": $|\zeta^{N} \rangle =\cos\left(\theta\right)|j\rangle^{\otimes N}+\sin\left(\theta\right)|k\rangle^{\otimes N}$, $|\zeta_{\perp}^{N} \rangle =-\sin\left(\theta\right)|j\rangle^{\otimes N}+\cos\left(\theta\right)|k\rangle^{\otimes N}$

Here $\zeta,\zeta_\perp$ are the images of $(\psi\pm\psi_\perp)/\sqrt2$ under the
encoding unitary, so the optimized pair is
$\xi=(\zeta+\zeta_\perp)/\sqrt2$, $\xi_\perp=(\zeta-\zeta_\perp)/\sqrt2$.

## Motivation

The conjecture would reduce the optimal noisy-readout protocol for $N$
probes to a single-probe choice of two levels and one angle. The frozen
declaration
`D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result`
shows that no cat pair need be optimal.

## Gap

Issue #12917 classifies the conjecture as Tier 1. Before any Lean it recorded
the following checks:

- Zhou, Michalakis and Gefen, PRX Quantum 4, 040305 (2023),
  arXiv:2210.11393v3, Theorem 6: for commuting measurements some optimal
  pair is supported on two common-eigenbasis states of the whole system,
  that is, on two arbitrary words. Their symmetric bit-flip example has
  non-repeated co-optimal words while repeated words remain optimal, and
  they leave the choice of words open.
- The objective $t(1-t)\sum_\omega(a_\omega-b_\omega)^2/(ta_\omega+(1-t)b_\omega)$ is
  the Le Cam divergence of a binary-input channel (Polyanskiy–Wu 2017,
  App. B; Ordentlich–Polyanskiy 2022). Neither source compares repeated with
  non-repeated words.
- QIQCOP Zoo and this repository have no record of the paper or of the
  claim.

These are seat-reported readings checked against the cited theorems'
statements, `not-found-in-searched-scope`; they do not establish exhaustive
worldwide novelty.

## Route

1. $d=3$, outcomes $\mathrm{Fin}\,3$, $N=2$, and
   $p(x|i)=P_{xi}$ with $P=\frac1{20}\begin{pmatrix}1&14&2\\15&2&17\\4&4&1\end{pmatrix}$.
2. Write $m_{\mathbf x}(s)=p(x_1|s_1)\,p(x_2|s_2)$. For orthonormal real
   vectors supported on two words $u\ne v$, with $\xi=(\zeta+\zeta_\perp)/\sqrt2$
   having squared weight $t$ on $u$,
   $\gamma=\sum_{\mathbf x}t(1-t)(m_{\mathbf x}(u)-m_{\mathbf x}(v))^2/
   (t\,m_{\mathbf x}(u)+(1-t)\,m_{\mathbf x}(v))$.
3. The pair $\zeta=|10\rangle$, $\zeta_\perp=|21\rangle$ has $t=1/2$ and
   $\gamma=6643859399/9075312000\approx0.732081$.
4. A cat pair with $j\ne k$ has $u=jj$, $v=kk$ and
   $t=(\cos\theta-\sin\theta)^2/2$. Each summand equals
   $D-ab/D-(2t-1)(a-b)$ with $D=ta+(1-t)b$, and
   $ab/D\ge ab\,(2/D_0-D/D_0^2)$ for $D_0=t_0a+(1-t_0)b$, so $\gamma$ is at
   most an affine function of $t$. At $t=0$ and $t=1$ it is below $73/100$
   for $t_0=2061/4000$, $191/500$, $1939/4000$, $363/800$, $309/500$,
   $437/800$ on the ordered pairs $(0,1)$, $(0,2)$, $(1,0)$, $(1,2)$,
   $(2,0)$, $(2,1)$.

## Falsifier

The kernel-checked `result` is the negation of the following statement. For
every $d\ge2$, every finite type $X$, every $p:X\to\mathrm{Fin}\,d\to\mathbb R$
with $p>0$ and $\sum_xp(x|i)=1$, and every $N\ge1$, there are $j\ne k$ in
$\mathrm{Fin}\,d$ and $\theta\in\mathbb R$ such that every orthonormal pair
$\zeta,\zeta_\perp$ of vectors on the words $\mathrm{Fin}\,N\to\mathrm{Fin}\,d$
has $\gamma(\zeta,\zeta_\perp)\le\gamma(\text{cat pair})$. The definitions
are as follows:

- `probeOp` is $\sum_ip(x|i)\,\Pi_i$ and `multiProbeOp` its $N$-fold tensor
  product, written entrywise on the product basis;
- `gamma` is Eq. (AgammaN) with $V_\Phi\psi=(\zeta+\zeta_\perp)/\sqrt2$ and
  $V_\Phi\psi_\perp=(\zeta-\zeta_\perp)/\sqrt2$; it takes the real part of
  each summand, whose numerator and denominator are real in the source;
- `basisPower j` is $|j\rangle^{\otimes N}$, and `catState`, `catPerp` are the
  displayed cat pair.

With all $p(x|i)>0$ every $M_{\mathbf x}$ is positive definite, so $\gamma$ is
continuous on the compact set of orthonormal pairs and attains its maximum
(orchestrator reasoning, not in Lean); the conjecture's "the optimal" pair
presupposes one. With zero entries the maximum need not be attained
(seat-reported: Zhou–Michalakis–Gefen, arXiv:2210.11393v3, the assumption
before Theorem 6 and its appendix), and the encoding does not treat that
case.

## Evidence

- Values (Python `fractions`, exact): the witness value is
  $6643859399/9075312000$; the six tangent bounds are below $0.72989$.
- Numerical scan of this detector (double precision, all pairs of words,
  $t$ on a grid of step $1/2000$):
  - $N=1$: the best pair is a cat pair;
  - $N=2$: best $0.732111$ at the words $01$, $12$ against $0.729872$ for
    repeated words;
  - $N=3$: best $0.852460$ at $122$, $211$ against $0.851646$.

The canonical source is
`D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.lean`.
- Public declarations: `probeOp`, `multiProbeOp`, `gamma`, `basisPower`,
  `catState`, `catPerp`, `claim`, `detector`, `witness`, `witnessPerp` and
  `result`.
- Freeze identities:
  - module statement `sha256:1ee13a5291b015024e4111c47a75b5883a73699dab5ae04df0b574bc2e20f085`;
  - `result` statement `sha256:776162f0773ebb482186286dec12dab90a961361f14c4ded6b203265e197a2d4`;
  - Freeze event `sha256:fb0919ca0050f4afdc48df2cf72b4162c040c0d135d26bea69781c6bc11f7826`.
- Axioms: the proof uses only `propext`, `Classical.choice` and
  `Quot.sound`. It contains no `sorry`, no `native_decide` and no new axiom.

## Triage

Tier 1 conjecture of a 2022 journal article. Resolution: `Refuted`, by
`D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.result`.

- `proof_shape: bind-only`. The settlement of the named conjecture is the new
  content; there is no escape witness.
- `admission_basis: open-problem-resolution` (issue #12917).
- Utility kind `certified-instance`, basis `refutes` the module's `claim`.

### What the settlement shows

- **Proved by `result`:** for the stated qutrit detector and two probes, the
  pair $|10\rangle,|21\rangle$ has a larger $\gamma$ than every cat pair, so
  no cat pair is optimal.
- **Proved inside the proof of `result`:** the formula for $\gamma$ of any
  real orthonormal pair supported on two words, and a tangent-line upper
  bound for $t\mapsto\sum t(1-t)(a-b)^2/(ta+(1-t)b)$ when
  $\sum a=\sum b=1$.
- **Mechanism (orchestrator reading, not stated in Lean):** by step 2, a pair
  on two words is scored by the Le Cam divergence of the two product
  distributions. Repeated words $jj$, $kk$ use the same label pair on both
  probes; crossed words such as $10$, $21$ use the label pairs $(1,2)$ and
  $(0,1)$ on the two probes. For this detector the crossed product
  distributions have the larger divergence (steps 3 and 4).
- **Effect on the paper's other conclusions (read from the arXiv source):**
  - Lemma 1 and Theorem 1, the convergence of the noisy QFI to the perfect
    QFI as $N\to\infty$, are unaffected; the example concerns only which pair
    attains $\gamma_{\mathcal M^{\otimes N}}$ at finite $N$.
  - The Hellinger-distance statement earlier in the same paragraph is
    unaffected: Bhattacharyya coefficients multiply over probes, so a
    repeated pair of the best single-probe labels minimizes them
    (orchestrator reasoning, not in Lean).
  - At $N=1$, for detectors with all $p(x|i)>0$, Zhou–Michalakis–Gefen
    Theorem 6 gives an optimal pair of the form
    $\sqrt q\,|k\rangle+\sqrt{1-q}\,|l\rangle$,
    $\sqrt{1-q}\,|k\rangle-\sqrt q\,|l\rangle$ on two basis states, which
    is a cat pair; so the conjecture holds for one probe under that
    assumption (seat-reported reading of the theorem statement).
- **Open here:**
  - the qubit specialization of the paper ($d=2$, labels $0,1$);
  - for which detectors and which $N\ge2$ cat pairs fail;
  - whether the gap persists for all $N\ge2$ for this detector, beyond the
    $N=3$ reading above.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority; the journal
supplement's wording is seat-reported, and the quotations are from the arXiv
v2 source. The Lean kernel verifies the encoded statement and its axiom
closure. Its correspondence to the paper, including the real part in
`gamma` and the weakest reading of "optimal", is checked by reading the
source and the definitions.
