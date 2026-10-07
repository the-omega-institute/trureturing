---
slug: girard-2017-binegativity-monotonicity
bibkey: girard2017binegativity
doi: 10.48550/arXiv.1701.02724
url: https://arxiv.org/abs/1701.02724v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.result
---

# Binegativity monotonicity for two qubits

## Problem

M. W. Girard and G. Gour, *The binegativity of two qubits*,
arXiv:1701.02724v3, introduction, p. 1:

> That is, we conjecture that for any two-qubit state $\sigma$ it holds that
> $N_2(\mathcal{E}(\sigma))\leq N_2(\sigma)$ for any LOCC (or PPT) channel
> $\mathcal{E}$ that outputs states of two qubits.

Here $N_2(\sigma)=\operatorname{Tr}[(\sigma^\Gamma)_-]+
2\operatorname{Tr}[(((\sigma^\Gamma)_-)^\Gamma)_-]$, with partial
transposition on Bob and the positive and negative components of
self-adjoint matrices. S. Sazim and N. Awasthi, *Binegativity of two qubits
under noise*, arXiv:1711.03717v2, introduction, p. 1, restate:

> On the basis of numerical evidence, it is conjectured that the
> binegativity behaves monotonically under both LOCC and PPT channels [15].

Their abstract also states: "Our study supports the conjecture that the
binegativity is a monotone."

## Motivation

The frozen declaration
`D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.result`
refutes deterministic monotonicity even for finite one-way LOCC channels
whose input and output each consist of two qubits. Thus binegativity does
not satisfy the LOCC monotonicity requirement of an entanglement measure.

## Gap

Preregistration #12908 records the Tier 1 classification, both verbatim
sources, the quantified statement, and literature checks before any Lean.
The original paper retains the conjecture and states that the authors do
not have a valid proof. The follow-up supplies noise-channel evidence,
which does not cover arbitrary adaptive local protocols. The existing
upper-bound refutation concerns Eq. (9), a distinct conjecture.

The literature and citation searches recorded in #12908 are
`not-found-in-searched-scope`, not an exhaustive worldwide priority claim.
The later multinegativity paper arXiv:2609.20698 was identified by the
search seat; its relevance is unverified here.

## Route

For finitely many Alice outcomes $i$, let $A_i$ satisfy
$\sum_i A_i^\dagger A_i=I$. For each outcome, Bob has a complete channel
$\sum_j B_{ij}^\dagger B_{ij}=I$. After discarding outcomes, the channel is
$\mathcal E(\sigma)=\sum_{i,j}(A_i\otimes B_{ij})\sigma
(A_i\otimes B_{ij})^\dagger$.

In the basis $00,01,10,11$, take
$\rho=\tfrac34|00\rangle\langle00|+\tfrac14|\psi^+\rangle
\langle\psi^+|$, where $|\psi^+\rangle=(|01\rangle+|10\rangle)/\sqrt2$.
Alice uses $A_0=\operatorname{diag}(1/2,1)$ and
$A_1=(\sqrt3/2)|0\rangle\langle0|$. Bob uses the identity on outcome 0
and resets to $|1\rangle$ on outcome 1, with Kraus operators
$|1\rangle\langle0|$ and $|1\rangle\langle1|$. The output is

$$
\rho'=\begin{pmatrix}
3/16&0&0&0\\
0&11/16&1/16&0\\
0&1/16&1/8&0\\
0&0&0&0
\end{pmatrix}.
$$

The partial transposes have single negative eigenvalues
$(3-\sqrt{10})/8$ and $(3-\sqrt{13})/32$. Positive rank-one decompositions
with vanishing positive-negative products identify both nested negative
parts through `CFC.posPart_negPart_unique`. Their traces give

$$
N_2(\rho)=-\frac14+\frac{7\sqrt{10}}{80}
< -\frac1{32}+\frac{7\sqrt{13}}{416}=N_2(\rho').
$$

The exact rational certificates are $\sqrt{10}<31623/10000$ and
$36055/10000<\sqrt{13}$.

## Falsifier

`claim` quantifies over all complex matrices on `Fin 2 × Fin 2` satisfying
the frozen `IsDensity` predicate (positive semidefinite, trace one), and
over every `E` satisfying `IsOneWayLOCC`, with conclusion
`binegativity (E σ) ≤ binegativity σ`. `result : ¬ claim` has no external
hypotheses. Since finite one-way LOCC is contained in LOCC, this refutes
the universal LOCC clause of the source conjecture. The formal claim does
not separately define the class of PPT channels.

## Evidence

The canonical source is
`D5/S3/Quantum/Entanglement/TwoQubitBinegativityMonotonicityRefutation.lean`.
Its entire public surface is `IsOneWayLOCC`, `claim`, and `result`.
It reuses `binegativity` and `vec4` from the upper-bound module and
`partialTransposeB` and `IsDensity` from the structured-negativity module.
All certificate helpers are local to the proof; no new private theorem,
new axiom, `sorry`, or `native_decide` is used.

Computed with NumPy 2.2.5 by
`python3 /Users/auric/.sshx/b465cc0994bedc55422789e7/attempt-1/bineg-check.py`:
$N_2(\rho)=0.026699295264733185$,
$N_2(\rho')=0.029420333962134428$, and increase
$0.002721038697401243$. Kraus completeness and the output matrix agree
within $10^{-14}$. The program diagonalizes both successive Hermitian
matrices; these numerical values supplement the exact proof.

## Triage

Tier 1; resolution **Refuted** by the frozen `result` above.
`proof_shape: bind-only`; `escape_witness: none`;
`admission_basis: open-problem-resolution` (#12908).
The utility is a certified instance refuting the module's `claim`.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** a deterministic finite one-way LOCC channel
  increases $N_2$ on the displayed density matrix. Consequently $N_2$ is
  not an LOCC monotone and cannot be an entanglement measure with that
  requirement. The density, local completeness, output action, and exact
  values are established within the proof of `result`.
- **Computed (the NumPy command in Evidence):** Alice's filter reduces the
  separable $|00\rangle$ weight relative to the entangled block. Bob's
  reset moves discarded weight to $|01\rangle$, outside the $00,11$
  negative-eigenvector block of the partial transpose. Ordinary negativity
  falls from $0.040569415042094825$ to $0.03784695471649933$, while the
  nested contribution $2\operatorname{Tr}[(((\rho^\Gamma)_-)^\Gamma)_-]$
  grows from $0.006414587743685773$ to $0.010496856603884766$.
- **Proved as a matrix-algebra consequence of the same protocol, not a
  separate Lean declaration:** the PPT clause also fails. For product
  Kraus matrices $A_i\otimes B_{ij}$, the map
  $\Gamma\mathcal E\Gamma$ has Kraus matrices
  $A_i\otimes\overline{B_{ij}}$, so it is completely positive. Thus this
  one-way LOCC witness is also a PPT channel; its strict increase is the
  one established by `result`.
- **Computed family; formalization open:** for
  $\rho(a,b,c,z)=\begin{pmatrix}a&0&0&0\\0&b&z&0\\0&z&c&0\\0&0&0&0\end{pmatrix}$,
  assume $a,b,c\ge0$, $a+b+c=1$, $z>0$, $z^2\le bc$,
  $r=a/(2z)>4/3$, and $16/(9r^2)\le s<1$. The same protocol sends
  $(a,b,c,z)$ to $(sa,b+(1-s)a,c,\sqrt{s}z)$. With
  $D=\sqrt{a^2+4z^2}$ the formula is
  $N_2=(D-a)(1+2z/D)/2$. Set
  $t=1/(r+\sqrt{r^2+1})$; then
  $N_2=(2z^2/a)H(t)$ for
  $H(t)=(1-t)(1+t)^3/(2(1+t^2))$. The filter preserves $z^2/a$ and
  strictly increases $t$ while keeping $0<t\le1/3$, because
  $\sqrt{s}r\ge4/3$.
  The derivative
  $H'(t)=(1+t)^2(1-3t+t^2-t^3)/(1+t^2)^2$ is positive on that interval.
  This is an analytical argument, not a separately certified theorem.
  The Evidence program checked 10,097 random admissible members with
  seed 12908, using the closed formula; minimum increase
  $1.9823902197423787\cdot10^{-9}$. The 10,097-member check reported in
  #12908 is an independent orchestrator reading. A uniform formal theorem
  is a separate candidate.
- **Proved in the source, not reproved here:** $N_2$ vanishes exactly on
  separable two-qubit states and is invariant under local unitaries
  (Girard–Gour, introduction). These properties survive this refutation.
- **Proved consequence of the refutation:** the source's conditional
  interpretation of the $N_2$ ordering as a new entanglement-measure
  ordering is unavailable. Algebraic computations of $N_2$ and the
  follow-up's calculations for selected noise channels remain unchanged.
  The separate upper bound in Eq. (9) is already refuted by the existing
  upper-bound module; the lower bound remains open here.

## ASSUMED-UNVERIFIED

The literature checks establish no exhaustive priority claim. The source
correspondence, LOCC interpretation, and PPT consequence are mathematical
reading judgements; the kernel certifies the encoded `¬ claim`. The
uniform family theorem and any separately encoded PPT-class theorem are
not delivered in this module. The random family check is a finite
numerical reading, not a uniform proof.
