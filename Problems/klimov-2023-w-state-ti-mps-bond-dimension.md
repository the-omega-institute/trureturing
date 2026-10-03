---
slug: klimov-2023-w-state-ti-mps-bond-dimension
bibkey: klimov2023wstate
doi: 10.48550/arXiv.2306.16456
url: https://arxiv.org/abs/2306.16456v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result
---

# The minimal translation-invariant MPS bond dimension of the W-state

## Problem

P. Klimov, R. Sengupta and J. Biamonte, *On Translation-Invariant Matrix
Product States and advances in MPS representations of the $W$-state*,
arXiv:2306.16456v2, Section 3, conjecture after their Theorem 1:

> These experiments lead us to conjecture that the representation obtained in Theorem \ref{W state representation} could be optimal both in terms of asymptotics and the constant factor or in other words it is impossible to come up with a TI MPS representation with PBC with bond dimension smaller than $\floor*{\frac{n}{2}}+1$ for the $W$-state of order $n$.

A TI MPS representation with PBC of bond dimension $d$ of the normalized
$W$-state of order $n$ is a pair of complex $d\times d$ matrices $A_0$, $A_1$
with $\operatorname{Tr}(A_{i_1}\cdots A_{i_n})=1/\sqrt n$ when exactly one
$i_j$ is $1$ and $0$ otherwise (Section 2). Problem 4 of Section 4 asks
whether $d(n)=\lfloor n/2\rfloor+1$, and the table of Section 4 lists
$d(7)=4$.

## Motivation

The $W$-state is translation invariant, but a translation-invariant MPS
with periodic boundary conditions needs a bond dimension that grows with
$n$: the known lower bound is $\Omega(n^{1/(3+\delta)})$ for every
$\delta>0$, and Theorem 1 of the paper gives the upper bound
$\lfloor n/2\rfloor+1$. The conjecture says that this upper bound is exact.
The frozen declaration
`D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result` refutes it.

## Gap

Issue #12026 classifies the conjecture as Tier 1 and records the bounded
literature check before any Lean. It found:

- arXiv v2 is the latest version, with no journal version;
- the five citing works listed by Semantic Scholar (arXiv:2408.04729,
  2408.13033, 2410.19541, 2412.19635, 2503.16327) give no representation
  below $\lfloor n/2\rfloor+1$; 2410.19541 calls the minimal TI MPS an open
  question, and 2503.16327 cites the paper as evidence for
  $\lfloor L/2\rfloor+1$;
- arXiv:1809.08185, arXiv:2108.00031 and quant-ph/0608197 give only border
  bond dimension, lower bounds and the $O(n)$ representation.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

1. Take the $3\times3$ matrices $A_0=E_{12}+E_{21}+E_{23}$ and
   $A_1=E_{31}/\sqrt7$, with $E_{ij}$ the matrix units, and write
   $B=\sqrt7A_1=E_{31}$.
2. $A_0^3=A_0$, and $(A_0^r)_{13}$ is $1$ for even $r\ge2$ and $0$
   otherwise.
3. A word with $k\ge1$ letters $1$ has trace
   $7^{-k/2}\prod_j(A_0^{r_j})_{13}$, where the cyclic gaps $r_j\ge0$
   between consecutive letters $1$ add up to $7-k$.
4. For $k=1$ the gap is $6$ and the trace is $1/\sqrt7$. For $k\ge2$ all
   gaps even and at least $2$ needs $3k\le7$, so $k=2$, and then the gaps
   add up to $5$, which is odd: the trace is $0$. For $k=0$,
   $\operatorname{Tr}A_0^7=\operatorname{Tr}A_0=0$.
5. So $d(7)\le3<4=\lfloor7/2\rfloor+1$. In Lean the 128 word traces of the
   integer matrices are computed by the kernel and the factor $1/\sqrt7$ is
   pulled out of each word.

## Falsifier

The kernel-checked `result` excludes the bound $d\ge\lfloor n/2\rfloor+1$
for $n=7$, hence the conjecture, the answer "yes" to Problem 4, and the
table entry $d(7)=4$. Changing the definition of a representation (the
normalization $1/\sqrt n$, the cyclic trace, or the order of the matrix
product) would change the question.

## Evidence

Exact SymPy arithmetic over all 128 words and an independent NumPy
computation give the traces above (0 failures). The same matrices give 10
and 17 failures for $n=6$ and $n=8$, and perturbing one entry by $0.01$
gives 7–21 failures. As a positive control, the paper's Theorem 1
construction for $n=5,6,7$ passes the same checker (issue #12026).

The canonical source is
`D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.lean`. Its public
declarations are `IsWStateTIMPS`, `claim` and `result`. The frozen module
state has statement identity `sha256:fd1e75a90d7c9c176ed83ca1295f07558a4caf391781f06e1d7c9f3c285e68c0`. The result declaration has
statement identity `sha256:8debb2e851e522c233797783f07fc7d6b5e8597be4fe6289c23b239431fd636d`. The Freeze event is `sha256:ac8c966e2d620df874db853c6f0de88ba4ae76757fabf4a4c4bc2f531cbbf038`. It has
no project-level frozen prerequisites (pinned Mathlib only). The proof uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 published conjecture; resolution `Refuted` by
`D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result`.
`proof_shape: bind-only` (evaluation at an explicit pair of matrices);
`admission_basis: open-problem-resolution` (issue #12026). Utility
`certified-instance`, refuting `claim`.

### What the refutation shows

- **Proved in this module:** the normalized $W$-state of order $7$ has a
  translation-invariant MPS representation with periodic boundary
  conditions of bond dimension $3<\lfloor7/2\rfloor+1$.
- **Where the conjecture fails:** in the proof of Theorem 1,
  $(A_0^m)_{d1}$ vanishes for $m\le d-2$ and is nonzero for
  $d-1\le m\le2d-2$ (display (d1), l. 373–379), and a word of weight
  $k\ge2$ is killed only by its shortest cyclic gap, which is below
  $\lfloor n/2\rfloor$ (l. 407). That mechanism needs $d$ of order
  $n/2$. The witness keeps the paper's shape of a scaled matrix unit
  ($A_1$ a multiple of a matrix unit: $E_{1d}$ in the paper, $E_{31}$
  here) but takes a periodic $A_0$: the entry $(A_0^r)_{13}$ is nonzero only on an arithmetic
  progression of lengths, and the words of weight $\ge2$ are killed by
  parity instead of by short gaps.
- **Computed, not formalized (orchestrator):** with $A_1$ a multiple of
  $E_{d1}$ and a nonnegative integer $A_0$, exact traces over all words give
  $d(10)\le4$, $d(11)\le4$ and $d(13)\le4$, against
  $\lfloor n/2\rfloor+1=6$, $6$, $7$. An exhaustive search over $0/1$
  matrices $A_0$ with this $A_1$ finds no representation for
  $(n,d)=(4,2),(5,2),(6,2),(6,3),(8,3),(9,3),(10,3),(6,4),(8,4),(9,4),(12,4)$.
  This restricted search does not settle the table entries $d(8)=5$ and
  $d(9)=5$; they are open here.
- **Model derivation, not checked in Lean (GPT Pro seat):** for $D\ge3$ and
  $n=D(D-1)+1$, the $(D-1)$-cycle on the vertices $1,\dots,D-1$ with the
  extra edge $D-1\to D$, and $A_1$ a multiple of $E_{D1}$, give
  $d(W_n)\le D$. A word of weight $k\ge2$ would need $k\equiv1\pmod{D-1}$,
  hence $k\ge D$, against $n<D^2$. So $d(n)/n\to0$ along this subsequence,
  and the "asymptotics" part of the conjecture fails along it. The
  orchestrator recomputed $D=4$ ($n=13$) over all $2^{13}$ words. Whether
  $d(n)=O(\sqrt n)$ for all $n$ is open here.
- **Unchanged:** Theorem 1 (the upper bound $\lfloor n/2\rfloor+1$), the
  lower bound $\Omega(n^{1/(3+\delta)})$, the paper's general constructions
  and its algorithm for $d(\psi)$ do not depend on the conjecture. The
  paper's question whether $d(6)=4$, and its question whether $d(n)$ is
  monotone, remain open here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent counterexample. The Lean kernel verifies the
encoded statement and its axiom closure; correspondence to the external
paper, including the reading of the cases display as the definition of a
representation and the hypothesis $n\ge2$ as a weakening, is checked by
reading the source and the definitions.
