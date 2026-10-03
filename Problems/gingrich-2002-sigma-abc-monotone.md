---
slug: gingrich-2002-sigma-abc-monotone
bibkey: gingrich2002properties
doi: 10.1103/PhysRevA.65.052302
url: https://arxiv.org/abs/quant-ph/0106042v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result
---

# Gingrich's proposed three-qubit monotone built from the Kempe invariant

## Problem

R. M. Gingrich, *Properties of entanglement monotones for three-qubit pure
states*, Phys. Rev. A 65, 052302 (2002), arXiv:quant-ph/0106042v2, Eq. (31)
and the text after it:

> $\sigma_{ABC} = 3 - (I_1 + I_2 + I_3) I_4$ and numerical results suggest
> that it is an EM. ... For the rest of the paper I will assume that
> $\sigma_{ABC}$ is an EM.

For $\psi=\sum t_{ijk}|ijk\rangle$, the polynomial invariants are
$P_{\sigma,\tau}=\sum t_{i_1j_1k_1}\cdots t_{i_nj_nk_n}\,
\bar t_{i_1j_{\sigma(1)}k_{\tau(1)}}\cdots\bar t_{i_nj_{\sigma(n)}k_{\tau(n)}}$
(Eq. (8)), with $I_1=P_{e,(12)}$, $I_2=P_{(12),e}$, $I_3=P_{(12),(12)}$ (the
three one-qubit purities) and the Kempe invariant $I_4=P_{(123),(132)}$. An
entanglement monotone (EM) in the paper's sense satisfies
$E(\psi)\ge\sum_kp_kE(A_k\psi/\sqrt{p_k})$ for every complete instrument
$\{A_k\}$ on one party, $p_k=\|A_k\psi\|^2$.

## Motivation

The paper proves that the monotones of a pure state determine its LU orbit,
so for three qubits some monotone must depend on the Kempe invariant; the
four known ones (the three one-versus-two tangles and the three-tangle) do
not. $\sigma_{ABC}$ was proposed as that fifth monotone and used to bound
conversion probabilities. The frozen declaration
`D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result` shows
that it is not a monotone.

## Gap

Issue #12508 classifies the proposal as Tier 1 and records the checks made
before any Lean:

- arXiv:quant-ph/0106042 v2 is the latest version and states the proposal
  with its numerical support (over 300,000 random states and operations) and
  the caveat that a small violating region might have been missed;
- Oreshkov–Brun, arXiv:quant-ph/0506181v6 (Phys. Rev. A 73, 042314 (2006)),
  §VI, state that "no rigorous proof of monotonicity was given" and construct
  a different, proved monotone depending on the Kempe invariant;
- Spedalieri, arXiv:quant-ph/0110179, §III, states that the bare Kempe
  invariant is not a monotone, which does not decide the combination
  $3-(I_1+I_2+I_3)I_4$; other papers use the name $\sigma$ for different
  functions (Emary–Beenakker, quant-ph/0311105; Lévay, quant-ph/0403060).

These are seat-reported and orchestrator-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $\psi=(5|000\rangle+5|011\rangle+2|110\rangle)/(3\sqrt6)$ and the
   instrument $K_0=\mathrm{diag}(3/5,0)$, $K_1=\mathrm{diag}(4/5,1)$ on qubit
   $A$, with $K_0^\dagger K_0+K_1^\dagger K_1=I$. Then $p_0=1/3$ with
   $\phi_0=(|000\rangle+|011\rangle)/\sqrt2$, and $p_1=2/3$ with
   $\phi_1=(2|000\rangle+2|011\rangle+|110\rangle)/3$.
2. For $a|000\rangle+b|011\rangle+c|110\rangle$, expanding Eq. (8) gives
   $I_1=(x+z)^2+y^2$, $I_2=x^2+(y+z)^2$, $I_3=(x+y)^2+z^2$ and
   $I_4=x^3+y^3+z^3+3xyz$, with $x=|a|^2$, $y=|b|^2$, $z=|c|^2$; diagonal
   operators on qubit $A$ and scalars keep this support.
3. Hence $\sigma_{ABC}(\psi)=8097475/3188646$, $\sigma_{ABC}(\phi_0)=5/2$ and
   $\sigma_{ABC}(\phi_1)=16792/6561$.
4. $p_0\sigma_{ABC}(\phi_0)+p_1\sigma_{ABC}(\phi_1)=8097813/3188646$ exceeds
   $\sigma_{ABC}(\psi)$ by $169/1594323$.

## Falsifier

The kernel-checked `result` is the negation of the statement that for every
three-qubit vector $\psi$ with $\sum_w|\psi(w)|^2=1$ and every finite family
$K_0,\dots,K_{n-1}$ of $2\times2$ complex matrices with
$\sum_kK_k^\dagger K_k=I$, acting on qubit $A$ through the frozen
`StabilizerPairLocalUnitaryInequivalence.localOp`, the sum over $k$ of
$p_k\,\mathrm{Re}\,\sigma_{ABC}(K_k\psi/\sqrt{p_k})$ (omitting the outcomes
with $p_k=0$) is at most $\mathrm{Re}\,\sigma_{ABC}(\psi)$. The invariants are
written as in Eq. (8), with $t_{ijk}=\psi(i,j,k)$, permutations in
`Equiv.Perm (Fin n)` and `finRotate 3` for $(123)$. The paper's
$\sigma_{ABC}$ is real valued, and $I_1,\dots,I_4$ are real for every state
($I_4$ because conjugation exchanges $P_{(123),(132)}$ and
$P_{(132),(123)}$, which coincide after relabeling the copies), so comparing
real parts is the paper's inequality. A complete instrument on one qubit is
an admissible operation in the paper's definition, so the failure refutes
the proposal.

## Evidence

Exact recomputation (Python rational arithmetic, issue #12508): the four
invariants of $\psi$, $\phi_0$ and $\phi_1$ evaluated directly from Eq. (8),
the outcome probabilities and the gap $169/1594323$; the same computation
gives the gap $166036/352218537$ for the search seat's first example
$(4|000\rangle+4|011\rangle+|110\rangle)/\sqrt{33}$ with
$K_0=\mathrm{diag}(\sqrt3/2,0)$, $K_1=\mathrm{diag}(1/2,1)$. The literature
seat recomputed both independently.

The canonical source is
`D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.lean`. Its public
declarations are `polyInvariant`, `sigmaABC`, `claim`, `psi`, `instrument`
and `result`; the operator on qubit $A$ is `localOp` of
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`.
The frozen module state has statement identity
`sha256:f88ba93e1f57e98e6ba5c8b4e46a75f8368f6997bab2d7b64e67c8ac942f3fc6`. The
result declaration has statement identity
`sha256:43b83312ba5b4895fe7531d1e06a7f9f5df119805d5ee5ecd3e9aeb20587c517`. The
Freeze event is
`sha256:ae01db2fdbce829658ccbecafe87ca4dcceb1f77f08d7af52bfebaeb019c65c3`; its
project-level frozen prerequisite is the Freeze event of
`D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence`.
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 proposal of a 2002 journal article; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation.result`.
`proof_shape: bind-only` (the settlement of the named proposal is the new
content; no escape witness); `admission_basis: open-problem-resolution`
(issue #12508). Utility kind `certified-instance`, basis `refutes` the
module's `claim`.

### What the settlement shows

- **Proved by `result`:** the proposal fails: some normalized three-qubit
  state and some complete instrument on qubit $A$ raise the average of
  $\sigma_{ABC}$.
- **Proved inside the proof of `result`:** the closed forms of
  $I_1,\dots,I_4$ on every vector supported on $|000\rangle,|011\rangle,
  |110\rangle$; for the witness $\psi$ with
  $K_0=\mathrm{diag}(3/5,0)$, $K_1=\mathrm{diag}(4/5,1)$, the values
  $\sigma_{ABC}(\psi)$, $\sigma_{ABC}(\phi_0)$, $\sigma_{ABC}(\phi_1)$ above
  and the increase $169/1594323$.
- **Mechanism (literature seat, 席位自报; checked by the orchestrator, not
  stated in Lean):** on
  $\psi_u=\sqrt{(1-u)/2}\,(|000\rangle+|011\rangle)+\sqrt u\,|110\rangle$
  the closed forms give $\sigma_{ABC}(\psi_u)=F(u)=\tfrac52+\tfrac u2+
  \tfrac{3u^2}4-\tfrac{9u^3}2+\tfrac{21u^4}4-\tfrac{9u^5}2$, and for
  $0<u<v<1$ a diagonal instrument on $A$ splits $\psi_u$ into $\psi_0$ and
  $\psi_v$ with probabilities $1-u/v$ and $u/v$. Monotonicity would make $F$
  concave along these splittings, but $F''(0)=3/2>0$; the witness is
  $u=2/27$, $v=1/9$. The family is locally equivalent (by $X$ on $B$) to
  W-class states, the region the paper's random sampling did not resolve.
- **Follows from it (orchestrator argument, not stated in Lean):** for the
  fixed instrument both outcome probabilities are positive, so the gap is
  continuous in $\psi$ and stays positive on an open set of states; replacing
  $K_0,K_1$ by $\mathrm{diag}(3/5,\varepsilon)$,
  $\mathrm{diag}(4/5,\sqrt{1-\varepsilon^2})$ with small $\varepsilon>0$
  gives invertible Kraus operators with the same strict increase. The
  failure is not confined to a set of measure zero, contrary to the
  possibility the paper allows (l. 599–602).
- **Effect on the paper's other conclusions (checked by reading the v2
  source):**
  - *Refuted:* the assumption that $\sigma_{ABC}$ is an EM (l. 589–599) and
    the proposal in the abstract (l. 22–23) of a form for the monotone
    depending on the Kempe invariant; the statement that
    $\tau_{(AB)C},\tau_{(AC)B},\tau_{(BC)A},\tau_{ABC},\sigma_{ABC}$ are five
    independent continuous EMs (§IV, l. 633–636).
  - *Needs another justification:* the use of the ratio
    $\sigma_{ABC}(\psi)/\sigma_{ABC}(\phi)$ as an upper bound on conversion
    probabilities (§III, l. 604–627); the functions $\upsilon^\pm$ built from
    the $\tau$ and $\sigma_{ABC}$ (l. 659–662); and the minimum over
    $\mathcal E=\{\tau_{(AB)C},\tau_{(AC)B},\tau_{(BC)A},\tau_{ABC},
    \sigma_{ABC},\upsilon^\pm\}$ in §V (l. 692–694, l. 800–812), where
    $\sigma_{ABC}$ can be replaced by a proved monotone depending on the
    Kempe invariant, such as the one of Oreshkov–Brun. A failure of average
    monotonicity does not by itself exhibit a pair of states violating the
    ratio bound: in the witness each term $p_k\sigma_{ABC}(\phi_k)$ is below
    $\sigma_{ABC}(\psi)$.
  - *Unaffected:* Theorem 1 (the EMs determine the LU orbit, l. 532–579) and
    its consequence that five independent continuous EMs, one of them
    depending on $I_4$, exist (l. 580–588); the four $\tau$ monotones; the
    existence arguments for EMs sensitive to $I_6$ and for an EM
    distinguishing the GHZ and W classes (§IV); Theorem 2 on $f$-type
    functions (§V).
- **Not formalized here:** the existence question the paper raises, an EM
  depending on the Kempe invariant, is answered by the proved monotone of
  Oreshkov–Brun (their Eq. (79)).
- **Open here:** the extent of the violating region of $\sigma_{ABC}$ beyond
  the W-class family.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained; the citing-work readings are
seat-reported. The Lean kernel verifies the encoded statement and its axiom
closure; its correspondence to the paper, including the permutation
conventions and the restriction to instruments on qubit $A$, is checked by
reading the source and the definitions.
