---
slug: ganardi-2022-negativity-ppt-distance
bibkey: ganardi2022hierarchy
doi: 10.22331/q-2022-02-16-654
url: https://arxiv.org/abs/2111.11887v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result
---

# Negativity and the partial transpose distance to the PPT states

## Problem

R. Ganardi, M. Miller, T. Paterek, M. Żukowski, *Hierarchy of correlation
quantifiers comparable to negativity*, Quantum 6, 654 (2022),
arXiv:2111.11887v2, Conjecture 1:

> Let $\rho$ be a density matrix. Then
> $\inf_{\sigma \in \mathrm{PPT}} d_T(\rho, \sigma) = N(\rho)$.

Here $d_T(\rho,\sigma)=\frac12\|\rho^{T_B}-\sigma^{T_B}\|_1$ is the partial
transpose distance, $N(\rho)=\frac12(\|\rho^{T_B}\|_1-1)$ is the negativity,
$T_B$ is the partial transpose on the second system, and PPT is the set of
states with $\sigma^{T_B}\ge0$. The triangle inequality gives
$N(\rho)\le\inf_\sigma d_T(\rho,\sigma)$, so the conjecture asserts the
reverse inequality.

## Motivation

The conjecture would make the negativity a member of a family of
distance-based correlation measures built from one distance, so that
entanglement measured by negativity could be compared with discord and total
correlations measured by the same distance. The paper proves the equality
for states of positive binegativity ($|\rho^{T_B}|^{T_B}\ge0$), which
include all pure states and all two-qubit states. The frozen declaration
`D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result`
shows that the equality fails in general.

## Gap

Issue #12452 classifies the conjecture as Tier 1 and records the checks
made before any Lean:

- arXiv:2111.11887 v2 is the latest version and states the conjecture; the
  authors report $10^6$ random states of two qudits for each $d=2,\dots,6$
  without a counterexample, and R. Ganardi's thesis (Gdańsk 2022) calls the
  general case open;
- Zaw, arXiv:2403.16441v2 (Phys. Rev. Lett. 133, 050201 (2024)), keeps the
  equality as a conjecture; the other citing works listed by Quantum do not
  address it;
- a gap between the κ-entanglement and the logarithmic negativity does not
  refute the conjecture: the paper reports agreement for such states, and
  the Wang–Wilde state of arXiv:1809.09592v2 satisfies the equality;
- the counterexample state belongs to the punch-card family of
  Lami–Mele–Regula, arXiv:2405.09613v2 (Phys. Rev. Lett. 134, 090202
  (2025)), Eq. (15), introduced there for the additivity of the
  κ-entanglement, a different question.

These are seat-reported and orchestrator-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $\rho=R/34$ on two qutrits, with $R=|v\rangle\langle v|+4(|02\rangle
   \langle02|+|20\rangle\langle20|+|12\rangle\langle12|+|21\rangle\langle21|)$
   and $v=|00\rangle+|11\rangle+4|22\rangle$.
2. $\rho^{T_B}=P-B$ with $B=\frac1{68}|c\rangle\langle c|$,
   $c=|01\rangle-|10\rangle$, and $P$ an explicit sum of positive rank-one
   and diagonal terms; $\mathrm{Tr}\,P=35/34$ and $\mathrm{Tr}\,B=1/34$, so
   $\|\rho^{T_B}\|_1\le36/34$ and $N(\rho)\le1/34$.
3. The signed permutation matrices $U_1,U_2,U_3$ (diagonal signs, and the
   swaps of $|02\rangle,|20\rangle$ and of $|12\rangle,|21\rangle$) are
   unitary, so $\mathrm{Re}\,\mathrm{Tr}(U_kX)\le\|X\|_1$; with
   $F=\frac13U_1+\frac16U_2+\frac12U_3$, $\mathrm{Re}\,\mathrm{Tr}(FX)\le
   \|X\|_1$.
4. $\mathrm{Tr}(F\rho^{T_B})=\frac7{17}$, and for every matrix $\sigma$,
   $\mathrm{Tr}(F\sigma^{T_B})=\frac13\mathrm{Tr}\,\sigma-\frac13\langle b|
   \sigma|b\rangle-\frac43\langle c|\sigma^{T_B}|c\rangle$ with
   $b=2|00\rangle+2|11\rangle-|22\rangle$; for a PPT state both quadratic
   forms are nonnegative, so $\mathrm{Re}\,\mathrm{Tr}(F\sigma^{T_B})\le
   \frac13$.
5. Hence $d_T(\rho,\sigma)\ge\frac12(\frac7{17}-\frac13)=\frac2{51}$ for every
   PPT state $\sigma$, and the infimum, over a nonempty set, is at least
   $\frac2{51}>\frac1{34}\ge N(\rho)$.

## Falsifier

The kernel-checked `result` is the negation of the statement that for every
$d$ and every density matrix $\rho$ on $\mathbb C^d\otimes\mathbb C^d$
(`IsDensity`, positive semidefinite with trace one), the infimum of
$\frac12\|\rho^{T_B}-\sigma^{T_B}\|_1$ over the density matrices $\sigma$
with $\sigma^{T_B}$ positive semidefinite equals
$\frac12(\|\rho^{T_B}\|_1-1)$. The partial transpose is the frozen
`partialTransposeB` (on the second factor) and the trace norm is the frozen
`FiniteTraceDistance.traceNorm`, $\mathrm{Re}\,\mathrm{Tr}\sqrt{A^\dagger A}$.
The equal-dimension statement is a special case of Conjecture 1, so its
failure refutes the conjecture.

## Evidence

Exact recomputation (SymPy, issue #12452): $34\rho^{T_B}$ has spectrum
$-1,1,1,1,8,8,16,0,0$, so $N(\rho)=1/34$; $\rho^{T_B}=P-B$;
$U_k^2=I$; $F=\frac13I-(\frac13|b\rangle\langle b|)^{T_B}-\frac43|c\rangle
\langle c|$; $\mathrm{Tr}(U_k\rho^{T_B})=-\frac1{17},-\frac1{17},
\frac{15}{17}$; and the identity of step 4 for a symbolic $9\times9$
matrix. The literature seat recomputed all values independently.

The canonical source is
`D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.lean`.
Its public declarations are `claim`, `witness` and `result`; the partial
transposition and `IsDensity` are frozen in
`D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation`, and
the trace norm with its unitary characterization, triangle inequality and
value on positive matrices in `D5/S3/Quantum/Foundation/FiniteTraceDistance`.
The frozen module state has statement identity
`sha256:31daa626b61549aff782cc922e91c9c221ed234b9ae3b8ae49abf57c324684cf`. The
result declaration has statement identity
`sha256:6e60470ff4128cd1ee4254cc12b96181b07ab9450ba2e609d807f31c574156cc`. The
Freeze event is
`sha256:91e2571bb81a148bd8d8e313a964edb4bb62a1c181700c24db1bf44497bdaaeb`; its
project-level frozen prerequisites are the Freeze events of
`D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation` and
`D5/S3/Quantum/Foundation/FiniteTraceDistance`. The
proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2022 journal article; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result`.
`proof_shape: bind-only` (the settlement of the named conjecture is the new
content; no escape witness); `admission_basis: open-problem-resolution`
(issue #12452). Utility kind `certified-instance`, basis `refutes` the
module's `claim`.

### What the settlement shows

- **Proved by `result`:** Conjecture 1 fails for a rank-five two-qutrit
  state, whose negativity is at most $1/34$ while its partial transpose
  distance to every PPT state is at least $2/51$.
- **Proved inside the proof of `result`, for this state only:**
  $\|\rho^{T_B}\|_1\le36/34$, and
  $\frac12\|\rho^{T_B}-\sigma^{T_B}\|_1\ge2/51$ for every PPT state
  $\sigma$.
- **Computed, not stated in Lean (orchestrator, high-precision check of the
  literature seat's certificates):** the exact distance is
  $(24-4\sqrt{34})/17\approx0.03978$, attained by an explicit PPT state
  supported on the same blocks and certified by a member of the same
  witness family, so the gap to $N(\rho)=1/34$ is about $0.0104$.
- **Mechanism (literature seat, 席位自报; not stated in Lean):** by the
  paper's alternative form (Appendix B), the equality holds iff some PPT
  state $\tau$ satisfies $\tau\le(\rho^{T_B})_+$. In the family
  $R_t=|v_t\rangle\langle v_t|+t\sum_{ij\in\{02,20,12,21\}}|ij\rangle\langle
  ij|$, $v_t=|00\rangle+|11\rangle+t|22\rangle$, the largest trace of a PPT
  $T\le(R_t^{T_B})_+$ is $t^2+3+2\sqrt3\,t$, which reaches
  $\mathrm{Tr}\,R_t=t^2+4t+2$ exactly when $t\le(2+\sqrt3)/2$; the state
  here is $t=4$. The orchestrator checked the endpoint $t=1$, the
  unfiltered punch-card state $R_1/7$ of Lami–Mele–Regula: an explicit PPT
  state attains $d_T=1/7=N$, so that state satisfies the equality and the
  failure comes from the local filtering.
- **Follows from it (orchestrator check of the witness):** the mixtures
  $(1-\varepsilon)\rho+\varepsilon I/9$ with $0<\varepsilon<9/196$ are
  full-rank counterexamples, since $\mathrm{Tr}\,F=-8/3$ gives
  $\mathrm{Tr}(F\rho_\varepsilon^{T_B})=\frac7{17}-\frac{325}{459}\varepsilon$
  and $N(\rho_\varepsilon)=\frac{1-\varepsilon}{34}-\frac\varepsilon9$; so
  the failure is not confined to rank-deficient states, and counterexamples
  form an open set.
- **Open here:** the smallest local dimensions in which the equality fails
  (two qubits satisfy it by positive binegativity; qubit–qutrit systems were
  not examined); the largest possible gap between the PPT distance and the
  negativity; and the relation of the PPT distance to the exact PPT
  entanglement cost.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained; the citing-work readings are
seat-reported. The Lean kernel verifies the encoded statement and its axiom
closure; its correspondence to the paper, including the restriction to
equal local dimensions and the second-system partial transpose, is checked
by reading the source and the definitions.
