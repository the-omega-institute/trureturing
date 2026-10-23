---
slug: ting-fullwood-wu-2026-three-weight-bayesian-inverse
bibkey: ting2026operational
doi: 10.48550/arXiv.2605.10375
url: https://arxiv.org/abs/2605.10375v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result
---

# Three-weight Pauli channels have Bayesian inverses only at the maximally mixed state

## Problem

O. Ting, J. Fullwood and Z. Wu, *Operational time-reversal symmetry for unital
qubit channels*, arXiv:2605.10375v1, call a channel $\mathcal F$ a Bayesian
inverse of $\mathcal E$ with respect to $\rho$ when
$\{\mathcal E(\rho)\otimes\mathbb 1,\mathscr J[\mathcal F]\}=\{\mathbb 1\otimes\rho,\mathscr J[\mathcal E^\dagger]\}$,
$\mathscr J[\mathcal N]=(\mathrm{id}\otimes\mathcal N)(\mathtt{SWAP})$. For Pauli
channels $\mathcal P(A)=\sum_\mu p_\mu\sigma_\mu A\sigma_\mu$ they settle the case of
two non-zero weights and characterize the general case by three inequalities, and
in Section V state that for exactly three non-zero weights they found no Bayesian
inverse away from the maximally mixed state, which is "probably due to the fact
that either the maximally mixed state is the only state for which a Bayesian
inverse exists in such a case, or that such states are restricted to a
measure-zero subset of the Bloch ball". The verbatim statements are in
[the literature note](../Library/QuantumChannels/ting2026operational.md).

Issue [#13585](https://github.com/the-omega-institute/trureturing/issues/13585)
fixes the reading: for every probability vector with exactly three non-zero
entries and every qubit density matrix $\rho$ (pure states included), a CPTP
Bayesian inverse of $\mathcal P$ with respect to $\rho$ exists if and only if
$\rho=\mathbb 1/2$; $\mathcal P^\dagger=\mathcal P$ is part of the statement.

## Motivation

A Bayesian inverse is the operational time reversal of a sequential measurement
through the channel. The question is whether three-weight Pauli noise, the generic
case between the two-weight channels (a coordinate axis of invertible states) and
the four-weight channels such as depolarizing noise (a neighbourhood of the
maximally mixed state, the paper's Fig. 1), still admits any time-reversal symmetry
away from the maximally mixed state.
`D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.result` shows it
does not.

## Gap

Section IV characterizes Bayesian-inverse existence by three Choi inequalities
without evaluating the three-weight case. The Section V alternative is the
question addressed here. The source and the preregistered full statement in
[#13585](https://github.com/the-omega-institute/trureturing/issues/13585) specify
all probability vectors with exactly three nonzero weights and all qubit density
matrices. A bounded literature search found no separate settlement in the
searched scope; it does not establish worldwide novelty or priority.

## Route

1. **The maximally mixed state.** $\mathcal P$ is CPTP with Kraus operators
   $\sqrt{p_\mu}\sigma_\mu$ and fixes $\mathbb 1/2$, so $\mathcal F=\mathcal P$
   satisfies the Bayes rule there. Cyclicity of trace and Hermiticity of the
   Pauli matrices prove $\mathcal P^\dagger=\mathcal P$ for all matrix arguments.
2. **The scaled candidate.** Write
   $\rho=(\mathbb 1+r\cdot\sigma)/2$ with $\sum_i r_i^2\leq1$ and
   $s_i=\lambda_i r_i$, where
   $\lambda=(p_0+p_1-p_2-p_3,p_0-p_1+p_2-p_3,p_0-p_1-p_2+p_3)$.
   For the canonical Choi convention
   $C_{(j_1,i_1),(j_2,i_2)}=\mathcal F(|i_1\rangle\langle i_2|)_{j_1j_2}$,
   the expanded Jam Bayes rule is exactly
   $C+(VC+CV)/2=R$, where
   $V=\mathbb 1\otimes(s\cdot\sigma)^{\mathsf T}$ and
   $R=\{\rho\otimes\mathbb 1,C(\mathcal P)\}$.
   Since $V^2=|s|^2\mathbb 1$, the Sylvester identity gives
   $$D C=(1-|s|^2/2)R-(VR+RV)/2+VRV/2,\qquad D=1-|s|^2\geq0.$$
3. **A negative direction.** If $p_k=0$, let $a_1,a_2,a_3$ be the other three
   weights, listed through the Pauli product table, and $h_i=(1-a_i)r_i$.
   The vector $w(j,i)=((\mathbb 1-h\cdot\sigma)\sigma_k)_{ji}$ is indexed
   by output $j$ and input $i$. For all four choices of $k$ it satisfies
   $$w^*(D C)w=-4[(1-|h|^2)B+KA],$$
   where $A=\sum_i a_i h_i^2$,
   $B=\sum_i a_i^2(1-a_i)r_i^2$ and $K=\sum_i a_i^2r_i^2$.
   The three active weights lie strictly between zero and one. If $r\ne0$,
   then $B>0$ and $|h|<1$, while $K,A\geq0$. The displayed value is therefore
   negative. Complete positivity makes $C$ positive semidefinite; scaling
   by $D\geq0$ preserves positive semidefiniteness, a contradiction.

The Lean argument never divides by $D$ and includes pure states. As explanatory
algebra, exactly three positive weights imply $|\lambda_i|<1$, hence $D>0$
throughout the closed Bloch ball. The same Sylvester identity then fixes the
candidate uniquely and yields the equivalent expression
$w^*Cw=-4[(1-|h|^2)B+KA]/D<0$. These strict-denominator and uniqueness
consequences are not additional Lean conclusions.

## Falsifier

The proof would fail if a three-weight channel had a Bayesian inverse at some
$r\ne0$, i.e. if the forced candidate's Choi matrix were positive semidefinite
there.

## Evidence

The mathematical source is
`D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.lean`.
Its public definitions are `sigma`, `pauliChannel`, `jam`, `IsBayesianInverse`
and `claim`; `result` proves the complete claim. `IsDensity` and `IsCPTP` are
owned by `CoPRelativeQuantumnessRefutation`, and `pauliMatrix` by
`StabilizerPairLocalUnitaryInequivalence`. Density coordinates use
`bloch_geometry_of_isHermitian` and `norm_bloch_le_trace_of_posSemidef` from
`ActualPureQubitGeometry`, with `EuclideanSpace.real_norm_sq_eq` supplying the
coordinate norm identity. The Choi matrix and its CP-to-PSD implication are
`MatrixMap.choi_matrix` and `MatrixMap.choi_PSD_iff_CP_map` from
`FiniteKrausRepresentation`; the Kraus construction uses `FiniteKrausChannel`.

[#13585](https://github.com/the-omega-institute/trureturing/issues/13585) reports
numerical experiments using the paper's coefficient formulas: 20 000 random
three-weight channels and states (10% pure) gave negative candidate Choi
eigenvalues; the reported Bayes-rule residual was below $10^{-15}$, and the
witness-identity residual was at most $7\times10^{-16}$. Its positive controls
were depolarizing noise at small $r$ and three-weight channels at
$\rho=\mathbb 1/2$. These are source-reported numerical results, not independent
replications or substitutes for the universal proof.

## Triage

Tier 1: an unresolved alternative in the cited paper. The complete Pauli
statement is the conclusion of `result`; the associated unital-channel
application below additionally uses the paper's Proposition 1.

### What the settlement shows

**Proved by `result`:** for every Pauli channel with exactly three non-zero
weights, a Bayesian inverse with respect to a qubit state exists exactly at the
maximally mixed state; this is the first alternative of the paper's sentence,
The singleton conclusion also gives the measure-zero alternative under the
usual Lebesgue measure on the Bloch ball; that measure statement is not part of
`result`.

**Established inside the proof.** The obstruction is a single explicit direction:
the scaled Choi matrix $DC$ is negative on the vector
$w(j,i)=((\mathbb 1-h\cdot\sigma)\sigma_k)_{ji}$ as soon as $r\ne0$, with a
closed-form value (`witness_numerator`, `witness_strict`). The corresponding
divided Choi value uses the strict-denominator algebra described above.

**Argued, not formalized.**

- The number of non-zero weights orders the invertible states: one weight (a
  unitary channel) gives every state; two weights give a coordinate axis (the
  paper's Section III); three weights give only $\mathbb 1/2$ (here); four positive
  weights give a neighbourhood of $\mathbb 1/2$, because the Choi matrix of
  $\mathcal P$ has eigenvalues $2p_\mu>0$ and the forced candidate depends
  continuously on $r$ (the original dossier reports 2 000 random four-weight channels positive
  semidefinite at small $r$; this numerical result is not independently replicated).
- At three weights the Choi matrix of $\mathcal P$ has a zero eigenvalue (the Bell
  vector of the missing Pauli), so the four-weight continuity argument is not
  available, and the explicit witness shows that the forced candidate leaves the
  positive cone for every $r\ne0$.

**Open.** The paper's inequalities for four weights are not evaluated in general,
and unital channels are treated only through their associated Pauli channels.

**Effect on the paper.** The Section V alternative is settled in its first form:
three-weight Pauli channels, and by the paper's unitary-equivalence proposition
every unital qubit channel whose associated Pauli channel has three non-zero
weights, admit operational time reversal only at the maximally mixed state.
Precisely, for $\mathcal N=\mathcal U\circ\mathcal E\circ\mathcal V$,
Proposition 1 maps $\rho$ to $\mathcal V^\dagger(\rho)$ and $\mathcal F$
to $\mathcal V^\dagger\circ\mathcal F\circ\mathcal U^\dagger$; unitary
conjugation fixes $\mathbb 1/2$ in both directions. This transport is a cited
application, not part of `result`. Operational reversal preserves the specified
sequential measurement correlations; it gives no arbitrary-state physical
noise inversion or resource bound. The paper's two-weight theorem and general four-weight inequalities have
their original scope; the three-weight conclusion does not strengthen them.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
