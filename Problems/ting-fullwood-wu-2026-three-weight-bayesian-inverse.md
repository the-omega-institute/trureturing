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
[the literature note](../Library/QuantumStates/ting2026operational.md).

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

Issue #13585 records the literature check before any Lean: the paper has a single
version (2026-05-11); the later papers of the second author, J. Fullwood (arXiv 2608.05535,
2608.28946, 2609.38631) do not treat Pauli-channel Bayesian inverses; abstract
searches for "Bayesian inverse(s)" return only statistical inverse problems; the
repository had no Bayesian-inverse result. Zenodo title searches ("Bayesian
inverse" Pauli, "Bayesian inverses" unital) and a web search (2026-10-06) returned
no settlement. `not-found-in-searched-scope`.

## Route

1. **The maximally mixed state.** $\mathcal P$ is CPTP with Kraus operators
   $\sqrt{p_\mu}\sigma_\mu$ and fixes $\mathbb 1/2$, so $\mathcal F=\mathcal P$
   satisfies the Bayes rule there.
2. **The candidate is forced.** For $\rho=(\mathbb 1+r\cdot\sigma)/2$ the Bayes
   rule applied to $\mathbb 1$ and $\sigma_j$ determines
   $\mathcal F(\mathbb 1)$ and $\mathcal F(\sigma_j)$, hence the Choi matrix $C$ of
   any inverse.
3. **A negative direction.** With the zero weight moved to index 0 by relabelling
   the Pauli indices, $h_i=(1-p_i)r_i$ and
   $w=(\mathbb 1\otimes(\mathbb 1-h\cdot\sigma))\Omega$, one has
   $w^*Cw=-4[(1-|h|^2)B+KA]/D$ with $A=\sum p_ih_i^2$,
   $B=\sum p_i^2(1-p_i)r_i^2$, $K=\sum p_i^2r_i^2$ and $D>0$; for $r\ne0$,
   $B>0$ and $|h|<1$, so $w^*Cw<0$, contradicting complete positivity.

## Falsifier

The proof would fail if a three-weight channel had a Bayesian inverse at some
$r\ne0$, i.e. if the forced candidate's Choi matrix were positive semidefinite
there.

## Evidence

The canonical source is
`D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.lean`. Its public
declarations are `sigma`, `pauliChannel`, `jam`, `IsBayesianInverse`, `claim` and
`result`. It reuses `IsDensity` and `IsCPTP` from
`CoPRelativeQuantumnessRefutation`, `pauliMatrix` from
`StabilizerPairLocalUnitaryInequivalence`, the Bloch-matrix constructor `blochMatrix` and
the coordinates `bloch` from `ActualPureQubitGeometry`, and the Kraus and
complete-positivity API of the frozen `FiniteKrausChannel` (`of_kraus`,
`IsCompletelyPositive`, `kron_def`), from which a private Choi matrix is shown positive
semidefinite for completely positive maps. It uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
The module statement is `sha256:18fb0b24ef41e6f6a42e855742a740958fe18ed9ec2da17f5a47a1b0e518dd41`, the `result` statement `sha256:fffab424a88fcc5f205bbd74be3aa74b73e2bb02febed86307c99dbc8a817e90` and the `claim`
statement `sha256:6825cebb471df0553e0d4abd3eaf5d50adff086ada5950da15e209fe382885f7`. The Freeze event is `sha256:605cb5b2bb4f0adfca305acdaf1b010023c1563ee0ab34f616ab07fbd2825db0`; its project-level prerequisites are
`sha256:3307284b9c26f6bb5974ae0ca6c7d4566b447631a36866a1523481ec82e4f44e`,
`sha256:660a2acf7ce0c983feb172c499e9d769132164ad70999e6aa69870c316b19e21` and
`sha256:77bbff97a385bba3448f6716e34267d9410bcd2a9c7074c2a257d6fad8694717`, the frozen
`CoPRelativeQuantumnessRefutation`, `ActualPureQubitGeometry` and
`StabilizerPairLocalUnitaryInequivalence`.

Numerical check (the paper's coefficient formulas for the unique candidate,
validated by a Bayes-rule residual below $10^{-15}$): 20 000 random three-weight
channels with random states (10% pure) all give a Choi matrix with a negative
eigenvalue; the witness identity of the Route holds to $7\times10^{-16}$; positive
controls: the depolarizing channel at small $r$ and every three-weight channel at
$\rho=\mathbb 1/2$ give positive semidefinite candidates.

## Triage

Tier 1 unresolved alternative of a 2026 paper, preregistered in issue #13585
before any Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every private theorem (`sigma_properties`, `channel_self_adjoint`,
`channel_unital`, `channel_cptp`, `mixed_inverse`, `state_eq_spin`, `density_coordinates`,
`choi_psd`, `choi_bayes`, `scaled_sylvester`, `channel_bloch`, `witness_strict`,
`support_zero`, `witness_numerator`, `inverse_only_mixed`) is bind-only and is used
on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`: the module proves a universal statement and
contains no finite enumeration, checker, numeric reduction or certified instance.
There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every Pauli channel with exactly three non-zero
weights, a Bayesian inverse with respect to a qubit state exists exactly at the
maximally mixed state; this is the first alternative of the paper's sentence,
which also implies its second.

**Established inside the proof.** The obstruction is a single explicit direction:
the Choi matrix of the forced candidate is negative on
$(\mathbb 1\otimes(\mathbb 1-h\cdot\sigma))\Omega$ as soon as $r\ne0$, with a
closed-form value (`witness_numerator`, `witness_strict`).

**Argued, not formalized.**

- The number of non-zero weights orders the invertible states: one weight (a
  unitary channel) gives every state; two weights give a coordinate axis (the
  paper's Section III); three weights give only $\mathbb 1/2$ (here); four positive
  weights give a neighbourhood of $\mathbb 1/2$, because the Choi matrix of
  $\mathcal P$ has eigenvalues $2p_\mu>0$ and the forced candidate depends
  continuously on $r$ (computed: 2 000 random four-weight channels are positive
  semidefinite at small $r$).
- At three weights the Choi matrix of $\mathcal P$ has a zero eigenvalue (the Bell
  vector of the missing Pauli), so the four-weight continuity argument is not
  available, and the explicit witness shows that the forced candidate leaves the
  positive cone for every $r\ne0$.

**Open.** The paper's inequalities for four weights are not evaluated in general,
and unital channels are treated only through their associated Pauli channels.

**Effect on the paper.** The Section V alternative is settled in its first form:
three-weight Pauli channels, and by the paper's unitary-equivalence proposition
every unital qubit channel whose associated Pauli channel has three non-zero
weights, admit operational time reversal only at the maximally mixed state. The
paper's other results are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
