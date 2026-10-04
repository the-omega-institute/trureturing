---
slug: zhou-bash-guha-gagatsos-2023-transmissivity-in-between-probe-refutation
bibkey: zhou2023transmissivity
doi: 10.1103/PhysRevResearch.5.043033
url: https://arxiv.org/abs/2304.05539v1
triage: theorem
motivation_gids:
  - D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.result
---

# In-between-state optimality for Bayesian transmissivity sensing

## Problem

B. Zhou, B. A. Bash, S. Guha and C. N. Gagatsos, “Bayesian minimum mean
square error for transmissivity sensing”, arXiv:2304.05539v1, Section V,
p. 4, state:

> For the two-point prior PDF (15), we verify that for integer n̄ the optimal
> state is the Fock state with the same photon number. For real n̄, our numerical
> results support the conjecture that the optimal state has the form of the
> state (27), up to a phase, i.e., |Φ′ₙ̄⟩ = e^{iφn̂}|Φₙ̄⟩.

Issue [#11653](https://github.com/the-omega-institute/trureturing/issues/11653)
preregisters this Tier 1 conjecture, the quantified reading and the witness.
The two-point prior is
$P(\tau)=q\delta(\tau-\tau_0)+(1-q)\delta(\tau-\tau_1)$,
with $q,\tau_0,\tau_1\in[0,1]$.

## Motivation

A pure input has finite Fock coefficients $d_n$, Hilbert norm one and mean
photon number $\sum_n n|d_n|^2=\bar n>0$. The loss branch acts as
$K_l|n\rangle=\sqrt{\binom nl\tau^{n-l}(1-\tau)^l}|n-l\rangle$.
The output is $\rho(\tau)=\sum_l K_l|\psi\rangle\langle\psi|K_l^\dagger$,
and $\Gamma_k=q\tau_0^k\rho(\tau_0)+(1-q)\tau_1^k\rho(\tau_1)$.
For finite positive semidefinite effects summing to the identity and real
estimates, the risk is
$\sum_j\operatorname{Re}\operatorname{tr}(E_j(x_j^2\Gamma_0-2x_j\Gamma_1+\Gamma_2))$.
Lean `MMSE` is the infimum of these risks over every finite outcome count on
that input's finite output span.

Equations (27)–(29) define an adjacent-Fock superposition with coefficients
$c=\sqrt{1-\lceil\bar n\rceil+\bar n}$ and $a=\sqrt{1-c^2}$.
Equation (33) multiplies its coefficient at photon number $n$ by
$e^{i\phi n}$. The quantified `claim` asserts that, for every admissible prior,
positive mean energy and finite normalized competitor at that energy, some
phase of the in-between state has no larger finite-POVM MMSE.

## Gap

The literature search recorded in #11653 reports no settlement in its checked
arXiv and citation scope; one journal full text was inaccessible. That record
is source-reported, not a new exhaustive literature check or a priority claim.

Identifying the finite-outcome quantity with the source's MMSE over arbitrary
measurements requires the following compression argument:
if $P$ projects onto the output support, then
$\operatorname{tr}(\rho E)=\operatorname{tr}(\rho PEP)$ because
$\rho=P\rho P$. Compressed effects sum (or integrate) to the identity on
that span. A finite POVM on the span extends to full Fock space by assigning
$1-P$ to one outcome, without changing the output statistics.
**ASSUMED-UNVERIFIED:** this compression argument and the equality with the
arbitrary-outcome source MMSE are not kernel-checked in this module. In
particular, preserving outcome statistics does not by itself formalize the
passage from arbitrary outcome spaces to the infimum over finite POVMs.
The kernel-checked settlement concerns exactly the preregistered finite-POVM
`claim`; the identification with the full source reading retains this boundary.

## Route

Inside `result`, the operator variance of any finite measurement is expressed
as a sum of positive semidefinite sandwiches. For a Hermitian Sylvester
certificate $B$ with $\Gamma_0B+B\Gamma_0=2\Gamma_1$, square completion gives
$risk\geq\operatorname{Re}\operatorname{tr}(\Gamma_2-B\Gamma_1)$.
The spectral projections of $B$, estimated by its eigenvalues, attain this
bound with finitely many outcomes.

Take $q=1/2$, $\tau_0=4/9$, $\tau_1=1$, $\bar n=1/2$.
All phases of $\chi_\phi=(|0\rangle+e^{i\phi}|1\rangle)/\sqrt2$
have finite-POVM MMSE $1625/23976$. The competitor
$\psi=(\sqrt3/2)|0\rangle+(1/2)|2\rangle$ has Hilbert norm one,
mean energy $1/2$ and finite-POVM MMSE $110575/1674432$.
The gap is $107725/61953984>0$.

The certificates are

$$B_\chi=\frac1{1332}\begin{pmatrix}787&145\\145&937\end{pmatrix},\qquad
B_\psi=\frac1{93024}\begin{pmatrix}62971&0&4293\sqrt3\\0&41344&0\\4293\sqrt3&0&68965\end{pmatrix}.$$

Phase conjugation supplies the certificate for every $\chi_\phi$.

## Falsifier

The universal claim is false if one admissible prior and one normalized
competitor at a positive mean energy strictly beat every in-between phase.
This is the exhibited witness. A comparison against one phase, or against
photon counting alone, would not refute `claim`.

## Evidence

`D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.lean` exposes
`meanPhoton`, `outputState`, `momentState`, `finitePOVM`, `bayesianRisk`,
`MMSE`, `inBetween`, `claim` and the sole theorem `result : ¬ claim`.
All auxiliary facts, including spectral attainment, are local `have` terms.
`result: proof_shape: bind-only; escape_witness: none; admission_basis:
open-problem-resolution (#11653; Refuted)`. The spectral construction applies
Mathlib's spectral theorem with finite-sum and matrix normalization; the lower
bound applies upstream positive-semidefinite facts and square completion. Utility is a certified instance
refuting the designated claim. The Scribe resolution is Refuted and cites
the Library note `zhou2023transmissivity`.

## Triage

Tier 1: an externally published conjecture with a preregistered finite-POVM
reading. No atom or coverage step is associated with this settlement.

### What the settlement shows

- **Proved in this module:** adjacent photon-number support is not sufficient
  for optimality at non-integer mean energy. At the stated prior, the
  vacuum–two-photon competitor beats every phase of the adjacent
  vacuum–one-photon state, with exactly the same mean energy.
- **Proved within the result's derivation:** both witness risks are finite-POVM
  optima, certified by square completion and attained by spectral measurements.
  The failure concerns the probe family, rather than a suboptimal measurement
  of the in-between state. These are proof-internal facts, not separate public
  theorems.
- **Proved within the result's derivation:** the positive gap is
  $107725/61953984$. The lower bound holds for every finite POVM and all real
  estimates, and the in-between risk is independent of its phase.
- **Open:** global optimality of the competitor, the source's integer-energy
  optimality statement, the beta-prior conjecture and the parameter region in
  which an adjacent-Fock probe is optimal. None is settled by `result`.
- **Open source scope:** conclusions that select an in-between probe by the
  refuted universal optimality claim lose that justification. Results about
  that fixed probe's risk remain compatible with the witness. No other source
  theorem is refuted here; full-space arbitrary-outcome identification retains
  the Gap boundary.

## ASSUMED-UNVERIFIED

The written compression argument and equality between the finite-POVM MMSE
and the source's arbitrary-measurement MMSE are not
kernel-checked results of this module. The literature check in #11653 is
source-reported and bounded, including its inaccessible journal full text.
Information-escape registration is paused under CLAUDE.md section 3.9.
