---
slug: meunson-deesuwan-2026-cop-relative-quantumness-refutation
bibkey: meunson2026cumulant
doi: 10.48550/arXiv.2606.31205
url: https://arxiv.org/abs/2606.31205v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.result
---

# Conjecture 15 fails for a commutativity-preserving qubit channel

## Problem

A. Meunson and T. Deesuwan, *Cumulant-based quantum relative Rényi
functional*, arXiv:2606.31205v1, Section VIII.A, PDF p. 18, conjecture the
following data-processing inequality at alpha zero:

> Let rho and sigma be noncommuting density matrices, with regularized states
> rho_epsilon and sigma_epsilon. If N is a commutativity-preserving CPTP
> channel and the support of N(rho_epsilon) is contained in that of
> N(sigma_epsilon), then Q(rho_epsilon || sigma_epsilon) is at least
> Q(N(rho_epsilon) || N(sigma_epsilon)), which is at least zero.

The literal source formulas and sentences are in
[the literature note](../Library/QuantumStates/meunson2026cumulant.md).
The source's malformed pair `\rho,\sigma)` is transcribed literally there;
the Blueprint display uses the normalized pair `(rho,sigma)`.

Equation `state_regularized` defines

$$A_\varepsilon=(1-\varepsilon)A+\frac{\varepsilon}{d}I,
\qquad 0<\varepsilon<1.$$

Equation `regularized_Cu-Q` and the definition of relative quantumness give

$$Q(A\Vert B)=-S_0^Q(A\Vert B)
=\ln\operatorname{Tr}\left[A\exp(\ln B-\ln A)\right].$$

Density means positive semidefinite with trace one. CPTP means complete
positivity at every finite amplification and trace preservation on every
matrix. CoP quantifies over every pair of commuting density matrices.
Support is the operator range. The Lean claim includes both conclusion
inequalities and all source hypotheses. It quantifies over `d : ℕ` and
complex matrices on `Fin d`; one witness with `d = 2` refutes that universal
claim. Every matrix logarithm in the witness is of a positive definite matrix,
so the refutation uses no convention for a singular output logarithm.

## Motivation

Let X and Z be the Pauli matrices, and put

$$t_n=\frac{4^n-1}{4^n+1},\quad
H=\frac{11Z+5\sqrt3 X}{14},\quad
J=\frac{29Z+\sqrt{455}X}{36}.$$

The regularized states and their channel outputs are

$$R=\frac{I+t_7Z}{2},\quad S=\frac{I+t_8H}{2},\quad
R'=\frac{I+t_6Z}{2},\quad S'=\frac{I+t_3J}{2}.$$

Set epsilon to `1/65537` and take

$$\rho=\frac I2+\frac{t_7}{2(1-\varepsilon)}Z,\qquad
\sigma=\frac I2+\frac{t_8}{2(1-\varepsilon)}H.$$

The unital map fixes I and sends X to `u X + v Z`, Y to `u w Y`, and Z to
`w Z`, where

$$u=\frac{3211313}{127793250}\sqrt{1365},\quad
v=-\frac{727356123473}{168188824118250}\sqrt3,\quad
w=\frac{22365525}{22373717}.$$

It sends R to R' and S to S'. The raw states rho and sigma are noncommuting
density matrices, and R', S' are positive definite. The trace arguments are
exactly

$$\operatorname{Tr}[R\exp(\ln S-\ln R)]
=\frac{50401283}{7340144}
<\frac{1879639}{266240}
=\operatorname{Tr}[R'\exp(\ln S'-\ln R')].$$

Strict monotonicity of the real logarithm gives a strict increase of Q.

## Gap

Issue [#11472](https://github.com/the-omega-institute/trureturing/issues/11472)
preregisters the published first-tier conjecture, its full quantified reading,
the witness, and the Choi or equivalent four-Kraus route before the probe.
The preregistration's bounded literature readings cover the paper, its earlier
2025 study, Semantic Scholar citations, MathDB, formal-conjectures, and the
repository. No prior settlement was found in those readings. The implementation
seat independently confirmed the DOI and read the MathDB public page, whose
progress and solution panels state “Nothing recorded yet” and “No solutions
have been posted yet.” These are bounded observations, not a priority claim.

## Route

Only the frozen `FiniteKrausChannel` module and pinned Mathlib are imported.
For `a=(1+u)(1+w)`, `b=(1-u)(1+w)`, and
`delta=(1-u^2)(1-w^2)-v^2`, the four Kraus matrices are

$$\sqrt{a/4}\begin{pmatrix}1&v/a\\-v/a&1\end{pmatrix},\quad
\sqrt{\delta/(4a)}\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
\sqrt{b/4}\begin{pmatrix}1&v/b\\v/b&-1\end{pmatrix},\quad
\sqrt{\delta/(4b)}\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$

Their Kraus sum equals the channel entrywise. Complete positivity follows by
direct application of `MatrixMap.of_kraus_isCompletelyPositive`. Trace
preservation and preservation of arbitrary commuting qubit matrices follow
from entrywise identities. Two-point functional calculus for self-adjoint
involutions evaluates both matrix exponentials and both traces exactly.

The public surface consists of `IsDensity`, `reg`, `Q`, `IsCPTP`, `IsCoP`,
`supp`, `claim`, and the single theorem `result : ¬ claim`. Witness matrices
are private data definitions. All auxiliary propositions occur as local
`have` proofs inside `result`; there are no companion or private theorems.

## Falsifier

The source claim is false once a CPTP CoP map, two noncommuting density
matrices, epsilon in `(0,1)`, and output support inclusion give a strict
increase of Q. Each hypothesis and the strict increase are checked on the
same qubit witness. The proof closes by applying the claimed universal
inequality to this witness and contradicting its first conjunct.

## Evidence

The canonical declaration is
`D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.result`.
Its proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
An independent symbolic recomputation gives

| quantity | exact value |
| --- | --- |
| u squared | `72187718287783/83749306387500` |
| delta | `4538306603684502857840557/100926936806701406237100062500` |
| output trace minus input trace | `23623958881/122139996160` |

All three are positive. The symbolic computation also verifies the channel
images, H squared = I, J squared = I, and the squared logarithmic difference
involutions. The formal theorem supplies the kernel-checked refutation;
the symbolic readings are independent supporting calculations.

## Triage

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The module's utility is `certified-instance` with a typed `refutes` edge to
`claim`. The external named-problem exception applies; there is no digestion
atom or coverage edge. All definitions are needed to state this settlement.

### What the settlement shows

**Proved by `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.result`:**
complete positivity, trace preservation, preservation of commuting pairs,
and full-rank outputs do not
suffice for the proposed monotonicity. CoP constrains the image of pairs with
zero commutator; it supplies no bound on the logarithmic trace for
noncommuting pairs. The Bloch map sends X to `u X+v Z`, so it mixes the two
input directions while keeping all parallel directions parallel. The exact
trace gap identifies the quantitative failure. Restricting to qubits or
requiring positive definite outputs cannot repair this conjecture.

**Computed and independently checked:** the explicit channel fixes the
identity matrix, so adding unitality cannot repair the conjecture. This
identity is checked as a transient exact Lean example. Both trace arguments exceed one,
so Q is positive at both the input and output of this witness. The
nonnegativity half of the conjecture is not refuted by this example.
Identity-channel monotonicity is equality by substitution. These statements
are checked as transient exact Lean examples, not added as public theorems.

**Open:** universal monotonicity for narrower channel families, including
those sampled in the paper, needs a separate theorem or counterexample.
This settlement gives neither a necessary and sufficient replacement
condition nor a classification of all channels that contract Q.

**Consequences for the source:** Section VIII.B's reported finite Monte Carlo
samples remain sample results; they cannot establish the universal CoP-QDPI.
The inference in its concluding discussion from the tested channel families
to all CoP channels fails. The preceding alpha-zero nonpositivity theorem for
S and the zero-quantumness characterization of commuting states do not depend
on Conjecture 15 in the source and are not refuted by this witness. Their
universal statements are not formalized in this delivery. The separate
positive-alpha numerical investigation remains a separate unresolved question.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not established.
The broader citation and corpus readings are orchestrator-reported.
Source fidelity and bind-only classification remain semantic review judgments.
Escape-audit registration is unfinished: no faithful registration with the
required source bridge, variation and sensitivity evidence is delivered.
