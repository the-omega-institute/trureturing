---
slug: abdelkhalek-et-al-2015-optimal-state-independence-refutation
bibkey: abdelkhalek2015optimality
doi: 10.1142/S0219749915500458
url: https://arxiv.org/abs/1509.00398v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result
---

# Optimal quantum states depend on the Rényi orders

## Problem

Kais Abdelkhalek, René Schwonnek, Hans Maassen, Fabian Furrer, Jörg Duhme,
Philippe Raynal, Berthold-Georg Englert and Reinhard F. Werner,
“Optimality of entropic uncertainty relations”, arXiv:1509.00398v1,
section V.E, Conjecture V.8 (Independence of the optimal states of
$(\alpha,\beta)$), state:

> If $\rho$ is an optimal state for any unitary operator and any
> $\alpha,\beta>\frac12$ satisfying the duality relation (2), then
> $\rho$ is also an optimal state for all other dual pairs.

The relation is $1/\alpha+1/\beta=2$. Section II defines
$f(\rho)=(H_\alpha(p_X^\rho),H_\beta(p_Y^\rho))$ and
$\rho\sqsubseteq\sigma$ by both entropy coordinates being at most
those of $\sigma$. Its definition of optimality is:

> We call a state $\rho$ optimal if $\rho'\sqsubseteq\rho$ implies
> $\rho\sqsubseteq\rho'$, and hence $f(\rho)=f(\rho')$.

The formal claim quantifies over all natural dimensions, complex unitaries,
complex positive trace-one density matrices, and both finite real dual pairs
with every order strictly above $1/2$. The source explicitly excludes
$\{1/2,\infty\}$. Issue [#11782](https://github.com/the-omega-institute/trureturing/issues/11782)
preregisters this reading and the refutation before any Lean probe.

## Motivation

The frozen declaration
`D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result`
refutes the universal conjecture. An X basis projector on $\mathbb C^3$
is Pareto optimal for $(1,1)$ but is strictly dominated for $(3/5,3)$.
Optimality at the first pair is proved against every density state,
including mixed competitors.

## Gap

The preregistration classifies this as a Tier 1 conjecture from quant-ph.
The bounded literature check reads the arXiv v1 source and the distinct
additivity question in arXiv:1801.04602; arXiv:2303.11382 concerns a different
conjecture. The recorded MathDB query “Pareto optimal entropic uncertainty”
has no matching entry. The preregistration discloses that its citation search did not read all
citing works. The result is
`not-found-in-searched-scope`, without a literature-priority claim.

The Library note `D5/L/QuantumStates/abdelkhalek2015optimality` preserves the
source locators, entropy convention and limits of the journal comparison.

## Route

Take the real orthogonal overlap matrix

$$
U=\begin{pmatrix}
\sqrt2/2&\sqrt2/2&0\\
\sqrt2/4&-\sqrt2/4&\sqrt3/2\\
\sqrt2\sqrt3/4&-\sqrt2\sqrt3/4&-1/2
\end{pmatrix}.
$$

Its squared row entries give the Y laws of the X basis projectors:
$p_0=(1/2,1/2,0)$, $p_1=(1/8,1/8,3/4)$ and
$p_2=(3/8,3/8,1/4)$. Every X law is a point mass.

At $(1,1)$, a dominating density state has zero X Shannon entropy.
The frozen point-mass characterization and the positive-semidefinite
zero-quadratic-form characterization force it to be an X basis projector.
The three Y Shannon entropies are
$\log2$, $(9/4)\log2-(3/4)\log3$, and
$(11/4)\log2-(3/4)\log3$. The last two exceed the first because
$27<32$ and $\log2>0$. Only the first projector weakly dominates the first projector at (1,1).

At $(3/5,3)$, the second projector has the same zero X entropy and
Y entropy $-(1/2)\log(109/256)<\log2$, since $1/4<109/256$.
It strictly dominates the first projector. Both pairs satisfy duality.
Natural logarithms preserve the paper's entropy-coordinate order because
conversion from base two multiplies by a positive constant.

## Falsifier

The witness must be a complex unitary, both projectors must be positive
and trace one, all four orders must exceed $1/2$, and both duality equations
must hold. Optimality at $(1,1)$ must quantify over all density matrices,
not merely the three exhibited projectors. The proof checks these
obligations and the strict inequality at the second pair. A restriction to
Maassen–Uffink equality states would be a different claim.

## Evidence

The canonical source is
`D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.lean`.
Its public declarations are `pX`, `pY`, `H`, `Below`, `Optimal`, `claim`,
and the sole public theorem `result : ¬ claim`. Density states reuse
`FiniteStateChannel.DensityState (Fin d)`, and the basis projectors directly
reuse the frozen `OrthogonalRecordEntropy.pointerState` specialized to
`Fin d`; the density-state carriers are definitionally equal. Matrix conversion
directly uses `CStarMatrix.ofMatrix.symm`. No duplicate carrier or matrix definition is
introduced. All numerical comparisons in the proof are exact. The Shannon optimality
argument is in source lines 234–254 and the order-three refutation is in
lines 255–269, within `result`.

The result has axiom closure `propext`, `Classical.choice`, `Quot.sound`,
with no new axiom or `sorry`. The Scribe resolution is `Refuted` and names
this dossier and the frozen result.

## Triage

Tier 1; resolution `Refuted`; `admission_basis: open-problem-resolution`
under the external named-problem exception in CLAUDE.md §3.2.
`proof_shape: bind-only`; `escape_witness: none`. The settlement combines
frozen Shannon results, upstream positive-semidefinite matrix results,
and exact matrix/logarithm normalization. The private witness definitions
serve this one refutation; normalization facts are local to its proof.
Utility is `certified-instance` with a typed `refutes` claim/result pair.
There is no digestion atom or coverage transaction.
Information-escape registration is paused under CLAUDE.md §3.9 「信息逃逸登记暂缓」.

### What the settlement shows

- **Proved in this module:** zero X Shannon entropy and positivity force
  a density matrix to be a basis projector. This excludes mixed competitors
  at the Shannon endpoint. For the exhibited matrix, the first projector is
  optimal there and the second strictly dominates it at $(3/5,3)$.
- **Proved in this module:** the Y ordering of $p_0$ and $p_1$ reverses
  between orders one and three, while their X entropies remain zero.
  The X entropy of every basis projector remains zero at every finite positive order.
  The failure mechanism is order-dependent ranking of these unequal
  probability laws. Real orthogonal measurements and pure witnesses
  already suffice; complex phases and mixed witnesses are unnecessary.
- **Computed:** the descending prefix sums of $p_0$ and $p_1$ at ranks
  one and two are $(1/2,1)$ and $(3/4,7/8)$ respectively. The larger prefix
  changes sides, so these two laws are majorization-incomparable.
  Reproduce with `python3 -c 'from fractions import Fraction as F; from itertools import accumulate; print([[str(x) for x in list(accumulate(sorted(p, reverse=True)))[:2]] for p in ((F(1,2),F(1,2),F(0)),(F(1,8),F(1,8),F(3,4)))])'`.
- **Open in this module:** the sharp restrictions under which independence
  survives, including dimension two and Fourier-linked measurements.
  The source's Corollary IV.4 is about Maassen–Uffink equality states,
  a narrower statement; this refutation does not refute it.
- **Open in this module:** a classification of all order pairs for this
  matrix, or of all matrices whose optimal-state sets are order-independent.
  The source's proposed reduction of arbitrary-order optimization to one
  common optimal-state set cannot follow from Conjecture V.8.
  Its separate theorems on pure states, real states for real overlaps,
  and extremality, and its Fourier-specific conjectures, are not refuted
  by this result.

## ASSUMED-UNVERIFIED

The journal full text was not read; fidelity of its conjecture to the arXiv
v1 source is unverified. Literature priority beyond the stated search scope,
including the other citing works, is unverified. The Lean kernel checks the
encoded mathematics, not the external source's authorship or publication
history. Distinct model families among the producing and reviewing carriers
are not established.
