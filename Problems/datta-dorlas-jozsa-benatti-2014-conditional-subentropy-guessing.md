---
slug: datta-dorlas-jozsa-benatti-2014-conditional-subentropy-guessing
bibkey: datta2014subentropy
doi: 10.1063/1.4882935
url: https://arxiv.org/abs/1310.1312
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Subentropy/Basic.subentropy
---

# Datta–Dorlas–Jozsa–Benatti: conditional subentropy and guessing

## Problem

> Conjecture 2. For a c-q state ρXB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ Hmin(X|B) = − ln pguess(X|B).

The supplied locator is arXiv:1310.1312v1, §2.5.1, Conjecture 2.
Let p be any finite probability distribution and rho_x any finite-dimensional
density states. Conditional subentropy is
Q(recordState p rho) minus Q(mixtureState p rho), using the canonical states.
The strengthened target is

$$
Q(X|B)\le1-p_{\rm guess}(X|B)\le-\log p_{\rm guess}(X|B).
$$

## Motivation

The target is preregistered in [issue #18957](https://github.com/the-omega-institute/trureturing/issues/18957).
It concerns arbitrary finite ensembles, including zero probabilities,
singular states and mixed conditional states.

## Gap

The key estimate holds against every labelled POVM:

$$
Q(\rho_{XB})-Q(\rho_B)
\le1-\sum_xp_x\operatorname{Re}\operatorname{Tr}(M_x\rho_x).
$$

The proof uses convexity of the actual canonical subentropy pinching gap,
not an assumed abstract coherence functional. The measurement outcome label
is retained through its positive Gram piece and pure-state decomposition.

## Route

The success-probability set consists of exactly

$$
\left\{\sum_xp_x\operatorname{Re}\operatorname{Tr}(M_x\rho_x):
M_x\succeq0,\ \sum_xM_x=I\right\},
$$

and p_guess is its real supremum. A deterministic guess at a
positive-probability label proves the set nonempty and p_guess>0.
Positivity and normalization of the POVM give success probabilities in
[0,1], so the set is bounded above and p_guess<=1.

Let Y_x=p_x rho_x and V(w)=sum_x sqrt(Y_x) w_x. The two Gram identities
VV*=rho_B and Delta(V*V)=rho_XB give Q(X|B)=C_Delta(V*V).
For each POVM form G_x=V* M_x V. These positive matrices sum to V*V.
Diagonalize each G_x separately as sum_j w_(x,j) |v_(x,j)><v_(x,j)|,
with normalized vectors and nonnegative weights of total sum one.
Zero eigenvalues stay as zero weights; no division by them is needed.

For each pure vector v, rectangular Gram invariance gives
C_Delta(|v><v|)=Q_cl(r), where r_y=sum_b |v(y,b)|^2.
The stage-1 kernel bound integrates to Q_cl(r)<=1-r_x for every label x.
Convexity of C_Delta therefore gives

$$
Q(X|B)\le\sum_{x,j}w_{x,j}(1-r_x^{(x,j)})
 =1-\sum_xp_x\operatorname{Re}\operatorname{Tr}(M_x\rho_x).
$$

The last equality follows from
Tr(P_x G_x)=Tr(M_x Y_x), with the same original outcome label x.
The least-upper-bound property now gives Q(X|B)<=1-p_guess;
no maximizing measurement is assumed to exist. Finally
log p_guess<=p_guess-1 proves the logarithmic bound.

## Falsifier

A valid finite ensemble violating the target would refute the conjecture.
A mismatch in the POVM set, omitted measurement labels or an unproved
pinching-gap inequality would invalidate this proof route. An estimate for
only pure or orthogonal conditional states would not settle the assertion.

## Evidence

The settlement theorem is
[`POVMGram.cq_conditional_subentropy_guessing`](../D5/S3/Quantum/Subentropy/POVMGram.lean).
Its conditionalSubentropy is exactly the subentropy of the repository's
recordState minus that of mixtureState.
[GuessingProbability](../D5/S3/Quantum/Subentropy/GuessingProbability.lean)
defines the genuine finite-POVM success set and its supremum, and proves
nonemptiness, boundedness, positivity and the supremum conversion.
[ClassicalQuantumGram](../D5/S3/Quantum/Subentropy/ClassicalQuantumGram.lean)
provides the canonical Gram equality and the pure label-specific bound.
[PinchingGap](../D5/S3/Quantum/Subentropy/PinchingGap.lean)
proves the actual convex pinching-gap inequality.

The frozen StrongSubadditivityRefutation.subentropyLike_eq identification
states that every SubentropyLike family equals the canonical subentropy
on every density state. Substitution at recordState and mixtureState
transfers this conditional inequality to every such family, including
repeated and zero spectra.

## Triage

**Proved statement:** for every finite ensemble,
Q(X|B)<=1-p_guess<=-log p_guess. The stronger first bound implies the stated
Conjecture 2. Zero probabilities, mixed or singular conditional states and
degenerate spectra are included.

## ASSUMED-UNVERIFIED

The quotation, arXiv version and locator are supplied source information,
unverified against the original paper under the offline constraint.
Bibliographic metadata has the boundaries stated in
[datta2014subentropy](../Library/Entropy/datta2014subentropy.md). No claim of
present-day literature-wide openness or originality follows from the supplied
conjecture label.
