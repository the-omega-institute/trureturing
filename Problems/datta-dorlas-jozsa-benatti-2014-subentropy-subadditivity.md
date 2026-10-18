---
slug: datta-dorlas-jozsa-benatti-2014-subentropy-subadditivity
bibkey: datta2014subentropy
doi: 10.1063/1.4882935
url: https://arxiv.org/abs/1310.1312
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Subentropy/Basic.subentropy
---

# Datta–Dorlas–Jozsa–Benatti: subadditivity of subentropy

## Problem

> Conjecture 1. Subentropy is subadditive: Q(ρAB) ≤ Q(ρA) + Q(ρB).

The supplied locator is arXiv:1310.1312v1, §2.3.1, Conjecture 1.
The related restatement in arXiv:1510.08859v2, §7.1 is:

> At present, we do not know wether the subadditivity inequality of subentropy is true or not

The assertion concerns every finite-dimensional bipartite density state, with
no commutation, rank or separability restriction. In the canonical partial-trace
interface, `marginalRight` retains A and `marginalLeft` retains B.

## Motivation

The target is preregistered in [issue #18957](https://github.com/the-omega-institute/trureturing/issues/18957).
The spectral formula and its unique continuous extension are represented by
the stage-1 `SubentropyLike` family; the determinant-integral `subentropy`
is its canonical member.

## Gap

The analytic bridge relates the determinant integral to a Gaussian expectation:

$$
Q(A)=\mathbb E_\gamma\eta(a_A(z))-\kappa_\iota,
\qquad a_A(z)=\tfrac12\operatorname{Re}\langle z,Az\rangle,
\qquad \eta(u)=-u\log u.
$$

The real and imaginary coordinates are independent standard real Gaussians.
The baseline is a fixed coordinate's expected entropy in the same index
space. Its cancellation only uses matrices of the same dimension;
rectangular Gram invariance handles changes of dimension. The representation
includes integrability and positive semidefinite trace-one matrices with
zero or repeated eigenvalues.

## Route

For nonnegative finite vectors the entropy Jensen gap

$$
J(a)=\eta(\operatorname{av}a)-\operatorname{av}\eta(a)
$$

is nonnegative, homogeneous and jointly convex, including zero coordinates.
Normalize by the means to prove convexity; a zero mean forces the associated
nonnegative vector to vanish. The Gaussian identity gives concavity of Q.
Averaging conjugations by all block-sign unitaries gives the exact pinching
map. Consequently

$$
C_\Delta(G)=Q(\Delta G)-Q(G)
 =\int J\bigl((a_{U_sGU_s^*}(z))_s\bigr)\,d\gamma(z)
$$

is nonnegative and convex. Rectangular Gram invariance identifies its value
on a pure vector v with Q_cl of the squared block norms r_x.
For a spectral decomposition G=sum_j w_j |v_j><v_j|, convexity followed by
concavity of Q_cl gives

$$
C_\Delta(G)\le\sum_jw_jQ_{\rm cl}(r^{(j)})
 \le Q_{\rm cl}\!\left(\sum_jw_jr^{(j)}\right).
$$

For arbitrary positive blocks Y_x with total trace one, set
V(w)=sum_x sqrt(Y_x) w_x. Then VV*=sum_x Y_x and
Delta(V*V)=directSum_x Y_x. Thus

$$
Q(\mathop{\rm directSum}_xY_x)
 \le Q\!\left(\sum_xY_x\right)+Q_{\rm cl}((\operatorname{Tr}Y_x)_x).
$$

No block normalization or division by a zero block trace is used.
Conjugate a joint density rho_AB by an eigenbasis of rho_A on the A factor.
Its diagonal B-blocks Y_x sum to rho_B and have traces equal to the
eigenvalues of rho_A. Pinching nonnegativity and the block bound yield

$$
Q(\rho_{AB})\le Q(\Delta\rho_{AB})
 \le Q(\rho_B)+Q_{\rm cl}(\operatorname{spec}\rho_A)
 =Q(\rho_B)+Q(\rho_A).
$$

## Falsifier

A density state violating the displayed subadditivity inequality would refute
the universal conjecture. Failure of the Gaussian representation or of a
required pinching estimate would invalidate this proposed proof route without
settling the conjecture.

## Evidence

The settlement theorem is
[`Subadditivity.subentropy_subadditive`](../D5/S3/Quantum/Subentropy/Subadditivity.lean).
Its quantifiers cover arbitrary finite coordinate types and every joint
DensityState, with the actual marginalRight and marginalLeft states.
[EigenbasisBlocks](../D5/S3/Quantum/Subentropy/EigenbasisBlocks.lean)
provides the local conjugation and block identities.
[PinchingGap](../D5/S3/Quantum/Subentropy/PinchingGap.lean)
proves concavity and the nonnegative convex pinching gap, using
[GaussianMatrix](../D5/S3/Quantum/Subentropy/GaussianMatrix.lean) and
[EntropyJensenGap](../D5/S3/Quantum/Subentropy/EntropyJensenGap.lean).
The pure-block identity is in
[ClassicalQuantumGram](../D5/S3/Quantum/Subentropy/ClassicalQuantumGram.lean).

The canonical subentropy is faithful to the paper's continuous-extension
convention: the frozen StrongSubadditivityRefutation.subentropyLike_eq
identification proves that every SubentropyLike family equals this canonical
value on all density states. Applying that equality to the joint state and
both marginals transfers the theorem to every such family.

## Triage

**Proved statement:** subentropy is subadditive on every finite bipartite
density state, without commutation, rank, purity or separability restrictions.
This result is separate from the failure of strong subadditivity.

## ASSUMED-UNVERIFIED

The quotations, spelling, arXiv versions and locators are supplied source
information. They have not been checked against original papers under the
offline constraint. They imply no present-day literature-wide openness or
priority claim. Bibliographic metadata has the boundaries stated in
[datta2014subentropy](../Library/Entropy/datta2014subentropy.md) and
[zhang2017subentropy](../Library/Entropy/zhang2017subentropy.md).
