---
bibkey: hiai2025geometricidentification
authors: Fumio Hiai
year: 2025
title: Log-majorizations between quasi-geometric type means for matrices
doi: null
url: https://arxiv.org/abs/2510.04691v3
claim: Equation (2.1) fixes the base-first geometric mean; classical polar normalization and spectral inversion identify its reversed and negative weights.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Classical geometric-mean identification

Equation (2.1) defines
G(t,X,Y) = X^(1/2) (X^(-1/2) Y X^(-1/2))^t X^(1/2).
The introduction explicitly extends this definition to all real weights for
positive definite matrices. The base is X, the first argument. This is the
ordinary Kubo-Ando weighted geometric mean on weights in [0,1], extended by
the same spectral formula outside that interval.

The identities G(t,X,Y)=G(1-t,Y,X) and
G(-t,X,Y)=X inverse(G(t,X,Y)) X are classical consequences of this formula.
The retained derivation makes their noncommutative content explicit rather
than attributing a new inequality or a solution of Problem 5.18 to them.
Set C=X^(-1/2) Y X^(-1/2). The polar-normalized element
U=Y^(-1/2) X^(1/2) C^(1/2) is unitary and transports inverse(C) to
Y^(-1/2) X Y^(-1/2). Unitary equivariance of the continuous functional
calculus proves weighted symmetry. Inverting the square-root congruence
and combining powers of C proves the inverse sandwich.

The formal proof uses Mathlib's public CFC mapping theorem, its unitary
conjugation automorphism, and its square-root sandwich inverse. It does
not transport the functional calculus through an arbitrary congruence.
No proof text is transcribed from the paper. The reference fixes the source
operation and target context; the displayed argument records the classical
derivation, not a theorem quoted verbatim from equation (2.1).

For t=-theta the symmetry gives G(1+theta,Y,X)=G(-theta,X,Y).
This connects the attained inverse-mean variational formula with the exact
positive-weight HS mean-trace concavity. The original SPD joint convexity
assembly and support-preserving common-epsilon PSD extension remain
additional obligations of Problem 5.18.

## Verified locator

https://arxiv.org/abs/2510.04691v3, introduction and equation (2.1).
