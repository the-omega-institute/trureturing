---
bibkey: mathlib2026operatorlog
authors: Mathlib contributors
year: 2026
title: Operator logarithms through the continuous functional calculus
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog
claim: Real CFC logarithms are continuous on self-adjoint invertible operators and operator monotone on strictly positive operators.
strata_touched:
  - D5/S3/Quantum/Analysis/TraceClass/LogRegularization
license: Apache-2.0
triage: anchor
---

# Operator logarithms and trace regularization

## Verified locator

https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog

## Suppliers

The pinned Mathlib revision is `db584cd6d46c92f209a44c0f1c829460d327499d`.
The primary source declarations are
[`CFC.log_le_log`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean#L96)
and
[`CFC.continuousOn_log`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean#L179).
The former uses Loewner order without requiring the two arguments to commute.
The latter is restricted to the self-adjoint invertible locus.

For a positive contraction T and epsilon greater than zero, T + epsilon I is
strictly positive. Thus log(1 + epsilon) I minus log(T + epsilon I) is a
bounded positive operator, continuous in T's operator norm. The trace-class
Banach inclusion is continuous from trace norm to operator norm, and the
actual observable trace pairing is continuous. Together these give continuity
of every regularized trace energy in the trace norm of T. Positive trace
pairing transfers the noncommutative order inequality to these energies.

The supremum over epsilon_n = 1/(n+1), after applying ENNReal.ofReal, is lower
semicontinuous. This auxiliary operator-defined supremum does not by itself
supply a spectral representation, its singular kernel interpretation, scaling,
or an entropy identity. No novelty is claimed for operator logarithm
monotonicity, spectral entropy, or the adopted analytic trace-class suppliers.


## Eigenvectors, parameter order and scaling

`ContinuousMap.induction_on_of_compact` in
`Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean` supplies density induction
for continuous real functions on the compact spectrum. The closed equality
locus for action on an actual eigenvector contains constants, the coordinate
function, sums and products. This proves the operator CFC action formula
without a full eigenbasis. A nonzero eigenvector supplies actual spectrum
membership through the bounded-operator and linear-endomorphism spectra;
the zero vector is handled separately.

For spectral x in [0,1] and 0<a<=b, cross multiplication gives
(1+b)/(x+b)<=(1+a)/(x+a). Scalar logarithm monotonicity and `cfc_le_iff`
therefore compare the actual B_b(T) and B_a(T). The increasing inverse-natural
grid permits `ENNReal.iSup_add_iSup_of_monotone` to lift finite nonnegative
trace linearity to the auxiliary supremum, including zero weights and
infinite values. This assertion does not imply a countable decomposition.

For 0<w<=1, the actual shifted operator T+(epsilon/w)I is strictly positive.
The supplied `CFC.log_smul'` applies there and yields
B_epsilon(wT)=B_(epsilon/w)(T)+log((1+epsilon)/(w+epsilon))I.
The positive grid w/(n+1) is cofinal at zero, and its scalar correction
increases to -log w. The same auxiliary supremum consequently scales by
adding Re Tr(rho) times -log w in ENNReal. No unshifted singular logarithm
or inverse is used in this derivation.

These are formal compositions of attributed standard CFC, Stone-Weierstrass,
trace pairing and monotone-supremum suppliers, with no claim of mathematical
priority for a spectral theorem or an entropy-continuity conjecture.
