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
